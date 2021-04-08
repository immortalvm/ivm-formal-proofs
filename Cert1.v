From iVM Require Import DSet Mono Cert0.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(*****************)

Proposition nCert_monotone n {ma mb: M bool} (Hab: ma ⊑ mb) (Hb: nCert n mb) :
  nCert n ma.
Proof.
  unfold nCert in *. transitivity mb; assumption.
Qed.

Corollary nCertN_monotone n {X} {RX: Rel X}
  (mx mx': M X) (Hmx: mx ⊑ mx') (H: nCertN n mx') : nCertN n mx.
Proof.
  unfold nCertN in *.
  assert (mx;; ret true ⊑ mx';; ret true) as HH.
  - crush. exact Hmx.
  - apply (nCert_monotone n HH H).
Qed.

(****)

Proposition wipe_swallow_precondition' u {n} (ops: vector Z n) :
  wipe u;;
  swallow ops ⊑ let* pc := get' PC in
                assume' (u # nAfter n pc);;
                swallow ops.
Proof.
  rewrite wipe_swallow_precondition.
  transitivity (
    let* pc := get' PC in
    assume' (u # nAfter n pc);;
    ret tt;;
    swallow ops);
  [ | crush ].
  apply bind_propr'; [ apply getPc_propr | ].
  intros p p' Hp. destruct Hp.
  setoid_rewrite <- simplify_assume.
  apply assume_rel.
  intros H.
  apply bind_propr'; [ apply wipe_less | ].
  crush.
Qed.

(*********************)

(* TODO: Is this useful? *)
Definition clearMem (mem: Memory) (a: Addr) (n: nat) : Memory :=
  update (Lens := restrLens (nAfter n a)) mem (fun _ _ _ => None).

Proposition wipe_nAfter a n :
  wipe (nAfter n a) =
    assume' (nAfter n a ⊆ available);;
    let* mem := get' MEM in
    put' MEM (clearMem mem a n).
Proof.
  rewrite wipe_spec.
  repeat rewrite put_spec. cbn.
  repeat rewrite get_spec. cbn.
  smon_rewrite.
Qed.

(***)

Instance restr_relation (u: DSet B64) : Rel (Memory' u) :=
  fun f g => forall a, forall (Hu: a ∈ u),
    forall (Ha: Machine.available' a), f a Hu Ha ⊑ g a Hu Ha.

Instance getMem'_propr u : PropR (get' (MEM' u)).
Proof.
  rewrite get_spec. cbn. crush. unfold rel.
  intros a Hu Ha.
  apply Hst.
Qed.

Instance putMem'_propr u : PropR (put' (MEM' u)).
Proof.
  intros f g Hfg. rewrite put_spec. cbn.
  unfold compose. crush. srel_destruct Hst.
  repeat split; unfold lens_relation; lens_rewrite; try assumption.
  do 2 rewrite proj_update. crush.
  destruct (decide _) as [H|_].
  - apply Hfg.
  - apply Hst_mem.
Qed.

(******************************)

Proposition simplify_put_1 {X} {RX: Rel X} {HT: Transitive RX}
    (mx mx': M X) {Hmx': PropR mx'}
    (s t: State) (Hst: s ⊑ t)
    (H: put s;; mx ⊑ put s;; mx') :
  put s;; mx ⊑ put t;; mx'.
Proof.
  transitivity (put s;; mx').
  - exact H.
  - now crush.
Qed.

Proposition simplify_put_2 {X} {RX: Rel X} {HT: Transitive RX}
    (mx mx': M X) {Hmx: PropR mx}
    (s t: State) (Hst: s ⊑ t)
    (H: put t;; mx ⊑ put t;; mx') :
  put s;; mx ⊑ put t;; mx'.
Proof.
  transitivity (put t;; mx).
  - now crush.
  - exact H.
Qed.

(** Cf. smonad_ext and rel_extensional'.
In general, one of the variations below is more convenient. *)

Proposition rel_extensional
    {X} (mx mx': M X) {RX: Rel X}
    (H: forall (s t: State) (Hst: s ⊑ t),
      put s;; mx ⊑ put t;; mx') :
  mx ⊑ mx'.
Proof.
  assert (
    let* s := get in
    put s;;
    mx ⊑
      let* t := get in
      put t;;
      mx') as HH.
  - apply bind_propr'.
    + crush.
    + exact H.
  - revert HH.
    now smon_rewrite.
Qed.

Corollary rel_extensional_1
    {X} {RX: Rel X} {HT: Transitive RX}
    (mx mx': M X) (Hmx: PropR mx)
    (H: forall s, put s;; mx ⊑ put s;; mx') :
  mx ⊑ mx'.
Proof.
  apply rel_extensional. intros.
  now apply simplify_put_2.
Qed.

Ltac rel_extensional_1 :=
  match goal with |- ?mx ⊑ ?mx' => apply (rel_extensional_1 mx mx') end.

Corollary rel_extensional_2
    {X} {RX: Rel X} {HT: Transitive RX}
    (mx mx': M X) (Hmx: PropR mx')
    (H: forall s, put s;; mx ⊑ put s;; mx') :
  mx ⊑ mx'.
Proof.
  apply rel_extensional. intros.
  now apply simplify_put_1.
Qed.

Ltac rel_extensional_2 :=
  match goal with |- ?mx ⊑ ?mx' => apply (rel_extensional_2 mx mx') end.

(***)

(* Lens argument no longer implicit. *)
Arguments proj {_ _} _.
Arguments update {_ _} _.

Proposition assume_below_tt P {DP: Decidable P} :
  assume' P ⊑ ret tt.
Proof.
  crush.
Qed.

(****************)

Definition assumeState
    (P: State -> Prop)
    {DP: forall s, Decidable (P s)} :=
  let* s := get in
  assume' (P s).

Proposition assumeState_sub_tt
    (P: State -> Prop)
    {DP: forall s, Decidable (P s)} :
  assumeState P ⊑ ret tt.
Proof.
  unfold assumeState.
  apply rel_extensional_2; [ crush | ]. intros s.
  rewrite put_get'.
  destruct (decide (P s)); crush.
Qed.

(***)

Definition wiped u :=
  let* mem := get' MEM in
  assume' (isWiped u mem).

Definition wipeStack n :=
  let* a := get' SP in
  wipe (nBefore (n * 8) a).

(*********)

Definition longsToBytes {n} (u: vector B64 n) : Bytes (n * 8).
Proof.
  induction n.
  - exact [].
  - dependent elimination u as [ @Vector.cons x n u ].
    exact (bitsToBytes (x : Bits (8 * 8)) ++ IHn u).
Defined.

Proposition longsToBytes_equation_1 : longsToBytes [] = [].
Proof. reflexivity. Qed.

Proposition longsToBytes_equation_2 n x (u: vector B64 n) :
  @longsToBytes (S n) (x :: u) = bitsToBytes (x : Bits (8 * 8)) ++ longsToBytes u.
Proof. reflexivity. Qed.

Hint Rewrite longsToBytes_equation_1 @longsToBytes_equation_2 : longsToBytes.
#[global] Opaque longsToBytes.

Proposition longsToBytes_bytesToLongs n (u: Bytes (n * 8)) :
  longsToBytes (bytesToLongs u) = u.
Proof. (* TODO: Simplify proof *)
  induction n.
  - now dependent elimination u.
  - dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u].
    simp bytesToLongs.
    simp longsToBytes.
    rewrite IHn. clear IHn.
    dependent elimination b0 as
      [b00 :: b01 :: b02 :: b03 :: b04 :: b05 :: b06 :: b07 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b1 as
      [b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b2 as
      [b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b3 as
      [b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b4 as
      [b40 :: b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b5 as
      [b50 :: b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b6 as
      [b60 :: b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: [] ].
    cbn. simp bitsToBytes.
    dependent elimination b7 as
      [b70 :: b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: [] ].
    cbn. simp bitsToBytes.
    reflexivity.
Qed.

(***********)

Proposition postpone_assume'' P {DP: Decidable P} (mx: M unit) :
  assume' P;; mx = mx;; assume' P.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

Proposition pop_getSP {X} (f: B8 -> B64 -> M X):
  let* x := pop in
  let* sp := get' SP in
  f x sp =
    let* sp := get' SP in
    let* x := pop in
    f x (offset 1 sp).
Proof.
  rewrite pop_spec.
  apply (smonad_ext' SP). intros sp.
  smon_rewrite.
  setoid_rewrite <- confined_load.
  now rewrite lens_put_get.
Qed.

Definition defined a :=
  let* Ha := assume (available a) in
  let* mem := get' MEM in
  assume' (mem a Ha).

Proposition defined_not_available a (Ha: ~ available a) :
  defined a = err.
Proof.
  unfold defined.
  destruct (decide (available a)) as [H|H].
  - now contradict Ha.
  - smon_rewrite.
Qed.

Definition defined_spec := unfolded_eq (defined).

Proposition defined_spec'' a :
  defined a =
    let* Ha := assume (available a) in
    let* x := get' (MEM'' a) in
    assume' (x Ha).
Proof.
  unfold defined.
  destruct (decide (available a)) as [H|H].
  - repeat rewrite get_spec. smon_rewrite.
  - now smon_rewrite01.
Qed.

#[global] Opaque defined.

Proposition load_defined a :
  load a = defined a;; load a.
Proof.
  rewrite load_spec, defined_spec, extr_spec.
  change (Machine.available' a) with (available a).
  destruct (decide (available a)) as [Ha|Ha]; [ | smon_rewrite ].
  apply (smonad_ext' MEM). intros mem.
  smon_rewrite.
  setoid_rewrite <- confined_put.
  - setoid_rewrite lens_put_get.
    destruct (mem a Ha) as [x|].
    + cbn. smon_rewrite.
    + smon_rewrite.
  - typeclasses eauto.
Qed.

Proposition load_store a :
  let* x := load a in store a x = defined a.
Proof.
  apply (smonad_ext' MEM). intros mem.
  rewrite load_defined, load_spec, defined_spec, extr_spec.
  setoid_rewrite store_spec.
  change (Machine.available' a) with (available a).
  destruct (decide (available a)) as [H|H].
  - smon_rewrite.
    rewrite postpone_assume'.
    rewrite lens_put_get.
    destruct (mem a H) as [x|] eqn:He.
    + cbn. smon_rewrite. f_equal.
      extensionality b.
      extensionality Hb.
      destruct (decide (a = b)) as [HH|HH].
      * destruct HH. rewrite <- He. f_equal. apply is_true_unique.
      * reflexivity.
    + cbn. smon_rewrite.
  - smon_rewrite.
Qed.

Proposition pop_push :
  let* x := pop in
  push x =
    let* sp := get' SP in
    defined sp.
Proof.
  rewrite pop_spec, push_spec.
  repeat setoid_rewrite bind_assoc.
  apply (smonad_ext' SP). intros sp.
  setoid_rewrite lens_put_get.
  setoid_rewrite lens_put_put.
  setoid_rewrite confined_load.
  setoid_rewrite lens_put_get.
  setoid_rewrite lens_put_put.
  setoid_rewrite <- confined_load.
  rewrite <- Z_action_add.
  cbn. rewrite Z_action_zero.
  now rewrite load_store.
Qed.

(***)

Definition pushN {n} (u: vector B64 n) := pushMany (longsToBytes u).

Definition pushN_spec := unfolded_eq (@pushN).

#[global] Opaque pushN.


Definition popMany' n :=
  let* u := popMany n in
  ret (to_list u).

Proposition popMany_ext m n (Hmn: m = n) :
  popMany' m = popMany' n.
Proof.
  now subst.
Qed.

Proposition popMany_to_popMany' n {X} (f: list Cell -> M X) :
  let* u := popMany n in f u =
  let* u := popMany' n in f u.
Proof.
  smon_rewrite.
Qed.

Proposition popMany_S n X (f: list Cell -> M X) :
  let* u := popMany (S n) in
  f u =
    let* u := popMany n in
    let* x := pop in
    f (u ++ [x]).
Proof.
  transitivity (
    let* w := (
      let* u := popMany n in
      let* v := popMany 1%nat in
      ret (u ++ v)%vector ) in
    f w
  ).
  - setoid_rewrite <- popMany_action.
    setoid_rewrite popMany_to_popMany'.
    apply bind_extensional'.
    + apply popMany_ext. lia.
    + reflexivity.
  - simp popMany. now smon_rewrite01.
Qed.

Proposition popMany_getSP n {X} (f: Cells n -> B64 -> M X) :
  let* u := popMany n in
  let* sp := get' SP in
  f u sp =
    let* sp := get' SP in
    let* u := popMany n in
    f u (offset n sp).
Proof.
  setoid_rewrite popMany_spec.
  smon_rewrite01.
  setoid_rewrite lens_get_get.
  apply bind_extensional.
  intros a.
  setoid_rewrite (confined_get SP).
  - now setoid_rewrite lens_put_get.
  - (* TODO: Simplify *)
    apply (confined_neutral (m' := MEM)).
    typeclasses eauto.
Qed.

Instance confined_defined a : Confined (MEM'' a) (defined a).
Proof.
  rewrite defined_spec''.
  typeclasses eauto.
Qed.

#[global] Instance semiNeutral_defined m a : SemiNeutral m (defined a).
Proof.
  rewrite defined_spec.
  unfold SemiNeutral.
  rewrite putM_spec, get_spec.
  destruct (decide (available a)) as [Ha|Ha].
  - smon_ext s. cbn. smon_rewrite.
    destruct (decide (proj MEM s a Ha)) as [H|H];
    smon_rewrite.
  - now smon_rewrite01.
Qed.

Definition sDefined u :=
  let* mem := get' MEM in
  assume' (forall a (Hu: a ∈ u), exists (Ha: available a), mem a Ha).

Definition sDefined_spec := unfolded_eq (sDefined).

#[global] Opaque sDefined.

Proposition sDefined_empty : sDefined ∅ = ret tt.
Proof.
  rewrite sDefined_spec.
  smon_ext' MEM mem.
  rewrite lens_put_get.
  destruct (decide _) as [H|H]; [ reflexivity | ].
  contradict H.
  intros a Ha.
  contradict Ha.
Qed.

Proposition sDefined_singleton a : sDefined !{a} = defined a.
Proof.
  smon_ext' MEM mem.
  rewrite sDefined_spec.
  rewrite defined_spec.
  destruct (decide (available a)) as [Ha|Ha].
  - smon_rewrite.
    destruct (decide (mem a Ha)) as [H|H];
    destruct (decide _) as [H'|H'].
    1, 4: reflexivity.
    + contradict H'.
      intros a' Ha'.
      apply singleton_spec in Ha'.
      subst a'.
      firstorder.
    + contradict H.
      specialize (H' a).
      setoid_rewrite singleton_spec in H'.
      specialize (H' eq_refl).
      destruct H' as [Ha' Hm].
      now destruct (is_true_unique Ha Ha').
  - smon_rewrite01.
    setoid_rewrite lens_put_get.
    destruct (decide _) as [H|H].
    + contradict Ha.
      apply H.
      now apply singleton_spec.
    + now smon_rewrite01.
Qed.

Proposition sDefined_union u v :
  sDefined (u ∪ v) =
    sDefined u;;
    sDefined v.
Proof.
  smon_ext' MEM mem.
  rewrite sDefined_spec.
  setoid_rewrite bind_assoc.
  setoid_rewrite lens_put_get.
  destruct (decide _) as [H|H];
  destruct (decide _) as [Hu|Hu].
  - smon_rewrite.
    destruct (decide _) as [Hv|Hv].
    + now smon_rewrite2.
    + contradict Hv.
      intros a Ha.
      apply H.
      apply union_spec.
      now right.
  - contradict Hu.
    intros a Ha.
    apply H.
    apply union_spec.
    now left.
  - smon_rewrite.
    destruct (decide _) as [Hv|Hv].
    + contradict H.
      intros a Ha.
      apply union_spec in Ha.
      destruct Ha as [Ha|Ha].
      * now apply Hu.
      * now apply Hv.
    + smon_rewrite.
  - smon_rewrite.
Qed.

Proposition addressable_64 n a : addressable n a <-> n <= 2^64.
Proof.
  unfold addressable.
  setoid_rewrite <- (fromBits_toBits' _ a) at 2.
  split; intros H.
  - by_lia (n <= 2^64 \/ 2^64 < n) as Hor.
    destruct Hor as [Hle|Hg]; [exact Hle | exfalso].
    apply (H (2^64)); [ lia | ].
    apply toBits_cong.
    transitivity (0 + a).
    + apply cong_add_proper.
      lia_rewrite (2^64 = 1 * 2^64).
      apply cong_zero.
      now apply eq_cong.
    + apply eq_cong. lia.
  - intros i [H0 Hn] He.
    apply toBits_cong in He.
    apply cong_eq in He.
    by_lia (i + a - a = i) as HH. rewrite HH in He. clear HH.
    unfold cong, irel in He.
    apply Z_div_exact_full_2 in He; [ | lia ].
    lia.
Qed.

Instance confined_assume' P {DP: Decidable P} : Confined (@fstMixer State) (assume' P).
Proof.
  typeclasses eauto.
Qed.

Lemma pop_defined :
  pop =
    let* sp := get' SP in
    defined sp;;
    pop.
Proof.
  rewrite defined_spec.
  setoid_rewrite pop_spec.
  setoid_rewrite load_spec.
  smon_ext' SP sp.
  setoid_rewrite lens_put_get.
  setoid_rewrite lens_put_put.

  setoid_rewrite (confined_get SP); [ | typeclasses eauto .. ].
  setoid_rewrite lens_put_get.
  setoid_rewrite (confined_put SP _); [ | typeclasses eauto .. ].
  setoid_rewrite lens_put_put.

  repeat setoid_rewrite bind_assoc.
  repeat setoid_rewrite (confined_get MEM); [ | typeclasses eauto .. ].

  smon_ext' MEM mem.
  setoid_rewrite lens_put_get.

  setoid_rewrite postpone_assume'.
  setoid_rewrite (confined_get MEM); [ | typeclasses eauto .. ].
  setoid_rewrite (confined_get MEM); [ | typeclasses eauto .. ].
  setoid_rewrite lens_put_get.

  change Machine.available' with available.

  destruct (decide (available sp)) as [Hsp|Hsp].
  - repeat setoid_rewrite ret_bind.
    destruct (mem sp Hsp) as [x|].
    + now setoid_rewrite ret_bind.
    + rewrite extr_spec. now smon_rewrite01.

  - now smon_rewrite01.
Qed.

Proposition pop_get_SP {X} (f: Cell -> B64 -> M X) :
  let* x := pop in
  let* sp := get' SP in
  f x sp =
    let* sp := get' SP in
    let* x := pop in
    f x (offset 1 sp).
Proof.
  rewrite pop_spec.
  smon_rewrite01.
  setoid_rewrite confined_load.
  setoid_rewrite lens_put_get.
  setoid_rewrite lens_get_get.
  reflexivity.
Qed.

Instance semiNeutral_load a : SemiNeutral MEM (load a).
Proof.
  unfold SemiNeutral.
  rewrite load_spec.
  change Machine.available' with available.
  destruct (decide (available a)) as [Ha|Ha]; [ | now smon_rewrite01 ].
  setoid_rewrite ret_bind.
  rewrite get_spec.
  rewrite putM_spec.
  rewrite extr_spec.
  smon_rewrite.
  smon_ext s.
  setoid_rewrite put_get'.
  destruct (proj MEM s a Ha) as [x|]; [ | now smon_rewrite01 ].
  smon_rewrite.
Qed.

Instance semiNeutral_pop : SemiNeutral MEM pop.
Proof.
  unfold SemiNeutral.
  rewrite pop_spec.
  rewrite get_spec.
  rewrite put_spec.
  setoid_rewrite semiNeutral_load.
  setoid_rewrite putM_specL.
  smon_rewrite.
Qed.

Proposition sDefined_member a u (Hau: a ∈ u) :
  sDefined u = defined a;; sDefined u.
Proof.
  rewrite sDefined_spec.
  smon_ext' MEM mem.
  setoid_rewrite (semiNeutral_get_put MEM (defined a)).
  repeat setoid_rewrite lens_put_get.
  rewrite defined_spec.
  destruct (decide (available a)) as [Ha|Ha].
  - smon_rewrite01.
    repeat setoid_rewrite lens_put_get.
    destruct (decide (mem a Ha)) as [Hm|Hm].
    + smon_rewrite.
    + smon_rewrite01.
      destruct (decide _) as [H|H].
      * contradict Hm.
        specialize (H a Hau).
        destruct H as [Ha' Hm].
        destruct (is_true_unique Ha Ha').
        exact Hm.
      * smon_rewrite.
  - smon_rewrite01.
    destruct (decide _) as [H|H].
    + contradict Ha.
      specialize (H a Hau).
      destruct H as [Ha Hm].
      exact Ha.
    + now smon_rewrite01.
Qed.

Lemma popMany_defined n :
  popMany n =
    let* sp := get' SP in
    sDefined (nAfter n sp);;
    popMany n.
Proof. (* TODO: Simplify *)
  induction n.
  - simp popMany.
    setoid_rewrite nAfter_empty.
    setoid_rewrite sDefined_empty.
    smon_rewrite.

  - simp popMany.
    setoid_rewrite IHn at 1.
    setoid_rewrite pop_defined at 1.
    repeat setoid_rewrite bind_assoc.

    smon_ext' SP sp.
    setoid_rewrite lens_put_get.
    setoid_rewrite pop_get_SP.
    setoid_rewrite (confined_get SP).
    setoid_rewrite lens_put_get.

    rewrite defined_spec.
    destruct (decide (available sp)) as [Hsp|Hsp].
    + smon_rewrite01.
      setoid_rewrite (confined_get MEM); [ | typeclasses eauto ].
      smon_ext' MEM mem.
      setoid_rewrite lens_put_get.

      destruct (decide (mem sp Hsp)) as [Hm|Hm].
      * setoid_rewrite ret_tt_bind.
        rewrite sDefined_spec.
        smon_rewrite01.
        setoid_rewrite (confined_get MEM) at 2; [ | typeclasses eauto ].
        setoid_rewrite lens_put_get.
        setoid_rewrite (semiNeutral_get_put MEM pop) at 1.

        setoid_rewrite (confined_get MEM); [ | typeclasses eauto ].
        repeat setoid_rewrite lens_put_get.
        setoid_rewrite <- (confined_put MEM mem); [ | typeclasses eauto .. ].
        setoid_rewrite <- semiNeutral_put_put; [ | typeclasses eauto .. ].
        destruct (decide _) as [H1|H1];
        destruct (decide _) as [H2|H2].
        1,4: smon_rewrite.
        -- contradict H2.
          intros a Ha.
          rewrite nAfter_spec in Ha.
          destruct Ha as [i [Hi Hi']].
          by_lia (i = 0 \/ (i - 1) + 1 = i)%nat as Hii.
          destruct Hii as [Hii|Hii].
          ++ rewrite Hii in Hi'.
            rewrite Z_action_zero in Hi'.
            destruct Hi'. exists Hsp. exact Hm.
          ++ apply H1. rewrite nAfter_spec.
            exists (i - 1)%nat.
            split.
            ** lia.
            ** rewrite <- Hi'.
              rewrite <- Z_action_add.
              f_equal.
              lia.
          -- contradict H1.
            intros a Ha.
            apply H2.
            apply nAfter_tail.
            exact Ha.
      * smon_rewrite01.
        setoid_rewrite (sDefined_member sp); [ | apply nAfter_head ].
        setoid_rewrite bind_assoc.
        setoid_rewrite <- (confined_put SP);
          rewrite defined_spec;
          [ | typeclasses eauto ].
        decided Hsp.
        smon_rewrite.
        undecided Hm.
        now smon_rewrite01.

    + smon_rewrite01.
      setoid_rewrite (sDefined_member sp); [ | apply nAfter_head ].
      setoid_rewrite bind_assoc.
      setoid_rewrite <- (confined_put SP);
        rewrite defined_spec;
        [ | typeclasses eauto ].
      undecided Hsp.
      now smon_rewrite01.

    + rewrite defined_spec.
      typeclasses eauto.
Qed.
