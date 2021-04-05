From iVM Require Import DSet Mono Cert0.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(*****************)

#[global] Opaque pushMany. (* TODO *)

(* TODO: Move *)
Instance swallow_propr {n} (ops: vector Z n) : PropR (swallow ops).
Proof.
  rewrite swallow_spec.
  crush.
Qed.

(*************)

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
  setoid_rewrite simplify_assume.
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

Definition clearMem (mem: Memory) (a: Addr) (n: nat) : Memory :=
  update (Lens := restrLens (nAfter n a)) mem (fun _ _ _ => None).

Proposition wipe_nAfter a n :
  wipe (nAfter n a) =
    let* mem := get' MEM in
    put' MEM (clearMem mem a n).
Proof.
  unfold wipe.
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

(********)

(* TODO: Move *)
Proposition bitsToN_bound {n} (u: Bits n) : (bitsToN u < 2 ^ n)%N.
Proof.
  assert ((2^n)%N = 2^n :> Z) as H; [ now rewrite N2Z.inj_pow | ].
  unfold bitsToN, fromBits.
  apply N2Z.inj_lt.
  rewrite N2Z.inj_pow.
  destruct (join_zero u) as [H0 H64].
  lia.
Qed.

(* TODO: Update definition in Init.v instead. *)
Arguments Nat2N_inj_lt {_ _}.

(* TODO: Move to after Nat2N_inj_lt *)
Corollary N2Nat_inj_lt {m n: N} :
  (N.to_nat m < N.to_nat n)%nat <-> (m < n)%N.
Proof.
  setoid_rewrite <- Nnat.N2Nat.id at 3 4.
  setoid_rewrite Nat2N_inj_lt.
  reflexivity.
Qed.

(***)

(* Finitely enumerable, equivalent to Coq.Logic.FinFun.Finite. *)
Class SFinite X : Type :=
{
  SFinite_n : N;
  SFinite_f : forall i, (i < SFinite_n)%N -> X;
  SFinite_p : forall x, exists i Hi, SFinite_f i Hi = x;
}.

#[refine]
Instance bits_sfinite n : SFinite (Bits n) :=
{
  SFinite_n := 2 ^ n;
  SFinite_f i _ := toBits n i;
}.
Proof.
  intros x. exists x, (bitsToN_bound x).
  apply fromBits_toBits'.
Qed.

(****)

Instance sfinite_decidable_all
    {X} {SF: SFinite X}
    (P: X -> Prop) {DP: forall x, Decidable (P x)} :
  Decidable (forall x, P x).
Proof.
  enough (
    (forall x, P x) <->
    (forall i (Hi: (i < SFinite_n)%N),
      P (SFinite_f i Hi))) as H;
  [ unshelve eapply (decidable_transfer H) | ].
  split.
  - intros H i Hi. apply H.
  - intros H x.
    destruct (SFinite_p x) as [i [Hi Hp]].
    specialize (H i Hi).
    rewrite Hp in H.
    exact H.
Qed.

Definition isWiped (u: DSet Addr) (m: Memory) :=
  forall a (Hau: a ∈ u), exists (Ha: available a), m a Ha = None.

(* TODO: Move to Init.v. *)
Instance exists_true_decidable
    (b: bool) (P: Is_true b -> Prop) {DP: forall Hb: b, Decidable (P Hb)} :
    Decidable (exists Hb, P Hb).
Proof.
  destruct b.
  - specialize (DP I).
    destruct (decide (P I)) as [H|H].
    + left. exists I. exact H.
    + right. intros [Hb Hp]. destruct Hb. exact (H Hp).
  - right. intros [Hb _]. exact Hb.
Qed.

(* Redundant *)
Instance isWiped_decidable u m : Decidable (isWiped u m).
Proof.
  typeclasses eauto.
Defined.

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

(* TODO: Replace postpone_assume in Mon.v. *)
Proposition postpone_assume' P {DP: Decidable P} {X} (mx: M X) {Y} (f: X -> M Y) :
  assume' P;;
  let* x := mx in
  f x = let* x := mx in
        assume' P;;
        f x.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

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

(* TODO: Replace definition of wipe instead. *)
Definition wipe' u :=
  assume' (u ⊆ available);;
  wipe u.

Definition wiped u :=
  let* mem := get' MEM in
  assume' (isWiped u mem).

Definition wipeStack n :=
  let* a := get' SP in
  wipe' (nBefore (n * 8) a).

(***)

(* TODO: Postpone *)
Definition stdStart m n {o} (ops: vector Z o) : M (vector B64 n) :=
  let* v := popN n in
  wipeStack (m + n);;
  swallow ops;;
  ret v.

(** By putting [swallow] after [wipeStack] we ensure that [stdStart] fails
    if the operations overlap with (the relevant parts of) the stack. *)

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

Transparent pushMany.

(* TODO: Move to Operations.v. *)
Proposition pushMany_empty : pushMany [] = ret tt.
Proof.
  unfold pushMany.
  reflexivity.
Qed.

Proposition pushMany_one x : pushMany [x] = push x.
Proof.
  cbn. smon_rewrite.
Qed.

Opaque pushMany.

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
  assert (toB64 (-1 + toB64 (1 + sp)) = sp) as Hsp.
  -
    transitivity (offset (-1) (offset 1 sp)).
    + reflexivity.
    + rewrite <- Z_action_add. cbn. apply Z_action_zero.
  - now rewrite Hsp, load_store.
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

(* TODO: move *)
Lemma to_list_action {X m n} (u: vector X m) (v: vector X n) :
  to_list (u ++ v)%vector = ((to_list u) ++ (to_list v))%list.
Proof.
  induction m.
  - now dependent elimination u.
  - dependent elimination u as [Vector.cons(n:=m) x u].
    simp to_list.
    rewrite <- append_comm_cons.
    setoid_rewrite to_list_equation_2. (* ! *)
    rewrite IHm.
    rewrite <- app_comm_cons.
    reflexivity.
Qed.

(* TODO: Move *)
Proposition collapse_bind_lift
            {S M} {SM: SMonad S M}
            {X} {mx: M X} {Y} {f: X -> M Y} {my: M Y}
            (H: mx >>= f = my)
            {Z} (g: Y -> M Z) :
    let* x := mx in
    let* y := f x in
    g y =
      let* y := my in
      g y.
Proof.
  transitivity (
    let* yy := (
      let* x := mx in
      f x) in
    g yy).
  - smon_rewrite.
  - now setoid_rewrite H.
Qed.

Proposition popMany_getSP n {X} (f: Cells n -> B64 -> M X) :
  let* u := popMany n in
  let* sp := get' SP in
  f u sp =
    let* sp := get' SP in
    let* u := popMany n in
    f u (toB64 (n + sp)).
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

(* TODO: Replace weaker version in Operations.v. *)
Instance confined_popMany' sp n :
  Confined (MEM' (nAfter n sp) * SP)
  (put' SP sp;; popMany n).
Proof.
  rewrite popMany_spec.
  smon_rewrite.
  typeclasses eauto.
Qed.

(* TODO: move to Mixer.v. Remove from Extras/Mixer.v. *)
Instance submixer_snd {A} (f: Mixer A) : (f | sndMixer).
Proof. mixer_rewrite'. Qed.

(* TODO: move to Mon.v *)
Section SemiNeutral_section.

  Context {S M} {SM: SMonad S M}.

  Class SemiNeutral {X} (m: Mixer S) (mx: M X) : Prop :=
    neutral : mx =  let* s := get in
                    let* x := mx in
                    putM m s;;
                    ret x.

  #[global] Instance sub_semiNeutral
          {X} {m: Mixer S} {mx: M X}
          (Hmx: SemiNeutral m mx)
          (m': Mixer S) {Hm: (m'|m)} : SemiNeutral m' mx.
  Proof.
    unfold SemiNeutral in *.
    setoid_rewrite Hmx.
    rewrite putM_spec.
    smon_rewrite.
  Qed.

  Context {X A} (LA: Lens S A) (mx: M X)
          {Hmx: SemiNeutral LA mx}
          {Y} (f: X -> M Y).

  Proposition semiNeutral_get_put :
    let* x := mx in
    f x =
      let* u := get' LA in
      let* x := mx in
      put' LA u;;
      f x.
  Proof.
    rewrite Hmx at 1.
    rewrite get_spec, put_spec, putM_spec.
    smon_rewrite.
  Qed.

  Proposition semiNeutral_put_put a :
    put' LA a;;
    let* x := mx in
    f x =
      put' LA a;;
      let* x := mx in
      put' LA a;;
      f x.
  Proof.
    setoid_rewrite semiNeutral_get_put at 1.
    now setoid_rewrite lens_put_get.
  Qed.

End SemiNeutral_section.

#[global] Instance semiNeutral_defined a : SemiNeutral sndMixer (defined a).
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


(* TODO: Repolace original in Init.v. *)
Proposition asBool_decide' P {DP: Decidable P} : Is_true (as_bool (decide P)) <-> P.
Proof.
  destruct (decide P) as [H|H]; now cbn.
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

(* TODO: Move to DSet.v and generalize. *)
Proposition union_symmetric (u v: DSet B64) :
  u ∪ v = v ∪ u.
Proof.
  apply extensionality.
  intros x.
  setoid_rewrite union_spec.
  tauto.
Qed.

(* TODO: Move to after cong_mod. *)
Corollary cong_zero n k : cong n (k * 2^n) 0.
Proof.
  transitivity ((k * 2^n) mod 2^n).
  - symmetry. apply cong_mod. lia.
  - apply eq_cong. apply Z_mod_mult.
Qed.

(* TODO: Move to after cong_proper_add. *)
Corollary cong_eq n x y : cong n x y <-> cong n (x - y) 0.
Proof.
  split; intros H.
  - transitivity (x + (-y)).
    + apply eq_cong. lia.
    + setoid_rewrite H. apply eq_cong. lia.
  - transitivity ((x - y) + y).
    + apply eq_cong. lia.
    + setoid_rewrite H.  apply eq_cong. lia.
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
  smon_rewrite.

  destruct (decide _) as [Hsp|Hsp].
  - smon_rewrite.
    setoid_rewrite (confined_get MEM).

    (* ------------ TODO: Continue from here -----------------*)

    smon_ext' MEM mem.
    smon_rewrite.



    setoid_rewrite <- (confined_put SP sp).
    setoid_rewrite <- (confined_put SP sp).


Lemma popMany_defined n :
  popMany n =
    let* sp := get' SP in
    sDefined (nAfter n sp);;
    popMany n.
Proof.
  induction n.
  - simp popMany.
    setoid_rewrite nAfter_empty.
    setoid_rewrite sDefined_empty.
    smon_rewrite.
  - match goal with |- _ = ?r => set (rh :=r) end.
    simp popMany.
    setoid_rewrite IHn.

    smon_rewrite.




Proposition popMany_pushMany n :
  let* u := popMany n in
  pushMany u =
    let* sp := get' SP in
    sDefined (nAfter n sp).
Proof.
  unfold def, member.
  smon_ext' SP sp.
  setoid_rewrite lens_put_get.
  smon_ext' MEM mem.
  induction n.

  - simp popMany. setoid_rewrite ret_bind. cbn.
    rewrite pushMany_empty.
    do 2 (apply bind_extensional; intros []).
    rewrite <- sDefined_empty. f_equal.
    apply extensionality. intros a. cbn.
    split; [ tauto | ]. unfold member.
    intros H. apply asBool_decide' in H. destruct H. lia.

  - setoid_rewrite popMany_S.
    setoid_rewrite to_list_action.
    setoid_rewrite pushMany_action.
    setoid_rewrite pushMany_one.
    setoid_rewrite (collapse_bind_lift pop_push).

    smon_rewrite01.
    setoid_rewrite (popMany_getSP n).
    setoid_rewrite lens_put_get.

    transitivity (
      put' MEM mem;;
      let* u := (put' SP sp;; popMany n) in
      defined (toB64 (n + sp));;
      pushMany u);
    [ now smon_rewrite01 | ].

    setoid_rewrite <- (confined_popMany' sp n _).
    + rewrite (semiNeutral_put_put MEM (defined _)).
      rewrite bind_assoc.
      setoid_rewrite IHn.
      clear IHn.

      setoid_rewrite nAfter_nonempty.
      setoid_rewrite union_symmetric.

      setoid_rewrite sDefined_union.
      setoid_rewrite sDefined_singleton.
      unfold offset.
      rewrite <- (semiNeutral_put_put MEM (defined _)).
      setoid_rewrite (confined_put SP) at 1.
      * reflexivity.
      * unshelve eapply (confined_neutral _ (Hmx := confined_defined _)).

    + clear x. (* Where did this come from? *)
      unshelve eapply (confined_neutral _ (Hmx := confined_defined _)).
      set (a := toB64 _).
      set (u := nAfter _ _).

      assert (Independent (MEM' u) (MEM'' a)) as Hi.
      * setoid_rewrite point_mem''.
        unfold MEM'.
        apply composite_independent_r.
        apply separate_independent.
        intros x [Hu Ha].
        subst a u.
        unfold nAfter, singleton, def, member in Hu, Ha.
        apply asBool_decide' in Hu, Ha.
        destruct Hu as [i [Hi Hi']].
        subst x.




Qed.




    symmetry.
    destruct (decide _) as [H|H]; [ reflexivity | ].
    contradict H. intros a.
    destruct (decide _) as [HH|HH]; [ | easy ].
    exfalso. destruct HH. lia.
  - setoid_rewrite popMany_S.
    setoid_rewrite to_list_action.
    setoid_rewrite pushMany_action.
    setoid_rewrite pushMany_one.
    setoid_rewrite (collapse_bind_lift pop_push).

    smon_rewrite01.
    setoid_rewrite (popMany_getSP n).
    setoid_rewrite lens_put_get.

    transitivity (
      put' MEM mem;;
      let* u := (put' SP sp;; popMany n) in
      defined (toB64 (n + sp));;
      pushMany u).
    + now smon_rewrite01.
    + setoid_rewrite <- (confined_popMany' sp n _);
      [ | eapply (confined_neutral _ (Hmx := confined_defined _)) ].
      rewrite (semiNeutral_put_put MEM (defined _)).
      rewrite bind_assoc.
      setoid_rewrite IHn.
      clear IHn.
      fold sDefined.




Proposition popMany_pushMany n :
  let* u := popMany n in
  pushMany u =
    let* sp := get' SP in
    sDefined (nAfter n sp).
Proof.
  unfold nAfter, sDefined, def, member.
  smon_ext' SP sp.
  setoid_rewrite lens_put_get.
  setoid_rewrite <- (confined_put SP _) at 2.
  2: solve [typeclasses eauto].
  smon_ext' MEM mem.
  setoid_rewrite lens_put_get.
  induction n.
  - simp popMany. setoid_rewrite ret_bind. cbn.
    rewrite pushMany_empty.
    do 2 (apply bind_extensional; intros []).
    destruct (decide _) as [H|H]; [ reflexivity | ].
    contradict H. intros a.
    destruct (decide _) as [HH|HH]; [ | easy ].
    exfalso. destruct HH. lia.
  - setoid_rewrite popMany_S.
    setoid_rewrite to_list_action.
    setoid_rewrite pushMany_action.
    setoid_rewrite pushMany_one.
    setoid_rewrite (collapse_bind_lift pop_push).

    smon_rewrite01.
    setoid_rewrite (popMany_getSP n).
    setoid_rewrite lens_put_get.

    transitivity (
      put' MEM mem;;
      let* u := (put' SP sp;; popMany n) in
      defined (toB64 (n + sp));;
      pushMany u).
    + now smon_rewrite01.
    + setoid_rewrite <- (confined_popMany' sp n _);
      [ | eapply (confined_neutral _ (Hmx := confined_defined _)) ].
      rewrite (semiNeutral_put_put MEM (defined _)).
      rewrite bind_assoc.
      setoid_rewrite IHn.
      clear IHn.
      fold sDefined.






      rewrite defined_spec.
      destruct (decide (available _)) as [Hn|Hn].
      2: {
        smon_rewrite01.
        set (d := decide _).
        destruct d as [H|H]; [ | now smon_rewrite01 ].
        exfalso.
        set (a := toB64 (n + sp)) in *.
        contradict Hn.
        specialize (H a).
        rewrite asBool_decide' in H.
        apply H.
        exists n.
        split; [ lia | reflexivity ].
      }
      smon_rewrite. (* TODO: slow! *)
      destruct (mem _) as [Hn'|] eqn:en.
      2: {
        smon_rewrite01.
        set (a := toB64 (n + sp)) in *.
        set (d := decide _).
        destruct d as [H|H]; [ | now smon_rewrite01 ].
        exfalso.


      }.
      admit.




        --

          (spec)

          Set Printing Coercions.
          as_bool
          rewrite (asBool_decide _) in H.


          destruct H.


        contradict H.

        admit.
        -- now smon_rewrite01.


      rewrite <- (semiNeutral_put_put MEM (defined _)).
      setoid_rewrite <- confined_defined; [ | typeclasses eauto ].
      apply bind_extensional. intros [].
      apply bind_extensional. intros [].






      * admit.
      * typeclasses eauto.

      smon_rewrite. (* TODO: Very slow *)
      rewrite <- bind_assoc.
      setoid_rewrite bind_assoc at 2.

      setoid_rewrite <- (semiNeutral_put_put MEM (defined _)).


      rewrite (semiNeutral_get_put (X:=unit) MEM (defined _)).
      smon_rewrite. (* TODO: Very slow *)
      rewrite (semiNeutral MEM (semiNeutral_defined _)).
      repeat setoid_rewrite bind_assoc.



    match goal with [ |- _ = ?h ] => set (hs := h) end.


    transitivity (
      put' MEM mem;;
      defined (toB64 (n + sp));;
      put' MEM mem;;
      let* u := (put' SP sp;; popMany n) in
      pushMany u).
    + setoid_rewrite <- (confined_popMany' sp n _).

    rewrite (lens_semiNeutral (sub_semiNeutral (semiNeutral_defined _) MEM)).
      smon_rewrite.
    sndMixer
    setoid_rewrite <- confined_defined.
      setoid_rewrite (confined_popMany' sp n _).
      smon_rewrite.




    + now smon_rewrite01.
    + setoid_rewrite <- (confined_popMany' sp n _);
      [ | eapply (confined_neutral _ (Hmx := confined_defined _)) ].






    transitivity (
      put' MEM mem;;
      let* u := (put' SP sp;; popMany n) in
      defined (toB64 (n + sp));;
      pushMany u).
    + now smon_rewrite01.
    + setoid_rewrite <- (confined_popMany' sp n _);
      [ | eapply (confined_neutral _ (Hmx := confined_defined _)) ].




      setoid_rewrite confined_defined.

      repeat setoid_rewrite bind_assoc.
      setoid_rewrite IHn.
      setoid_rewrite <- confined_defined.
      setoid_rewrite <- confined_defined.
      * admit.
      * typeclasses eauto.
      *



  by_lia (S n = (n + 1)%nat) as H.
    setoid_rewrite H.

    popMany_action
    smon_ext' SP sp.
    setoid_rewrite lens_put_get.
    setoid_rewrite <- (confined_put SP _).

    destruct (decide (forall a: B64, _)).




    Transparent pushMany.
    unfold pushMany.




  setoid_rewrite popMany_spec.
  smon_ext' SP sp.
  smon_rewrite. (* TODO: Slow! *)
  setoid_rewrite <- (confined_put SP _).
  2, 3: apply (confined_neutral (m':=MEM)); typeclasses eauto.
  smon_ext' MEM mem.
  smon_rewrite.

  setoid_rewrite loadMany_spec_fromMem.
  smon_rewrite.



  setoid_rewrite (assume'_proper _ _ (asBool_decide _)).
  set (b := as_bool (decide _)).
  setoid_rewrite (asBool_decide _).
  induction n.
  - simp popMany.
  smon_rewrite.

(* Continue from here *)

Admitted.
