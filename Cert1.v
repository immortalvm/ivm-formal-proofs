From iVM Require Import DSet Mono Cert0.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(*****************)

Global Opaque pushMany. (* TODO *)

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
Global Opaque longsToBytes.

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
  - rewrite lens_put_get.
    reflexivity.
  - apply neutral_get.
    typeclasses eauto.
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

Global Opaque defined.

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
  -
    setoid_rewrite lens_put_get.
    setoid_rewrite lens_put_put.
    setoid_rewrite <- confined_load.
    +
      assert (toB64 (-1 + toB64 (1 + sp)) = sp) as Hsp.
      *
        transitivity (offset (-1) (offset 1 sp)).
        -- reflexivity.
        -- rewrite <- Z_action_add. cbn. apply Z_action_zero.
      *
        rewrite Hsp.
        rewrite load_store.
        reflexivity.
    + typeclasses eauto.
  - typeclasses eauto.
Qed.

(***)

Definition pushN {n} (u: vector B64 n) := pushMany (longsToBytes u).

Definition pushN_spec := unfolded_eq (@pushN).

Global Opaque pushN.

Definition sDefined u :=
  let* mem := get' MEM in
  assume' (forall a (Hu: a ∈ u), exists (Ha: available a), mem a Ha).

Proposition popMany_pushMany n :
  let* u := popMany n in
  pushMany u =
    let* sp := get' SP in
    sDefined (nAfter n sp).
Proof.

(* Continue from here *)

Admitted.
