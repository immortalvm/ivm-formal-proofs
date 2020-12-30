(** The contents of this file will be either integrated with Cert.v or moved elsewhere. *)

From iVM Require Import DSet Mono.
Import DSetNotations.

Unset Suggest Proof Using.

Open Scope vector.

(* TODO: Place inside section or module. *)
Import OpCodes.

(* TODO: Move? *)
Global Opaque next.

Open Scope Z.


(** ** Preliminaries / to be moved *)

(* TODO: Delete / move to end of Operations.v. *)
(* Notation "⫫" := (@fstMixer State). *)

(* TODO: Move *)
Proposition sub_put_spec {A B} {LA: Lens State A} {LB: Lens A B} (b: B) :
  put' (LB ∘ LA) b = let* a := get' LA in
                     put' LA (update a b).
Proof.
  setoid_rewrite put_spec'.
  setoid_rewrite get_spec.
  smon_rewrite.
Qed.

(* TODO: Make definition in Operations.v global instead. *)
Global Ltac simp_loadMany := rewrite_strat (outermost (hints loadMany)).

(* TODO: Move to Operations.v ? *)
Global Opaque loadMany.
Global Opaque load.

Proposition postpone_assume P {DP: Decidable P} {X} (mx: M X) {Y} (f: X -> M Y) :
  assume P;;
  let* x := mx in
  f x = let* x := mx in
        assume P;;
        f x.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

Lemma assume_cons {A} (EA: EqDec A) (a a': A) n (u u': vector A n) {X} (mx: M X) :
  assume (a :: u = a' :: u');;
  mx = assume (a = a');;
       assume (u = u');;
       mx.
Proof.
  destruct (decide (a :: u = a' :: u')) as [He|He].
  - rewrite ret_bind.
    apply cons_inj in He.
    destruct He as [Ha Hu].
    decided Ha.
    decided Hu.
    now do 2 rewrite ret_bind.
  - destruct (decide (a = a')) as [Ha|Ha];
      destruct (decide (u = u')) as [Hu|Hu].
    1: exfalso. congruence.
    all: smon_rewrite.
Qed.


(* TODO: Move to Init.v ? *)

Proposition vector_map_equation_1 {A B} (f: A -> B) : Vector.map f [] = [].
Proof.
  reflexivity.
Qed.

Proposition vector_map_equation_2 {A B} (f: A -> B) (x: A) {n} (u: vector A n) : Vector.map f (x :: u) = f x :: Vector.map f u.
Proof.
  reflexivity.
Qed.

Hint Rewrite @vector_map_equation_1 : map.
Hint Rewrite @vector_map_equation_2 : map.

Global Opaque Vector.map.


Lemma next_1_helper (op: Z) (Hop: 0 <= op < 256) :
  (Vector.map toB8 [op] : Bytes 1) = Z.to_N op :> N.
Proof.
  simp map.
  remember (toB8 op) as u eqn:Hu.
  dependent elimination u as [[b0; b1; b2; b3; b4; b5; b6; b7]].
  simp bytesToBits. simpl. rewrite Hu.
  unfold bitsToN. f_equal.
  apply fromBits_toBits. cbn. lia.
Qed.

Lemma step_match_helper (op: Z) (Hop: 0 <= op < 256) :
  Z.of_N (bitsToN (bytesToBits (cells_to_bytes (Vector.map toB8 [op])))) = op.
Proof.
  unfold cells_to_bytes, id.
  rewrite next_1_helper;
    [ rewrite Z2N.id | ];
    lia.
Qed.


Proposition chain_ret_true u : chain u (ret true) = u.
Proof.
  unfold chain.
  rewrite <- bind_ret.
  apply bind_extensional.
  intros [|]; reflexivity.
Qed.

(* TODO: Move *)
Corollary toBits_cong' n z : cong n (toBits n z) z.
Proof.
  rewrite ofN_bitsToN, fromBits_toBits_mod.
  apply cong_mod.
  lia.
Qed.

(* TODO: Move *)
Hint Opaque cong : rewrite.

(* TODO: Move *)
Instance cong_equivalence n : Equivalence (cong n).
Proof.
  typeclasses eauto.
Qed.

(* TODO: Move *)
Ltac cong_tac :=
  apply toBits_cong;
  rewrite toBits_cong';
  apply eq_cong;
  lia.

(* TODO: Move *)
Lemma nAfter_action (a: B64) (m n: nat) :
  nAfter (m + n) a = (nAfter m a ∪ nAfter n (offset m a))%DSet.
Proof.
  revert a; induction m; intros a.
  - unfold offset. cbn.
    rewrite ofN_bitsToN, toBits_fromBits.
    apply extensionality. intro x.
    rewrite union_spec.
    unfold nAfter.
    setoid_rewrite def_spec.
    split.
    + intros H. right. exact H.
    + intros [H|H].
      * exfalso. destruct H as [i [H _]]. lia.
      * exact H.

  - unfold offset.
    apply extensionality. intro x.
    rewrite union_spec.
    unfold nAfter.
    setoid_rewrite def_spec.
    split.
    + intros [i [H1 H2]].
      by_lia (i < S m \/ S m <= i < S m + n)%nat as H.
      destruct H as [H|H].
      * left. exists i. split.
        -- exact H.
        -- exact H2.
      * right. exists (i - S m)%nat. split.
        -- lia.
        -- rewrite <- H2. cong_tac.
    + intros [[i [H1 H2]] | [i [H1 H2]]].
      * exists i. split.
        -- lia.
        -- exact H2.
      * exists (S m + i)%nat. split.
        -- lia.
        -- rewrite <- H2. cong_tac.
Qed.

(* TODO: Move *)
Instance cong_toBits_proper n : Proper (cong n ==> eq) (toBits n).
Proof. intros z z' Hz. apply toBits_cong. exact Hz. Qed.

(* TODO: Move *)
Corollary fromBits_toBits' n (u: Bits n) : toBits n u = u.
Proof. rewrite ofN_bitsToN. apply toBits_fromBits. Qed.

(* TODO: Useful? *)
Proposition generalizer
      {MP1 : MachineParams1}
      {MP2 : MachineParams2}
      {X Y: Type}
      {mx: M X}
      {f: X -> M Y}
      {my: M Y}
      (H : mx >>= f = my)
      {Z: Type}
      (g: Y -> M Z) : let* x := mx in
                     let* y := f x in
                     g y = let* y := my in
                           g y.
Proof.
  rewrite <- bind_assoc.
  rewrite H.
  reflexivity.
Qed.

(* TODO: Move to Mon.v *)
Lemma put_get_prime
      {MP1 : MachineParams1}
      {MP2 : MachineParams2}
      {X : Type}
      {LX: Lens State X} (x: X) : put' LX x;; get' LX = put' LX x;; ret x.
Proof.
  (* TODO: Use lens_transfer tactic *)
  setoid_rewrite get_spec.
  setoid_rewrite put_spec'.
  repeat rewrite <- bind_spec.
  smon_rewrite'.
Qed.

(* TODO: Move. *)
(** Making this an instance confuses the proof search.
    Maybe this could somehow be made into an instance of [Proper] instead? *)
Proposition decidable_proper {P} {D: Decidable P} {Q} (H: Q <-> P) : Decidable Q.
Proof.
  destruct D; [left|right]; tauto.
Defined.

(* TODO: Move *)
Lemma bounded_all_neg P {DP: forall (x:nat), Decidable (P x)} n :
  not (forall x, (x < n)%nat -> P x) -> (exists x, (x < n)%nat /\ not (P x)).
Proof.
  induction n; intro H.
  - exfalso. apply H. intros x Hx. exfalso. lia.
  - destruct (decide (P n)) as [Hd|Hd].
    + assert (~ forall x : nat, (x < n)%nat -> P x) as Hnot.
      * intros Hno.
        apply H.
        intros x Hx.
        by_lia (x < n \/ x = n)%nat as H0.
        destruct H0 as [H1|H2].
        -- apply Hno. exact H1.
        -- destruct H2. exact Hd.
      * specialize (IHn Hnot).
        destruct IHn as [x [Hx Hp]].
        exists x. split.
        -- lia.
        -- exact Hp.
    + exists n. split.
      * lia.
      * exact Hd.
Qed.

(* TODO: Move. Are there better ways to do this? *)
Definition bounded_evidence
           P {DP: forall (x:nat), Decidable (P x)}
           n (H: exists x, (x < n)%nat /\ P x) : { x: nat | (x < n)%nat /\ P x }.
Proof.
  induction n.
  - exfalso. destruct H as [x [H1 H2]]. lia.
  - specialize (DP n). destruct DP as [H1|H2].
    + refine (exist _ n _). split; [lia | exact H1].
    + assert (exists (x: nat), (x < n)%nat /\ P x) as He.
      * destruct H as [x [Hsn Hx]].
        exists x. split; [ | exact Hx ].
        by_lia (x < n \/ x = n)%nat as Hn.
        destruct Hn as [Hn|Hn]; [ exact Hn | ].
        destruct Hn. exfalso. exact (H2 Hx).
      * specialize (IHn He).
        destruct IHn as [x [IH1 IH2]].
        refine (exist _ x _).
        split; [lia | exact IH2].
Defined.

Proposition nAfter_disjoint_spec u n a :
  u # nAfter n a <-> forall i, (i<n)%nat -> not (offset i a ∈ u).
Proof.
  unfold nAfter, disjoint.
  setoid_rewrite def_spec.
  split; intro H.
  - intros i Hi Ho.
    apply (H (offset i a)).
    split.
    + exact Ho.
    + now exists i.
  - intros x [Hx [i [Hi Ha]]].
    apply (H i Hi).
    unfold offset.
    rewrite Ha.
    exact Hx.
Qed.

Instance nAfter_disjoint_decidable u n a : Decidable (u # nAfter n a).
Proof.
  refine (decidable_proper (nAfter_disjoint_spec _ _ _)).
Defined.

Proposition not_nAfter_disjoint_spec u n a :
  not (u # nAfter n a) -> exists i, (i<n)%nat /\ offset i a ∈ u.
Proof.
  rewrite nAfter_disjoint_spec.
  intros H.
  apply bounded_all_neg in H.
  - setoid_rewrite decidable_raa in H. exact H.
  - typeclasses eauto.
Qed.

Definition not_nAfter_disjoint_evidence u n a (H : not (u # nAfter n a)) :
  { x: Addr | x ∈ u /\ exists i, (i < n)%nat /\ offset i a = x }.
Proof.
  apply not_nAfter_disjoint_spec in H.
  apply bounded_evidence in H; [ | typeclasses eauto ].
  destruct H as [i [Hi Hu]].
  refine (exist _ (offset i a) _).
  split.
  - exact Hu.
  - now exists i.
Defined.


(* TODO: Move to Binary.v *)
(** Cf. [bitsToBytes] *)
Definition bytesToLongs {n} (u: Bytes (n * 8)) : vector B64 n.
Proof.
  induction n.
  - exact [].
  - simpl in u.
    dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u].
    exact ((b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) :: IHn u).
Defined.

Proposition bytesToLongs_equation_1 : @bytesToLongs (0 * 8) [] = [].
Proof. reflexivity. Qed.

Proposition bytesToLongs_equation_2 {n} b0 b1 b2 b3 b4 b5 b6 b7 (u: Bytes (n * 8)) :
  @bytesToLongs (S n) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u) =
  (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) :: bytesToLongs u.
Proof. reflexivity. Qed.

Hint Rewrite bytesToLongs_equation_1 @bytesToLongs_equation_2 : bytesToLongs.
Global Opaque bytesToLongs.


Equations popN (n: nat) : M (vector B64 n) :=
  popN 0 := ret [];
  popN (S n) := let* h := pop64 in
                let* r := popN n in
                ret (h :: r).

(* TODO: Move *)
Global Opaque popMany.

Proposition bytesToBits_equation_2' {n} b (u: Bytes n) :
  @bytesToBits (S n) (b :: u) = b ++ bytesToBits u.
Proof.
  dependent elimination b as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: []].
  simp bytesToBits.
  reflexivity.
Qed.

(* Proposition append_nil {A} {n} (u: vector A n) : u ++ [] = u. *)

Proposition bytesToLongs_equation_2' {n} b0 b1 b2 b3 b4 b5 b6 b7 (u: Bytes (n * 8)) :
  @bytesToLongs (S n) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u) =
  (([b0; b1; b2; b3; b4; b5; b6; b7] : Bytes 8) : B64) :: bytesToLongs u.
Proof.
  (* TODO: Can this be done more elegantly? *)
  simp bytesToLongs.
  repeat rewrite bytesToBits_equation_2'.
  repeat f_equal.
  dependent elimination b7 as [c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: []].
  reflexivity.
Qed.

Proposition popN_spec n :
  popN n = let* u := popMany (n * 8) in
           ret (bytesToLongs u).
Proof.
  induction n.
  - simp popMany. smon_rewrite.
  - simp popN.
    change (S n * 8)%nat with (S (S (S (S (S (S (S (S (n * 8)))))))))%nat.
    setoid_rewrite IHn.
    unfold pop64.
    simp popMany.
    smon_rewrite.
    setoid_rewrite bytesToLongs_equation_2'.
    reflexivity.
Qed.


Proposition nAfter_empty a : nAfter 0 a = ∅%DSet.
Proof.
  apply extensionality.
  intros x.
  unfold nAfter.
  rewrite def_spec.
  transitivity False.
  - split.
    + intros [i [Hi _]]. lia.
    + tauto.
  - set (H := @empty_spec _ x). tauto.
Qed.

Proposition simp_assume P {DP: Decidable P} {X} (mx: M X) :
  assume P;; mx = if decide P
                  then mx
                  else err.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

Ltac simp_assume := setoid_rewrite simp_assume.

(* TODO: Move *)
Instance decidable_iff {P Q} (H: P <-> Q) {DP: Decidable P} : Decidable Q.
Proof.
  destruct DP; [left|right]; tauto.
Defined.

(* Presumably in coq-hott this could be an actual instance of Proper. *)
Proposition decide_proper
            {P Q}
            {DP: Decidable P}
            {DQ: Decidable Q}
            (H: P <-> Q)
            {X} (x x':X) :
  (if decide P then x else x') = (if decide Q then x else x').
Proof.
  destruct (decide P) as [Hp|Hp];
    destruct (decide Q) as [Hq|Hq];
    reflexivity || tauto.
Qed.

(* TODO: Move *)
Proposition decide_true
          {P} {DP: Decidable P} (H: P) {X} (x x':X) :
  (if decide P then x else x') = x.
Proof.
  decided H. reflexivity.
Qed.


Proposition rew_cons [X m n x] [u: vector X m] [HS: S m = S n] (H: m = n) :
  rew HS in (x :: u) = x :: rew H in u.
Proof.
  destruct H. revert HS. apply EqDec.UIP_K. reflexivity.
Qed.

Proposition shiftin_spec [X n] [x: X] [u: vector X n] (H: (n + 1 = S n)%nat) :
  shiftin x u = rew H in (u ++ [x]).
Proof.
  induction u.
  - revert H. apply EqDec.UIP_K. reflexivity.
  - cbn in *.
    set (HH := Nat.succ_inj _ _ H). rewrite (rew_cons HH).
    f_equal. exact (IHu HH).
Qed.

(** We would have preferred to call this [shiftout_shiftin], but we stick
to the same naming pattern of VectorSpec. *)

Proposition shiftin_shiftout
            [X n] (x: X) (u: vector X n) :
  shiftout (shiftin x u) = u.
Proof.
  induction u.
  - reflexivity.
  - cbn. rewrite IHu. reflexivity.
Qed.

Proposition last_shiftout_shifting [X n] (u: vector X (S n)) :
  shiftin (Vector.last u) (shiftout u) = u.
Proof.
  induction n.
  - dependent elimination u as [[x]]. reflexivity.
  - dependent elimination u as [x :: u].
    cbn. f_equal. exact (IHn u).
Qed.

(** Cf. [List.rev_ind]. *)
Proposition vec_rev_ind
            [A : Type]
            (P : forall {n}, vector A n -> Prop)
            (H_nil: P [])
            (H_cons: forall {n} (u: vector A n) x, P u -> P (shiftin x u))
            {n} (u: vector A n) : P u.
Proof.
  induction n.
  - dependent elimination u. exact H_nil.
  - specialize (H_cons n (shiftout u) (Vector.last u) (IHn (shiftout u))).
    rewrite last_shiftout_shifting in H_cons. exact H_cons.
Qed.

Corollary vec_rev_ind'
          [A : Type]
          (P : forall {n}, vector A n -> Prop)
          (H_nil: P [])
          (H_cons: forall {n} (u: vector A n) x, P u -> P (u ++ [x]))
          {n} (u: vector A n) : P u.
Proof.
  induction u using vec_rev_ind.
  - exact H_nil.
  - set (H := Nat.add_1_r n).
    rewrite (shiftin_spec H).
    destruct H.
    exact (H_cons n u x IHu).
Qed.

Hint Rewrite nAfter_empty : nAfter.

(* TODO: Needed? *)
(* Proposition nAfter_equation_2 a n :
  nAfter (S n) a = (!{ a } ∪ nAfter n (offset 1 a))%DSet.
Proof.
  unfold nAfter.
  unfold union.
  apply extensionality.
  intros x.
  setoid_rewrite def_spec.
  split.
  - intros [i [Hi Hx]].
    by_lia (i = n \/ i < n) as Hii.
    destruct Hii as [Hi1|Hi2].
Admitted. *)

Instance chain_propr : PropR chain.
Proof.
  intros u u' Hu v v' Hv.
  unfold chain.
  apply (bind_propr _ _ _).
  - exact Hu.
  - intros x x' Hx.
    cbv in Hx.
    subst x.
    destruct x'.
    + exact Hv.
    + crush.
Qed.


(* TODO: Why do we have to repeat this? *)
Global Opaque bytesToBits.

Proposition bytesToBits_equation_3 (u: B8) : bytesToBits [u] = u.
Proof.
  dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: []].
  reflexivity.
Qed.

Hint Rewrite @bytesToBits_equation_3 : bytesToBits.

Proposition id_equation_1 X (x: X) : id x = x.
Proof. reflexivity. Qed.

(* TODO: Move *)
Proposition negb_not (b: bool) : negb b <-> not b.
Proof.
  destruct b; now cbn.
Qed.


(** * Certified programs *)

Definition Cert (spec: M bool) :=
  exists (f: State -> nat), spec ⊑ let* s := get in
                           nSteps (f s).

(** In most cases we know exactly how many steps are needed. *)
Definition nCert n (spec: M bool) := spec ⊑ nSteps n.

Proposition nCert_is_Cert n (spec: M bool) : nCert n spec -> Cert spec.
Proof.
  unfold nCert, Cert.
  intros H.
  exists (fun _ => n).
  smon_rewrite.
  exact H.
Qed.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

Lemma cert_id : nCert 0 not_terminated.
Proof.
  unfold nCert.
  simp nSteps.
  crush.
Qed.

Lemma ncert_comp m n (u: M bool) {Cu: nCert m u} (v: M bool) {Cv: nCert n v} :
  nCert (m + n) (chain u v).
Proof.
  unfold nCert in *.
  rewrite nSteps_action.
  apply chain_propr.
  - exact Cu.
  - exact Cv.
Qed.

Definition nCertN n {X} (mx: M X) := nCert n (mx;; not_terminated).


(** *** Asserting next operations and move PC *)

Definition swallow1 (op: Z) : M unit :=
  let* pc := get' PC in
  let* x := load pc in
  assume (x = toB8 op);;
  put' PC (offset 1 pc).

Equations swallow {n} (ops: vector Z n) : M unit :=
  swallow [] := ret tt;
  swallow (op :: rest) :=
    swallow1 op;;
    swallow rest.

Lemma swallow_spec {n} (ops: vector Z n) :
  swallow ops = let* pc := get' PC in
                let* u := loadMany n pc in
                assume (u = Vector.map toB8 ops);;
                put' PC (offset n pc).
Proof.
  (* TODO: Simplify *)
  induction n.
  - dependent elimination ops.
    simp swallow map.
    simp_loadMany.
    unfold offset.
    smon_rewrite. setoid_rewrite toBits_ofN_bitsToN.
    smon_rewrite.
  - dependent elimination ops as [ @Vector.cons z n ops ].
    simp swallow map. unfold swallow1. rewrite IHn.
    simp_loadMany.
    smon_rewrite.

    apply bind_extensional. intros pc.
    apply bind_extensional. intros op.

    do 3 setoid_rewrite postpone_assume.
    smon_rewrite.
    setoid_rewrite <- confined_put;
      [ | apply (confined_neutral (m:=MEM));
          typeclasses eauto ].

    apply bind_extensional. intros u.
    simpl Vector.map.

    unfold Cells. (* TODO: How can we avoid having to remember this everywhere? *)
    setoid_rewrite assume_cons.
    destruct (decide (op = toB8 z)) as [Hop|Hop]; [ | smon_rewrite ].
    subst op.
    destruct (decide _) as [Hu|Hu]; [ | smon_rewrite ].
    subst u.
    smon_rewrite.
    setoid_rewrite <- Z_action_add.
    do 2 f_equal.
    lia.
Qed.

Instance confined_swallow {n} (ops: vector Z n) :
  Confined (MEM * PC) (swallow ops).
Proof.
  rewrite swallow_spec.
  typeclasses eauto.
Qed.

Lemma swallow_action {m n} (o1: vector Z m) (o2: vector Z n) :
  swallow (o1 ++ o2) = swallow o1;; swallow o2.
Proof.
  induction m.
  - dependent elimination o1.
    simp swallow.
    smon_rewrite.
  - dependent elimination o1 as [ @Vector.cons x m o1 ].
    simpl (swallow _).
    simp swallow.
    rewrite (IHm o1).
    rewrite bind_assoc.
    reflexivity.
Qed.

Proposition swallow1' (op: Z) n (ops: vector Z n) :
  swallow (op :: ops) = swallow ([op] ++ ops).
Proof.
  reflexivity.
Qed.

Lemma swallow_lemma {n} {ops: vector Z n} {X} {u: M X} {f: Bytes n -> M X} :
  u ⊑ f (Vector.map toB8 ops) -> swallow ops;; u ⊑ next n >>= f.
Proof.
  intros H.
  repeat setoid_rewrite bind_assoc.
  revert ops u f H.
  induction n; intros ops u f H; simp next.
  - dependent elimination ops. simp swallow.
    setoid_rewrite ret_bind. exact H.
  - dependent elimination ops as [Vector.cons (n:=n) x r].
    simp swallow.
    unfold swallow1.
    repeat setoid_rewrite bind_assoc.
    crush.
    smon_rewrite.
    subst.
    exact (IHn r u (fun v => f (toB8 x :: v)) H).
Qed.

Proposition swallow_equation_3 (n : nat) (z : Z) (u : vector Z n) :
  swallow (shiftin z u) = swallow u;;
                          swallow1 z.
Proof.
  set (H := Nat.add_1_r n).
  rewrite (shiftin_spec H).
  destruct H. cbn.
  rewrite swallow_action. simp swallow.
  setoid_rewrite bind_ret_tt.
  reflexivity.
Qed.

Hint Rewrite swallow_equation_3 : swallow.


(** ** EXIT *)

Ltac cert_start :=
  unfold nCert;
  simp nSteps;
  unfold chain, oneStep;
  repeat setoid_rewrite bind_assoc;
  apply swallow_lemma;
  setoid_rewrite next_1_helper; [ | lia ];
  try (unfold cells_to_bytes, id;
       rewrite next_1_helper; try lia);
  simpl;
  repeat rewrite ret_bind;
  crush.

Proposition cert_EXIT : nCert 1 (swallow [EXIT];;
                           terminated).
Proof. cert_start. Qed.

Proposition cert_NOP : nCertN 1 (swallow [NOP]).
Proof. unfold nCertN. cert_start. Qed.

(**********************)

Proposition andb_spec (x y: bool) : x && y <-> x /\ y.
Proof.
  destruct x, y; now cbn.
Qed.

Proposition Is_true_spec (b: bool) : b <-> b = true.
Proof.
  destruct b; now cbn.
Qed.

Proposition ltb_spec (x y: Z) : x <? y <-> x < y.
Proof.
  rewrite Is_true_spec, Z.ltb_lt. tauto.
Qed.

Notation isStdOp op := (0 < op < 256).

Proposition isStdOp_toB8 {op} (Hop: isStdOp op) : toB8 op = op :> Z.
Proof.
  rewrite ofN_bitsToN.
  apply fromBits_toBits.
  lia.
Qed.

Proposition isStdOp_match0 {op} (Hop: isStdOp op) {X} (u v: X) :
  match op with 0 => u | _ => v end = v.
Proof.
  now destruct op.
Qed.



(** ** Not exit *)

(* TODO: Expand and maybe move *)
Ltac binary_simpl_tac :=
  unfold cells_to_bytes;
  try simp map;
  try rewrite id_equation_1;
  try rewrite bytesToBits_equation_3.

Lemma swallow_step_lemma n op n' (ops: vector Z n') mb
    (Hop: isStdOp op)
    (H: swallow ops;; mb ⊑ oneStep' op;; nSteps n) :
  nCert (S n) (swallow (op :: ops);; mb).
Proof.
  unfold nCert.
  simp nSteps.
  unfold chain.
  unfold oneStep.
  rewrite swallow1'.
  rewrite swallow_action.
  smon_rewrite.
  apply swallow_lemma.
  simp map.

  binary_simpl_tac.
  setoid_rewrite (isStdOp_toB8 Hop).
  setoid_rewrite (isStdOp_match0 Hop).
  smon_rewrite.
  setoid_rewrite (isStdOp_toB8 Hop).
  exact H.
Qed.

Corollary swallow_step_lemma' n op mb
    (Hop: isStdOp op)
    (H: mb ⊑ oneStep' op;; nSteps n) :
  nCert (S n) (swallow [op];; mb).
Proof.
  apply swallow_step_lemma; [ exact Hop | ].
  simp swallow.
  smon_rewrite.
  exact H.
Qed.

Corollary swallow_step_lemma_N n op n' (ops: vector Z n') X (mx: M X)
  (Hop: isStdOp op)
  (H: (swallow ops;; mx);; not_terminated ⊑ oneStep' op;; nSteps n) :
  nCertN (S n) (swallow (op :: ops);; mx).
Proof.
  unfold nCertN. revert H.
  smon_rewrite. intros H.
  apply swallow_step_lemma; assumption.
Qed.

Corollary swallow_step_lemma_N' n op X (mx: M X)
  (Hop: isStdOp op)
  (H: mx;; not_terminated ⊑ oneStep' op;; nSteps n) :
  nCertN (S n) (swallow [op];; mx).
Proof.
  apply swallow_step_lemma_N; [ exact Hop | ].
  simp swallow.
  smon_rewrite.
  exact H.
Qed.


(* TODO: Move? *)
Proposition bind_ret_helper {X Y Z} {mx: M X} {y: Y} {f: Y -> M Z} :
  mx;; ret y >>= f = mx;; f y.
Proof.
  rewrite bind_assoc, ret_bind. reflexivity.
Qed.

(* TODO: Remove? *)
Proposition not_terminated_helper X (mx: M X) Y (f: X -> M Y) :
  let* x := mx in
  let* y := f x in
  not_terminated = (let* x := mx in f x);;
                   not_terminated.
Proof.
  smon_rewrite.
Qed.

Ltac swallow1_tac :=
  unfold nCertN;
  apply swallow_step_lemma_N';
  [ lia | ];
  simp nSteps;
  apply (bind_propr _ _ _);
  [ simp oneStep' |  ];
  crush.

(** ** Instructions with no operands *)

Proposition cert_JUMP : nCertN 1 (
  swallow [JUMP];;
  let* a := pop64 in
  put' PC a).
Proof. swallow1_tac. Qed.

Proposition cert_SET_SP : nCertN 1 (
  swallow [SET_SP];;
  let* a := pop64 in
  put' SP a).
Proof. swallow1_tac. Qed.

Proposition cert_GET_PC : nCertN 1 (
  swallow [GET_PC];;
  let* a := get' PC in
  pushZ a).
Proof. swallow1_tac. Qed.

Proposition cert_GET_SP : nCertN 1 (
  swallow [GET_SP];;
  let* a := get' SP in
  pushZ a).
Proof. swallow1_tac. Qed.

(* For the other push instructions, see below. *)
Proposition cert_PUSH0 : nCertN 1 (
  swallow [PUSH0];;
  pushZ 0).
Proof. swallow1_tac. Qed.

Proposition cert_LOAD1 : nCertN 1 (
  swallow [LOAD1];;
  let* a := pop64 in
  let* x := loadMany 1 a in
  pushZ x).
Proof. swallow1_tac. Qed.

Proposition cert_LOAD2 : nCertN 1 (
  swallow [LOAD2];;
  let* a := pop64 in
  let* x := loadMany 2 a in
  pushZ x).
Proof. swallow1_tac. Qed.

Proposition cert_LOAD4 : nCertN 1 (
  swallow [LOAD4];;
  let* a := pop64 in
  let* x := loadMany 4 a in
  pushZ x).
Proof. swallow1_tac. Qed.

Proposition cert_LOAD8 : nCertN 1 (
  swallow [LOAD8];;
  let* a := pop64 in
  let* x := loadMany 8 a in
  pushZ x).
Proof. swallow1_tac. Qed.

Proposition cert_STORE1 : nCertN 1 (
  swallow [STORE1];;
  let* a := pop64 in
  let* x := pop64 in
  storeZ 1 a x).
Proof. swallow1_tac. Qed.

Proposition cert_STORE2 : nCertN 1 (
  swallow [STORE2];;
  let* a := pop64 in
  let* x := pop64 in
  storeZ 2 a x).
Proof. swallow1_tac. Qed.

Proposition cert_STORE4 : nCertN 1 (
  swallow [STORE4];;
  let* a := pop64 in
  let* x := pop64 in
  storeZ 4 a x).
Proof. swallow1_tac. Qed.

Proposition cert_STORE8 : nCertN 1 (
  swallow [STORE8];;
  let* a := pop64 in
  let* x := pop64 in
  storeZ 8 a x).
Proof. swallow1_tac. Qed.

Proposition cert_ADD : nCertN 1 (
  swallow [ADD];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (x + y)).
Proof. swallow1_tac. Qed.

Proposition cert_MULT : nCertN 1 (
  swallow [MULT];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (x * y)).
Proof. swallow1_tac. Qed.

Proposition cert_DIV : nCertN 1 (
  swallow [DIV];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (if decide (x = 0 :> Z) then 0 else y / x)).
Proof. swallow1_tac. Qed.

Proposition cert_REM : nCertN 1 (
  swallow [REM];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (if decide (x = 0 :> Z) then 0 else y mod x)).
Proof. swallow1_tac. Qed.

Proposition cert_LT : nCertN 1 (
  swallow [LT];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (if decide (y < x) then -1 else 0)).
Proof. swallow1_tac. Qed.

Proposition cert_AND : nCertN 1 (
  swallow [AND];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (Vector.map2 andb x y : B64)).
Proof. swallow1_tac. Qed.

Proposition cert_OR : nCertN 1 (
  swallow [OR];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (Vector.map2 orb x y : B64)).
Proof. swallow1_tac. Qed.

Proposition cert_NOT : nCertN 1 (
  swallow [NOT];;
  let* x := pop64 in
  pushZ (Vector.map negb x : B64)).
Proof. swallow1_tac. Qed.

Proposition cert_XOR : nCertN 1 (
  swallow [XOR];;
  let* x := pop64 in
  let* y := pop64 in
  pushZ (Vector.map2 xorb x y : B64)).
Proof. swallow1_tac. Qed.

Proposition cert_POW2 : nCertN 1 (
  swallow [POW2];;
  let* x := pop64 in
  pushZ (2 ^ x)).
Proof. swallow1_tac. Qed.

(******************)

Proposition cert_READ_FRAME : nCertN 1 (
  swallow [READ_FRAME];;
  let* i := pop64 in
  let* pair := readFrame i in
  pushZ (fst pair);;
  pushZ (snd pair)).
Proof. swallow1_tac. rewrite readFrame_spec. crush. Qed.

Proposition cert_READ_PIXEL : nCertN 1 (
  swallow [READ_PIXEL];;
  let* y := pop64 in
  let* x := pop64 in
  let* c := readPixel x y in
  pushZ c).
Proof. swallow1_tac. Qed.

Proposition cert_NEW_FRAME : nCertN 1 (
  swallow [NEW_FRAME];;
  let* r := pop64 in
  let* h := pop64 in
  let* w := pop64 in
  newFrame w h r).
Proof. swallow1_tac. Qed.

Proposition cert_SET_PIXEL : nCertN 1 (
  swallow [SET_PIXEL];;
  let* b := pop64 in
  let* g := pop64 in
  let* r := pop64 in
  let* y := pop64 in
  let* x := pop64 in
  setPixel x y (r, g, b)).
Proof. swallow1_tac. Qed.

Proposition cert_ADD_SAMPLE : nCertN 1 (
  swallow [ADD_SAMPLE];;
  let* r := pop64 in
  let* l := pop64 in
  addSample (toB16 l) (toB16 r)).
Proof. swallow1_tac. rewrite addSample_spec. crush. Qed.

Proposition cert_PUT_CHAR : nCertN 1 (
  swallow [PUT_CHAR];;
  let* c := pop64 in
  putChar (toB32 c)).
Proof. swallow1_tac. rewrite putChar_spec. crush. Qed.

Proposition cert_PUT_BYTE : nCertN 1 (
  swallow [PUT_BYTE];;
  let* b := pop64 in
  putByte (toB8 b)).
Proof. swallow1_tac. rewrite putByte_spec. crush. Qed.

(********************)

Ltac cert_operand_tac :=
  apply swallow_step_lemma_N; [ lia | ];
  simp nSteps;
  apply (bind_propr _ _ _); [ | crush ];
  apply swallow_lemma;
  binary_simpl_tac.

  Proposition cert_JZ_FWD o : nCertN 1 (
    swallow [JZ_FWD; o];;
    let* x := pop64 in
    (if (decide (x = 0 :> Z))
     then
       let* pc := get' PC in
       put' PC (offset (toB8 o) pc)
     else
       ret tt)).
  Proof. cert_operand_tac. crush. Qed.

  Proposition cert_JZ_BACK o : nCertN 1 (
    swallow [JZ_BACK; o];;
    let* x := pop64 in
    (if (decide (x = 0 :> Z))
     then
       let* pc := get' PC in
       put' PC (offset (-(1 + toB8 o)) pc)
       else
       ret tt)).
  Proof. cert_operand_tac. crush. Qed.

(*************************)

Ltac cert_push_tac :=
  cert_operand_tac;
  apply pushZ_propr.

Definition zVecToZ {n} (u : vector Z n) : Z :=
  Vector.map toB8 u : Bytes n.

Proposition cert_PUSH1 (u: vector Z 1) : nCertN 1 (
  swallow (PUSH1 :: u);;
  pushZ (zVecToZ u)
).
Proof. cert_push_tac. Qed.

Corollary cert_PUSH1' x : nCertN 1 (
  swallow [PUSH1; x];;
  pushZ (toB8 x)
).
Proof. apply (cert_PUSH1 [x]). Qed.

Proposition cert_PUSH2 (u: vector Z 2) : nCertN 1 (
  swallow (PUSH2 :: u);;
  pushZ (zVecToZ u)
).
Proof. cert_push_tac. Qed.

Proposition cert_PUSH4 (u: vector Z 4) : nCertN 1 (
  swallow (PUSH4 :: u);;
  pushZ (zVecToZ u)
).
Proof. cert_push_tac. Qed.

Proposition cert_PUSH8 (u: vector Z 8) : nCertN 1 (
  swallow (PUSH8 :: u);;
  pushZ (zVecToZ u)
).
Proof. cert_push_tac. Qed.

(******************************************)

Proposition Nat2N_inj_pow (m n : nat) : (m ^ n)%nat = (m ^ n)%N :> N.
Proof.
  induction n; [ reflexivity | ].
  rewrite
    Nnat.Nat2N.inj_succ,
    N.pow_succ_r',
    Nat.pow_succ_r',
    Nnat.Nat2N.inj_mul,
    IHn.
  reflexivity.
Qed.

Proposition inj_succ (n: nat) : S n = Z.succ n :> Z.
Proof.
  now rewrite Nnat.Nat2N.inj_succ, N2Z.inj_succ.
Qed.

Proposition Nat2N_inj_lt (m n: nat): (m < n)%N <-> (m < n)%nat.
Proof.
  setoid_rewrite N2Z.inj_lt.
  setoid_rewrite nat_N_Z.
  symmetry.
  apply Nat2Z.inj_lt.
Qed.

Definition isPow2 (z:Z) : Prop := exists (n: nat), z = 2 ^ n.

Proposition isPow2_spec z : isPow2 z <-> exists (n: nat), z = (2 ^ n)%nat.
Proof.
  unfold isPow2.
  change 2 with (Z.of_N (N.of_nat 2)).
  setoid_rewrite <- N2Z.inj_pow.
  setoid_rewrite Nat2N_inj_pow.
  reflexivity.
Qed.

Proposition isPow2_spec' z :
  isPow2 z <-> 0 < z /\ exists (y: nat), (y < Z.to_nat z)%nat /\ z = 2 ^ y.
Proof.
  split.
  - intros [n H].
    subst z.
    split; [ apply pow2_pos | ].
    exists n.
    split; [ | reflexivity ].
    rewrite <- Z_N_nat.
    change 2 with (Z.of_N (N.of_nat 2)).
    rewrite <- N2Z.inj_pow.
    rewrite <- Nat2N_inj_pow.
    rewrite N2Z.id.
    rewrite Nnat.Nat2N.id.
    apply Nat.pow_gt_lin_r.
    lia.

  - intros [H0 [n [Hn Hz]]].
    exists n.
    exact Hz.
Qed.

Instance isPow2_decidable z : Decidable (isPow2 z).
Proof.
  exact (decidable_proper (isPow2_spec' z)).
Defined.

Definition toBytes' n z : vector Z n :=
  Vector.map Z.of_N (Vector.map bitsToN (toBytes n z)).

Proposition toBytes'_spec n z i : Vector.nth (toBytes' n z) i = Vector.nth (toBytes n z) i.
Proof.
  unfold toBytes'.
  now do 2 rewrite (nth_map _ _ i i eq_refl).
Qed.

(* TODO: Move to Binary.v *)
Corollary bytesToBits_injective {n} {u v: Bytes n} (H: bytesToBits u = bytesToBits v) : u = v.
Proof.
  apply (f_equal bitsToBytes) in H.
  setoid_rewrite bitsToBytes_bytesToBits in H.
  exact H.
Qed.

(* TODO: Move to Binary.v *)
Corollary bitsToN_injective {n} {u v: Bits n} (H: bitsToN u = bitsToN v) : u = v.
Proof.
  Set Printing Coercions.
  apply (f_equal Z.of_N) in H.
  apply (f_equal (toBits n)) in H.
  setoid_rewrite toBits_ofN_bitsToN in H.
  exact H.
Qed.

(* See also N2Z.inj *)

Proposition toBytes_eq {n x y} (H: cong (n * 8) x y) : toBytes n x = toBytes n y.
Proof.
  apply bytesToBits_injective.
  setoid_rewrite bytesToBits_bitsToBytes.
  apply toBits_cong.
  exact H.
Qed.


(**********************)

Open Scope DSet.

(* TODO *)
Proposition nAfter_nonempty n a :
  nAfter (S n) a = (nAfter n a) ∪ !{ offset n a }.
Proof.
  apply extensionality. intros x.
  unfold nAfter, singleton, union.
  repeat setoid_rewrite def_spec.
  split.
  - intros [i [Hi Hx]].
    by_lia (i < n \/ i = n) as Hor.
    destruct Hor as [Hor|Hor].
    + left. exists i. intuition.
    + right. subst i. exact Hx.
  - intros [[i [Hi Hx]] | Hor].
    + exists i. split; [lia | exact Hx].
    + exists n. split; [lia | exact Hor].
Qed.

Proposition disjoint_union_spec X (u v w: DSet X) :
  u # v ∪ w <-> u # v /\ u # w.
Proof.
  unfold disjoint.
  setoid_rewrite union_spec.
  intuition.
  apply (H0 x). (* TODO *)
  intuition.
Qed.

Proposition disjoint_not_member' u x : u # !{x} <-> ~ x ∈ u.
Proof.
  split; intros H.
  - apply disjoint_not_member.
    apply disjoint_symmetric.
    exact H.
  - apply disjoint_symmetric.
    apply disjoint_not_member.
    exact H.
Qed.

Corollary disjoint_nAfter_nonempty u n a :
  u # nAfter (S n) a <-> u # nAfter n a /\ ~ offset n a ∈ u.
Proof.
  rewrite nAfter_nonempty.
  rewrite disjoint_union_spec.
  setoid_rewrite disjoint_not_member'.
  tauto.
Qed.

(********************************)
(** The following holds in the initial smonad, see MonoExtras.v. *)

Parameter err_less_eq :
  forall {X} {RX: Rel X} (mx: M X) (Hmx: mx ⊑ err), mx = err.

Parameter RM_transitive :
  forall X (RX: Rel X) (RXT: Transitive RX),
    Transitive (RM X RX).

Parameter RM_antisymmetric :
  forall X (RX: Rel X) (RXT: Antisymmetric X eq RX),
    Antisymmetric (M X) eq (RM X RX).

Existing Instance RM_transitive.
Existing Instance RM_antisymmetric.

(**************************)

Section restriction_section.

  Context {A : Type} {F : A -> Type}.

  Proposition fullLens_is_all : @fullLens A F ≃ sndMixer.
  Proof. easy. Qed.

  Proposition emptyLens_is_void : @restrLens A F ∅ ≃ fstMixer.
  Proof. intros f g. now extensionality a. Qed.

End restriction_section.

Proposition fstMixer_composite {S A} (LA: Lens S A) : compositeMixer fstMixer LA ≃ fstMixer.
Proof.
  intros x y. cbn. apply update_proj.
Qed.

Proposition sndMixer_composite {S A} (LA: Lens S A) : compositeMixer sndMixer LA ≃ LA.
Proof.
  intros x y. reflexivity.
Qed.

(************************)

Proposition emptyMem_is_void : MEM' ∅ ≃ fstMixer.
Proof.
  unfold MEM'.
  rewrite composite_compositeMixer, emptyLens_is_void.
  apply fstMixer_composite.
Qed.

Proposition put_void {A} (LA: Lens State A) (H: (LA|fstMixer)) a : put' LA a = ret tt.
Proof.
  unfold Submixer in H. cbn in H.
  rewrite put_spec. cbn.
  enough (forall s, update s a = s) as Hu.
  - setoid_rewrite Hu. smon_rewrite.
  - intros s. specialize (H s s (update s a)).
    revert H. lens_rewrite. tauto.
Qed.

Corollary put_empty f : put' (MEM' ∅) f = ret tt.
Proof.
  apply put_void.
  clear f.
  rewrite emptyMem_is_void.
  reflexivity.
Qed.

(* TODO: Move to StateRel.v ? *)
Instance update_MEM_propR : PropR (@update _ _ MEM).
Proof.
  crush.
  srel_destruct Hst.
  unfold rel, state_relation, lens_relation, and_relation.
  lens_rewrite.
  repeat split; assumption.
Qed.

(******)

(* TODO: Useful? *)
Notation assume' P := (if decide P then ret tt else err).

(* TODO: Move *)
Proposition simplify_assume P {DP: Decidable P} {X} (mx: M X) :
  assume P;; mx = assume' P;; mx.
Proof.
  destruct (decide P); smon_rewrite.
Qed.

Proposition assume_bind P {DP: Decidable P} {X} (f: P -> M X) :
  let* H := assume P
  in f H =
    match decide P with
    | left H => f H
    | right _ => err
    end.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

Corollary assume_bind' P {DP: Decidable P} {X} (mx: M X) :
  assume P;; mx = if decide P then mx else err.
Proof.
  apply assume_bind.
Qed.

(******)

Section assume_rel_section.

  Proposition assume_eq
    P {DP: Decidable P} {X} (f g: P -> M X)
    (H : forall (p:P), f p = g p) :
      let* p := assume P in f p =
      let* p := assume P in g p.
  Proof.
    destruct (decide P) as [p|_]; smon_rewrite.
    apply H.
  Qed.

  Ltac assume_rel_tac P H :=
    destruct (decide P) as [p|_];
    smon_rewrite;
    [ apply H
    | crush ].

  Proposition assume_rel
    P {DP: Decidable P} {X} (f g: P -> M X)
    (H : forall (p:P), f p ⊑ g p) :
      let* p := assume P in f p ⊑
      let* p := assume P in g p.
  Proof. assume_rel_tac P H. Qed.

  Proposition assume_rel'
    P {DP: Decidable P} {X} (f: P -> M X) (mx: M X)
    (H : forall (p:P), f p ⊑ mx) :
      let* p := assume P in f p ⊑ mx.
  Proof. assume_rel_tac P H. Qed.

End assume_rel_section.

Proposition confined'
  {mix: Mixer State} {mx: M unit} (Cmx: Confined mix mx)
  (my: M unit) {Hmy: Neutral mix my} :
my;; mx = mx;; my.
Proof.
enough (my;; mx;; ret tt = mx;; my;; ret tt) as HH.
- revert HH. smon_rewrite. tauto.
- rewrite Cmx.
  + reflexivity.
  + typeclasses eauto.
Qed.

Instance confined_swallow' pc {n} (ops: vector Z n) :
  Confined (MEM' (nAfter n pc) * PC) (
    put' PC pc;;
    swallow ops
  ).
Proof.
  rewrite swallow_spec, lens_put_get.
  typeclasses eauto.
Qed.

(************************)

(** ** Mark memory as undefined *)
Definition wipe (u: DSet Addr) : M unit :=
  put' (MEM' u) (fun _ _ _ => None).

Goal forall u, Confined (MEM' u) (wipe u).
  typeclasses eauto.
Qed.

Proposition wipe_empty : wipe ∅ = ret tt.
Proof. apply put_empty. Qed.

Proposition wipe_mono u v (H: u ⊆ v) : wipe v ⊑ wipe u.
Proof.
  unfold wipe. do 2 rewrite put_spec. cbn.
  unfold restr. crush.
  apply update_MEM_propR; [ exact Hst | ]. crush.
  specialize (H a). cbv. cbv in H.
  destruct (v a) eqn:Hva; [ exact I | ].
  destruct (u a) eqn:Hua.
  - exfalso. exact (H I).
  - srel_destruct Hst.
    apply Hst_mem.
Qed.

Corollary wipe_less u : wipe u ⊑ ret tt.
Proof.
  (* This is also provable without assuming RM_transitive. *)
  transitivity (wipe ∅).
  - apply wipe_mono. apply empty_initial.
  - rewrite wipe_empty. crush.
Qed.

Instance confined_wipe u : Confined (MEM' u) (wipe u).
Proof.
  typeclasses eauto.
Qed.

(* TODO: Probably not safe to define as an instance. *)
Lemma disjoint_independent' u v (H: u # v) : Independent (MEM' u) (MEM' v).
Proof.
  unfold MEM'.
  apply
    composite_independent_r,
    separate_independent. (* TODO: Rename and move. *)
  exact H.
Qed.

(***********)

Lemma wipe_swallow_reordering'
    u {n} (ops: vector Z n) pc (Hdis: u # nAfter n pc) :
  put' PC pc;;
  wipe u;;
  swallow ops =
    put' PC pc;;
    swallow ops;;
    wipe u.
Proof.
  setoid_rewrite confined_wipe; [ | typeclasses eauto .. ].
  setoid_rewrite <- bind_assoc at 2.

  setoid_rewrite (confined' (confined_wipe u)); [ reflexivity | ].
  unshelve eapply (confined_neutral (m:= MEM' (nAfter n pc) * PC ));
    try typeclasses eauto.

  apply independent_forward.
  setoid_rewrite prodLens_prodMixer.
  apply independent_prod.
  - apply disjoint_independent'.
    apply disjoint_symmetric. (* TODO: make global? *)
    exact Hdis.
  - apply independent_symmetric.
    typeclasses eauto.
Qed.

Corollary wipe_swallow_reordering u {n} (ops: vector Z n) :
  let* pc := get' PC in
  assume (u # nAfter n pc);;
  wipe u;;
  swallow ops =
    let* pc := get' PC in
    assume (u # nAfter n pc);;
    swallow ops;;
    wipe u.
Proof.
  smon_ext' PC pc.
  setoid_rewrite lens_put_get.
  setoid_rewrite <- confined_put; [ | typeclasses eauto .. ].
  apply assume_eq, wipe_swallow_reordering'.
Qed.

Arguments proj {_ _} _ _.
Arguments update {_ _} _ _ _.

(* TODO: Don't we have this already? Safe as global? *)
#[refine]
Instance sublensFactor
  {A X Y} {LX: Lens A X} {LY: Lens A Y}
  (HS: (LX|LY)) (a:A) : Lens Y X :=
{
  proj y := proj LX (update LY a y);
  update y x := proj LY (update LX (update LY a y) x);
}.
Proof.
  - intros y x. lens_rewrite.
    specialize (HS a (update LY a y) (update LX a x)).
    revert HS. cbn. lens_rewrite.
    intros HS. rewrite <- HS. lens_rewrite.
  - intros y.
    specialize (HS a (update LY a y) (update LY a y)).
    revert HS. cbn. lens_rewrite.
  - intros y x x'.
    specialize (HS
      (update LY a y)
      (update LX (update LY a y) x)
      (update LX a x')).
    cbn in HS. revert HS. lens_rewrite.
    intros HS. rewrite HS. lens_rewrite.
Defined.

Lemma sublensFactor_spec
  {A X Y} {LX: Lens A X} {LY: Lens A Y}
  (HS: (LX|LY)) (a:A) : sublensFactor HS a ∘ LY ≅ LX.
Proof.
  intros b x. cbn. unfold compose.
  remember (HS a b (update LX a x)) as HH eqn:HHe; clear HHe.
  revert HH. cbn. lens_rewrite. intros HH.
  rewrite HH. clear HH. lens_rewrite.
  specialize (HS b b (update LX b x)).
  revert HS. cbn. lens_rewrite. congruence.
Qed.

Arguments proj {_ _ _} _.
Arguments update {_ _ _} _ _.

(****)

Proposition sub_put_get {A B} (LA: Lens State A) (LB: Lens A B) a :
  put' LA a;;
  get' (LB ∘ LA) =
    put' LA a;;
    ret (proj a).
Proof.
  rewrite put_spec, get_spec.
  cbn. smon_rewrite'.
Qed.

Proposition mem_point_sub {a u} (Ha: a ∈ u) :
  (MEM'' a | MEM' u).
Proof.
  unfold MEM', MEM''.
  apply sublens_comp, pointLens_sublens.
  exact Ha.
Qed.

(* TODO*)
Existing Instance compositeLens_proper.

Lemma mem_put_get'' {a u} (Ha: a ∈ u) f :
  put' (MEM' u) f;;
  get' (MEM'' a) =
    put' (MEM' u) f;;
    ret (f a Ha).
Proof.
  unfold MEM', MEM''.
  set (PL := pointLens _).
  set (RL := restrLens _).
  assert (PL|RL) as H;
  [ apply pointLens_sublens; exact Ha | ].
  setoid_rewrite <- (sublensFactor_spec H (fun _ _ => None)).
  setoid_rewrite <- compositeLens_associative.
  setoid_rewrite sub_put_get. f_equal.
  extensionality x. destruct x. f_equal.
  cbn. decided Ha. reflexivity.
Qed.

Proposition rel_extensional'
  {A} (LA: Lens State A)
  {RA: Rel A} {Hg: @PropR _ (RM A RA) (get' LA)}
  {X} {RX: Rel X}
  (mx mx': M X)
  (H: forall a a', a ⊑ a' -> put' LA a;; mx ⊑ put' LA a';; mx') :
  mx ⊑ mx'.
Proof.
  enough (
    let* a := get' LA in put' LA a;; ret tt;; mx ⊑
    let* a' := get' LA in put' LA a';; ret tt;; mx') as HHH.
  - revert HHH. smon_rewrite. tauto.
  - setoid_rewrite ret_tt_bind.
    apply (
      bind_propr State M _ _ _ _ Hg
      (fun a => put' LA a;; mx)
      (fun a' => put' LA a';; mx') H).
Qed.

(*****)

Proposition wipe_load {u a} (Ha: a ∈ u) : wipe u;; load a = err.
Proof.
  unfold wipe.
  rewrite load_spec''.
  setoid_rewrite confined_get; [ | typeclasses eauto ].
  smon_rewrite.
  rewrite <- bind_assoc.
  rewrite mem_put_get''.
  - smon_rewrite.
  - exact Ha.
Qed.

Proposition put_to_get
    {A} (LA: Lens State A)
    {X} (f g: A -> M X)
    (H: forall a,
      put' LA a;; f a =
      put' LA a;; g a) :
  let* a := get' LA in f a =
  let* a := get' LA in g a.
Proof.
  smon_ext' LA a.
  setoid_rewrite lens_put_get.
  exact (H a).
Qed.

Proposition put_to_get'
    {A} (LA: Lens State A)
    {RA: Rel A} {Hg: @PropR _ (RM A RA) (get' LA)}
    {X} (f g: A -> M X)
    (H: forall a a', a ⊑ a' ->
      put' LA a;; f a ⊑
      put' LA a';; g a') :
  let* a := get' LA in f a ⊑
  let* a' := get' LA in g a'.
Proof.
  apply (rel_extensional' LA). intros a a' Ha.
  setoid_rewrite lens_put_get. apply H. exact Ha.
Qed.

(****)

Proposition rel_assume
    {X} (mx: M X) {RX: Rel X} {Hmx: PropR mx}
    (P: X -> Prop) {HP: forall x, Decidable (P x)}
    {Y} (f: X -> M Y) {RY: Rel Y} (HRY: Reflexive RY) {Hf: PropR f} :
  let* x := mx in
  assume' (P x);;
  f x ⊑
    let* x := mx in
    f x.
Proof.
  apply bind_propr'.
  - exact Hmx.
  - crush. apply Hf. exact Hxy.
Qed.

(*************************)

Proposition load_mx a {X} {RX: Rel X} {mx mx': M X} (Hmx: mx ⊑ mx') :
  load a;; mx ⊑ mx'.
Proof.
  rewrite load_spec.
  destruct (decide _) as [Ha|_]; smon_rewrite; [ | crush ].
  rewrite extr_spec.
  apply (rel_extensional' MEM).
  intros mem mem' Hm.
  rewrite lens_put_get.
  destruct (mem a Ha) as [H|]; smon_rewrite; crush.
  apply Hm.
  exact Hmx.
Qed.

Proposition loadMany_mx
    n a {X} {RX: Rel X} {TX: Transitive RX}
    (mx: M X) {Hmx: mx ⊑ mx} :
  loadMany n a;; mx ⊑ mx.
Proof.
  revert a.
  induction n; intros a; simp loadMany; smon_rewrite; crush; [ exact Hmx | ].
  transitivity (load a;; mx).
  - apply bind_propr'.
    + apply load_propr.
    + crush. apply IHn.
  - apply load_mx. exact Hmx.
Qed.

(****)

Proposition swallow_n {n} (ops: vector Z n) :
  swallow ops ⊑
    let* pc := get' PC in
    put' PC (offset n pc).
Proof.
  rewrite swallow_spec.
  apply (@put_to_get' _ _ eq_relation getPc_propr).
  intros a a' Ha. destruct Ha.
  apply (rel_extensional' MEM). intros mem mem' Hm.

  setoid_rewrite simplify_assume.
  setoid_rewrite confined_put.
  2,3:
    apply (confined_neutral (m:=MEM)); (* TODO *)
    typeclasses eauto.

  transitivity (
    put' PC a;;
    put' MEM mem;;
    let* u := loadMany n a in
    put' PC (offset n a)).

  - apply bind_propr'.
    + apply putPc_propr. reflexivity.
    + crush.

  - apply bind_propr'.
    + apply putPc_propr. reflexivity.
    + crush.
      * apply Hm.
      * apply loadMany_mx.
        -- typeclasses eauto.
        -- apply putPc_propr. reflexivity.
Qed.

(***********)

Proposition wipe_swallow_precondition u {n} (ops: vector Z n) :
  wipe u;;
  swallow ops = let* pc := get' PC in
                assume (u # nAfter n pc);;
                wipe u;;
                swallow ops.
Proof.
  induction ops using vec_rev_ind.
  {
    simp_assume.
    smon_ext s.
    unfold Addr.
    rewrite get_spec.
    smon_rewrite.
    apply bind_extensional. intros [].
    rewrite decide_true.
    - reflexivity.
    - now rewrite nAfter_empty.
  }
  simp swallow.
  rewrite <- bind_assoc.
  rewrite IHops at 1. clear IHops.
  rewrite bind_assoc.
  smon_ext' PC pc.
  repeat rewrite lens_put_get.

  destruct (decide (u # nAfter (S n) pc)) as [Hd'|Hd'].
  {
    setoid_rewrite ret_bind.
    repeat setoid_rewrite bind_assoc.
    rewrite nAfter_nonempty in Hd'.
    apply disjoint_union_spec in Hd'.
    destruct Hd' as [Hd0 Hd1].

    destruct (decide (u # nAfter n pc)) as [He0|He1];
    [ | contradict He1; exact Hd0 ].
    rewrite ret_bind.
    reflexivity.
  }

  destruct (decide (u # nAfter n pc)) as [Hd''|Hd''].
  {
    smon_rewrite.
    setoid_rewrite disjoint_nAfter_nonempty in Hd'.
    assert (offset n pc ∈ u) as Hn; [ apply decidable_raa; intuition idtac | ].

    setoid_rewrite <- bind_assoc at 2.
    setoid_rewrite <- bind_assoc at 1.
    rewrite wipe_swallow_reordering'; [ | exact Hd'' ].
    setoid_rewrite -> bind_assoc at 1.
    setoid_rewrite -> bind_assoc at 1.

    apply err_less_eq.
    setoid_rewrite simplify_assume.
    transitivity (
      put' PC pc;;
      (let* pc := get' PC in
      put' PC (offset n pc));;
      wipe u;;
      let* x3 := get' PC in
      let* x4 := load x3 in
      assume' (x4 = toB8 x);;
      put' PC (offset 1 x3)
    ).
    - apply bind_propr'; [ apply putPc_propr; reflexivity | ].
      intros [] [] _. apply bind_propr'; [ apply swallow_n | ].
      intros [] [] _. crush. unfold wipe.

      rewrite (put_spec (MEM' u)).
      cbn.
      unfold compose.
      crush.
      unfold rel, state_relation, and_relation, lens_relation.
      lens_rewrite.
      srel_destruct Hst.
      repeat split; try assumption.
      setoid_rewrite proj_update.
      crush.
      destruct (decide (a ∈ u)); [ crush | ].
      apply Hst_mem.

    - setoid_rewrite bind_assoc.
      rewrite lens_put_get.
      rewrite lens_put_put.
      setoid_rewrite confined_get.
      rewrite lens_put_get.
      setoid_rewrite <- bind_assoc at 2.
      assert (wipe u;; load (offset n pc) = err) as H.
      + apply wipe_load. exact Hn.
      + setoid_rewrite H.
        smon_rewrite. crush.
      + apply (confined_neutral _ (m:=MEM)).
  }
  smon_rewrite.
Qed.
