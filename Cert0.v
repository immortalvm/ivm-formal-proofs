(** The contents of this file will be either integrated with Cert.v or moved elsewhere. *)

From iVM Require Import DSet Mono.
Import DSetNotations.

Unset Suggest Proof Using.

Open Scope vector.

(* TODO: Place inside section or module. *)
Import OpCodes.

(* TODO: Move? *)
Opaque next.

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
Opaque loadMany.
Opaque load.

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

Opaque Vector.map.


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

(* TODO: Move and improve name *)
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
Qed.

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
Qed.

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
Opaque bytesToLongs.


Equations popN (n: nat) : M (vector B64 n) :=
  popN 0 := ret [];
  popN (S n) := let* h := pop64 in
                let* r := popN n in
                ret (h :: r).

(* TODO: Move *)
Opaque popMany.

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
Qed.

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
Opaque bytesToBits.

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
    Opaque Vector.map.

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
