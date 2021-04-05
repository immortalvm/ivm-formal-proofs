(** The contents of this file will be either integrated with Cert.v or moved elsewhere. *)

From iVM Require Import DSet Mono.
Import DSetNotations.

Unset Suggest Proof Using.

Open Scope vector.

(* TODO: Place inside section or module. *)
Import OpCodes.

Open Scope Z.


(***)

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

(***)

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

Proposition id_equation_1 X (x: X) : id x = x.
Proof. reflexivity. Qed.


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
      [ | apply (confined_neutral (m':=MEM));
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
  exact (decidable_transfer (isPow2_spec' z)).
Defined.

(***)

Definition toBytes' n z : vector Z n :=
  Vector.map Z.of_N (Vector.map bitsToN (toBytes n z)).

Proposition toBytes'_spec n z i : Vector.nth (toBytes' n z) i = Vector.nth (toBytes n z) i.
Proof.
  unfold toBytes'.
  now do 2 rewrite (nth_map _ _ i i eq_refl).
Qed.

Proposition toBytes_eq {n x y} (H: cong (n * 8) x y) : toBytes n x = toBytes n y.
Proof.
  apply bytesToBits_injective.
  setoid_rewrite bytesToBits_bitsToBytes.
  apply toBits_cong.
  exact H.
Qed.


(**********************)

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

Section assume_rel_section.

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

(* TODO: Remove *)
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
  unshelve eapply (confined_neutral (m':= MEM' (nAfter n pc) * PC ));
    try typeclasses eauto.

  apply independent_backward.
  setoid_rewrite prodLens_prodMixer.
  apply independent_prod; [ | typeclasses eauto ].

  (* TODO: Why doesn't 'typeclasses eauto' solve this as well? *)
  now apply independent_backward,
            composite_independent_r,
            separate_independent.
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

(***)

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

(***)

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

(* TODO: Remove *)
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
    apply (confined_neutral (m':=MEM)); (* TODO *)
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

(* TODO: Duplicate *)
Ltac simplify_assume := setoid_rewrite simplify_assume.

Require Import Coq.Classes.Morphisms_Prop.

(* TODO: Why is this needed? *)
Instance not_proper_impl : Proper (iff ==> impl) not.
Proof.
  intros p p' Hp H. tauto.
Qed.

Proposition wipe_swallow_precondition u {n} (ops: vector Z n) :
  wipe u;;
  swallow ops = let* pc := get' PC in
                assume (u # nAfter n pc);;
                wipe u;;
                swallow ops.
Proof.
  induction ops using vec_rev_ind.
  {
    simplify_assume.
    smon_ext s.
    unfold Addr.
    rewrite get_spec.
    smon_rewrite.
    apply bind_extensional. intros [].
    rewrite decide_true.
    - now rewrite ret_tt_bind.
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
      + apply (confined_neutral _ (m':=MEM)).
  }
  smon_rewrite.
Qed.
