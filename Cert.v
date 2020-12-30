From iVM Require Import DSet Mono Cert0 Cert1.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(******************************)

(******************************)

(** Optimized implementation *)
Definition pushCode (z: Z) : list Z :=
  let x := z mod 2 ^ 64 in
  let y := (-1 - z) mod 2 ^ 64 in
  if decide (x = 0) then [PUSH0]
  else if decide (y = 0) then [PUSH0; NOT]
  else if decide (x < 2 ^ 8) then [PUSH1; x]
  else if decide (y < 2 ^ 8) then [PUSH1; x; NOT]
  else if decide (x < 2 ^ 16) then [PUSH2] ++ toBytes' 2 x
  else if decide (isPow2 x) then [PUSH1; Z.log2 x; POW2]
  else if decide (y < 2 ^ 16) then [PUSH2] ++ toBytes' 2 y ++ [NOT]
  else if decide (isPow2 y) then [PUSH1; Z.log2 y; POW2; NOT]
  else if decide (x < 2 ^ 32) then [PUSH4] ++ toBytes' 4 x
  else if decide (y < 2 ^ 32) then [PUSH4] ++ toBytes' 4 y ++ [NOT]
  else [PUSH8] ++ toBytes' 8 x.

Definition pushCode_steps (z: Z) : nat :=
  let x := z mod 2 ^ 64 in
  let y := (-1 - z) mod 2 ^ 64 in
  if decide (x = 0) then 1
  else if decide (y = 0) then 2
  else if decide (x < 2 ^ 8) then 1
  else if decide (y < 2 ^ 8) then 2
  else if decide (x < 2 ^ 16) then 1
  else if decide (isPow2 x) then 2
  else if decide (y < 2 ^ 16) then 2
  else if decide (isPow2 y) then 3
  else if decide (x < 2 ^ 32) then 1
  else if decide (y < 2 ^ 32) then 2
  else 1.

Lemma cert_pushCode z : nCertN (pushCode_steps z) (
  wipeStack 1;;
  swallow (of_list (pushCode z));;
  pushZ z
).
Proof.
  unfold pushCode, pushCode_steps.
  set (x := z mod 2 ^ 64).
  set (y := (-1 - z) mod 2 ^ 64).

  destruct (decide (x = 0)) as [H0|_].
  {
    subst x.
    assert (pushZ z = pushZ 0) as H.
    - unfold pushZ. do 2 f_equal. apply toBytes_eq. exact H0.
    - rewrite H.
      unshelve eapply (wipeStack_nCertN _ cert_PUSH0 1).
      crush. apply swallow_propr.
  }
  destruct (decide (y = 0)) as [H1|_].
  {
    subst y.
    simpl of_list.
    unfold nCertN, nCert, wipeStack.
    repeat rewrite bind_assoc.
    setoid_rewrite <- bind_assoc at 2.
    apply (rel_extensional' SP). intros sp sp' Hsp. destruct Hsp.
    rewrite lens_put_get.

    transitivity (
      put' SP sp;;
      (
        let* pc := get' PC in
        assume' (nBefore 8 sp # nAfter 2 pc);;
        swallow [8; 42] );;
      pushZ z;;
      ret true
    ).
    apply bind_propr'.
    - apply putSp_propr. reflexivity.
    - intros _ _ _.
      apply bind_propr'.
      * apply wipe_swallow_precondition'.
      * crush.
    - repeat setoid_rewrite bind_assoc.
      apply (rel_extensional' PC). intros pc pc' Hpc. destruct Hpc.
      setoid_rewrite <- confined_put; [ | typeclasses eauto .. ].

      setoid_rewrite lens_put_get.
      rewrite <- simplify_assume.
      do 2 setoid_rewrite <- postpone_assume.
      apply assume_rel'. intros H.
      rewrite swallow_spec.
      setoid_rewrite simplify_assume.

      Opaque loadMany. (* TODO *)
      repeat setoid_rewrite bind_assoc.
      setoid_rewrite lens_put_get.

      apply (rel_extensional' (MEM' (nAfter 2 pc))).
      intros f g Hfg.

      setoid_rewrite confined_loadMany.
      setoid_rewrite confined_loadMany.
      2,3 : typeclasses eauto.


      setoid_rewrite confined_loadMany.








    intros y y' Hy.

    idtac.

    setoid_rewrite (wipe_swallow_precondition' (nBefore 8 a)).
    transitivity

    unfold wipeStack.
    rewrite bind_assoc.
    setoid_rewrite <- bind_assoc at 2.
    setoid_rewrite wipe_swallow_precondition.
    repeat setoid_rewrite bind_assoc.
    setoid_rewrite simplify_assume.

    unfold nCertN.
    rewrite bind_assoc.
    apply swallow_step_lemma; [ easy | ].
    simp oneStep'.

  }








(*************************************************)



Definition stdDis m n o :=
  let* sp := get' SP in
  let* pc := get' PC in
  assume (nBefore (m * 8) sp # nAfter o pc);;
  assume (nAfter (n * 8) sp # nAfter o pc);;
  ret tt.



(* TODO: Move *)

(** In VectorSpec.v: [shiftin_last] *)



(* ----------------------------------- *)




(* ----------------------------------- *)


    setoid_rewrite nAfter_empty.
    unfold nAfter.


setoid_rewrite nAfter_spec.

  smon_ext s. rewrite get_spec. smon_rewrite. apply bind_extensional. intros [].
  set (pc := proj _).
  destruct (decide _) as [H|H]; smon_rewrite.
    apply not_nAfter_disjoint_evidence in H.
  destruct H as [x [Hx [i [Hi Ho]]]];
    subst x.



Proposition stdStart_stdDis m n {o} (ops: vector Z o) :
  stdDis m n o;; stdStart m n ops = stdStart m n ops.
Proof.
  unfold stdDis, stdStart.
  smon_ext s.
  setoid_rewrite get_spec.
  repeat setoid_rewrite bind_assoc.
  smon_rewrite.

  destruct (decide (nBefore _ _ # _)) as [H0|H];
    [ destruct (decide (nAfter _ _ # _)) as [H0'|H] | ];
    [ smon_rewrite | | ];
    apply not_nAfter_disjoint_evidence in H;
    destruct H as [x [Hx [i [Hi Ho]]]];
    subst x.

  - setoid_rewrite popN_spec.
    setoid_rewrite popMany_spec.
    smon_rewrite.

    setoid_rewrite <- (confined_loadMany _ _ _ _ _).
    setoid_rewrite get_spec at 1.
    smon_rewrite.

    set (sp := (@proj _ _ SP s)).
    set (pc := (@proj _ _ PC s)).
    set (sp' := (toB64 ((n * 8)%nat + sp))).

    do 2 (setoid_rewrite <- (confined_put SP sp');
          (* TODO: Why is this needed? *)
          [ | apply (confined_neutral (Hm:=independent_MEM_SP));
              typeclasses eauto ] ).

    setoid_rewrite <- (confined_put SP sp');
      [ | apply (confined_neutral (m := MEM * PC)); typeclasses eauto ].


          (* TODO: Why is this needed? *)
          [ | apply (confined_neutral (Hm:=independent_MEM_SP));
              typeclasses eauto ] ).

          setoid_rewrite <- (confined_put SP sp');
      (* TODO: Why is this needed? *)
      [ | apply (confined_neutral (Hm:=independent_MEM_SP));
          typeclasses eauto ].

    admit.


    setoid_rewrite get_spec.
    setoid_rewrite get_spec.



unfold wipe.


  smon_rewrite.



(** ** Zero check *)

(* TODO: Move / remove *)
Definition inc' L z :=
  let* a := get' L in
  put' L (offset z a).

Definition code_isZero := [PUSH1; 1; LT].

(* TODO *)
Opaque pushZ.

Lemma ncert_isZero :
  nCert 2 (let* v := stdStart 1 1 code_isZero in
           pushZ (if decide (Vector.hd v = 0 :> Z) then -1 else 0);;
           not_terminated).
Proof.
  unfold nCert;
    simp nSteps;
    unfold stdStart, chain, oneStep;
    setoid_rewrite chain_true.
  (* TODO: smon_rewrite is too slow. *)
  repeat setoid_rewrite bind_assoc.
  simpl nBefore.



  apply swallow_lemma.
  unfold code_isZero.




let* x := pop64 in
           wipeStack 2;;
           swallow code_isZero;;
           pushZ (if decide (x = 0 :> Z) then -1 else 0);;
           not_terminated}.
Proof.
  unfold nCert, code_isZero.
  simp nSteps.
  setoid_rewrite chain_true.
  unfold chain.

Lemma ncert_isZero :
  nCert 2 (let* x := pop64 in
           wipeStack 2;;
           swallow code_isZero;;
           pushZ (if decide (x = 0 :> Z) then -1 else 0);;
           not_terminated).
Proof.
  unfold nCert, code_isZero.
  simp nSteps.
  setoid_rewrite chain_true.
  unfold chain.




(** ** ??? *)

(* TODO: Rename? Move up? *)
Definition uphold (u: M bool) : M unit :=
  let* cont := u in
  assert* cont in
  ret tt.

Lemma uphold_chain
      {u u' v v': M bool} (Hu: u ⊑ u') (Hv: v ⊑ v') : uphold u;; v ⊑ chain u' v'.
Proof.
  unfold uphold, chain.
  rewrite bind_assoc.
  apply (bind_propr _ _ _).
  - exact Hu.
  - crush.
    destruct y; cbn; smon_rewrite.
    + exact Hv.
    + apply (err_least _).
Qed.

(* TODO *)
Context
  (TB: Transitive (@rel (M bool) _))
  (TU: Transitive (@rel (M unit) _))
.

Lemma uphold_lemma (u v w: M bool) :
  u;; not_terminated ⊑ uphold v;; w ->
  u;; not_terminated ⊑ chain v w.
Proof.
  (* This would have been easier with transitivity. *)
  unfold uphold, chain.
  intros H.



  setoid_rewrite assert_bind.







Lemma chain_prime u v : chain' u v ⊑ chain u v.



  -> m1;; not_terminated ⊑ chain v1 v2





  rewrite swallow_lemma.









(** To be continued.
It seems possible that we will need an extra axiom at some,
ensuring that [⊑] is transitive on [M bool], but we'll see. *)
