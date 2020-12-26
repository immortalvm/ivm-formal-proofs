From iVM Require Import DSet Mono Cert0.
Import DSetNotations.

Unset Suggest Proof Using.

Open Scope vector.

(* TODO: Place inside section or module. *)
Import OpCodes.

(* TODO: Move? *)
Opaque next.

Open Scope Z.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).


Definition wipeStack n :=
  let* a := get' SP in
  wipe (nBefore (n * 8) a).

Corollary wipeStack_less n : wipeStack n ⊑ ret tt.
Proof.
  unfold wipeStack.
  rewrite get_spec.
  cbn.
  rewrite bind_assoc.
  rewrite <- get_ret.
  crush.
  rewrite ret_bind.
  apply wipe_less.
Qed.

Proposition rel_ret_tt
            mu Y (my my' : M Y)
            `(mu ⊑ ret tt)
            `(my ⊑ my') : mu;; my ⊑ my'.
Proof.
  assert (my' = ret tt;; my') as HH.
  - rewrite ret_bind. reflexivity.
  - rewrite HH. crush; assumption.
Qed.

Definition w_pop64 := let* v := pop64 in
                      wipeStack 1;;
                      ret v.

Corollary wiped_pop64 : w_pop64 ⊑ pop64.
Proof.
  unfold w_pop64.
  rewrite <- bind_ret.
  crush.
  apply rel_ret_tt.
  - apply wipeStack_less.
  - crush.
Qed.


(** ** Standard cert start *)

Definition stdStart m n {o} (ops: vector Z o) : M (vector B64 n) :=
  let* v := popN n in
  wipeStack (m + n);;
  swallow ops;;
  ret v.

(** By putting [swallow] after [wipeStack] we ensure that [stdStart] fails
    if the operations overlap with (the relevant parts of) the stack. *)


(************************************)




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

Proposition wipe_swallow_precondition u {n} (ops: vector Z n) :
  wipe u;;
  swallow ops = let* pc := get' PC in
                assume (u # nAfter n pc);;
                wipe u;;
                swallow ops.
Proof.
  induction ops using vec_rev_ind.
  - simp_assume.
    smon_ext s.
    unfold Addr.
    rewrite get_spec.
    smon_rewrite.
    apply bind_extensional. intros [].
    rewrite decide_true.
    + reflexivity.
    + now rewrite nAfter_empty.

  - simp swallow.
    rewrite <- bind_assoc.
    rewrite IHops at 1.
    rewrite bind_assoc.
    smon_ext' PC pc.
    repeat rewrite lens_put_get.
    destruct (decide (u # nAfter n pc)) as [Hd|Hd].
    + destruct (decide (u # nAfter (S n) pc)) as [Hd'|Hd'].
      * smon_rewrite.
      * smon_rewrite.
        assert (offset n pc ∈ u) as Hu.
        -- clear IHops.
           apply not_nAfter_disjoint_spec in Hd'.
           destruct Hd' as [i [Hi Hu]].
           by_lia (i = n \/ i < n) as Hii.
           destruct Hii as [[]|Hii]; [exact Hu|].
           contradict Hd.
           unfold disjoint.
           intros Hd.
           apply (Hd (offset i pc)).
           split.
           ++ exact Hu.
           ++ unfold nAfter.
              rewrite def_spec.
              exists i.
              split.
              ** lia.
              ** reflexivity.
        -- rewrite swallow_spec.

(********* Continue from here *********)

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
    setoid_rewrite chain_ret_true.
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
  setoid_rewrite chain_ret_true.
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
  setoid_rewrite chain_ret_true.
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
