From iVM Require Import DSet Mono Cert0 Cert1.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(*****************)

(* TODO: Continue from here *)

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
    intros H. apply asBool_decide in H. destruct H. lia.

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

    setoid_rewrite <- (confined_popMany sp n _).
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
        apply asBool_decide in Hu, Ha.
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
    + setoid_rewrite <- (confined_popMany sp n _);
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
    + setoid_rewrite <- (confined_popMany sp n _);
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
        rewrite asBool_decide in H.
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
    + setoid_rewrite <- (confined_popMany sp n _).

    rewrite (lens_semiNeutral (sub_semiNeutral (semiNeutral_defined _) MEM)).
      smon_rewrite.
    sndMixer
    setoid_rewrite <- confined_defined.
      setoid_rewrite (confined_popMany sp n _).
      smon_rewrite.




    + now smon_rewrite01.
    + setoid_rewrite <- (confined_popMany sp n _);
      [ | eapply (confined_neutral _ (Hmx := confined_defined _)) ].






    transitivity (
      put' MEM mem;;
      let* u := (put' SP sp;; popMany n) in
      defined (toB64 (n + sp));;
      pushMany u).
    + now smon_rewrite01.
    + setoid_rewrite <- (confined_popMany sp n _);
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
