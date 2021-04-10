From iVM Require Import DSet Mono Cert0 Cert1.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(*****************)

(* TODO: Move *)
Proposition get_mem''_spec a {X} (f: (available a -> option Cell) -> M X) :
  let* x := get' (MEM'' a) in
  f x =
    let* mem := get' MEM in
    f (mem a).
Proof.
  unfold MEM''.
  setoid_rewrite get_spec.
  smon_rewrite.
Qed.

(* TODO: Move *)
Proposition pointLens_restrLens
  {A : Type} {F : A -> Type}
  {H_eqdec: EqDec A} (a : A) :
  pointLens (F:=F) a ≃ restrLens !{a}.
Proof.
  intros f g.
  cbn.
  extensionality x.
  destruct (decide (x ∈ !{a})) as [Hx|Hx].
  - rewrite singleton_spec in Hx.
    symmetry in Hx.
    decided Hx.
    destruct H.
    reflexivity.
  - rewrite singleton_spec in Hx.
    assert (a <> x) as H; [ congruence | ].
    undecided H.
    reflexivity.
Qed.

Proposition not_member_independent
  {A : Type} {F : A -> Type}
  {H_eqdec: EqDec A} (a : A) (u: DSet A) (Ha: ~ (a ∈ u)) :
  Independent (pointLens (F:=F) a) (restrLens u).
Proof.
  intros f g h.
  cbn.
  extensionality x.
  destruct (decide (x ∈ u)) as [Hxu|Hxu]; [ | reflexivity ].
  assert (a <> x) as Hax; [ congruence | ].
  now undecided Hax.
Qed.

(* TODO: Move *)
Arguments confined_neutral {_ _ _ _} _ _ {_ _} _.

Instance lens_semiNeutral
{S M} {SM: SMonad S M}
{X A} (LA: Lens S A) (mx: M X)
(Hmx: mx =
  let* a := get' LA in
  let* x := mx in
  put' LA a;;
  ret x) : SemiNeutral LA mx.
Proof.
  unfold SemiNeutral.
  rewrite -> Hmx at 1.
  rewrite get_spec, put_spec, putM_spec.
  smon_rewrite.
Qed.

Instance semiNeutral_popMany n : SemiNeutral MEM (popMany n).
Proof.
  induction n;
    apply lens_semiNeutral;
    simp popMany;
    [ smon_rewrite | ].
  setoid_rewrite (semiNeutral_get_put MEM pop).
  setoid_rewrite (semiNeutral_get_put MEM (popMany n)) at 1.
  smon_rewrite.
Qed.

Lemma popMany_pushMany n :
  let* u := popMany n in
  pushMany u =
    let* sp := get' SP in
    sDefined (nAfter n sp).
Proof.
  rewrite popMany_defined.
  rewrite sDefined_spec.
  repeat setoid_rewrite bind_assoc.
  smon_ext' SP sp.
  setoid_rewrite lens_put_get.
  setoid_rewrite (confined_get MEM);
  [ | typeclasses eauto .. ].
  smon_ext' MEM mem.
  setoid_rewrite lens_put_get.
  destruct (decide _) as [H|H];
  [ | now smon_rewrite01 ].
  smon_rewrite2.
  revert sp mem H;
    induction n;
    intros sp mem H.
  - simp popMany.
    setoid_rewrite ret_bind.
    simp to_list.
    rewrite pushMany_empty.
    now smon_rewrite2.
  - rewrite popMany_S.
    setoid_rewrite to_list_action.
    setoid_rewrite pushMany_action.
    setoid_rewrite pushMany_one.
    setoid_rewrite (collapse_bind_lift pop_push).
    setoid_rewrite bind_assoc.
    setoid_rewrite popMany_getSP.
    setoid_rewrite lens_put_get.

    rewrite defined_spec.
    smon_rewrite01.
    set (a := offset n sp).
    assert (a ∈ nAfter (S n) sp) as Hin.
    + rewrite nAfter_nonempty.
      rewrite union_spec.
      right.
      rewrite singleton_spec.
      reflexivity.
    + destruct (H a Hin) as [Ha Hm].
      decided Ha.
      setoid_rewrite ret_bind.
      setoid_rewrite (semiNeutral_get_put MEM (popMany n)).
      setoid_rewrite <- (confined_put SP); [ | typeclasses eauto ].
      repeat setoid_rewrite lens_put_get.
      decided Hm.
      setoid_rewrite ret_tt_bind.
      setoid_rewrite (confined_put SP); [ | typeclasses eauto ].
      setoid_rewrite <- (semiNeutral_put_put MEM (popMany n)).
      setoid_rewrite <- (confined_put SP); [ | typeclasses eauto ].
      apply IHn.
      clear a Hin Ha Hm.
      intros a Hin.
      apply (H a).
      rewrite nAfter_nonempty.
      rewrite union_spec.
      now left.
Qed.
