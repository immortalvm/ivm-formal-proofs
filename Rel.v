From iVM Require Export Restr Mon.
From iVM Require Import DSet.
Import DSetNotations.

Unset Suggest Proof Using.


(** ** Relations ***)

Class Rel (X: Type) := rel : relation X.

#[global]
Hint Mode Rel - : typeclass_instances.

Infix "⊑" := rel (at level 70).
Arguments rel : clear implicits.
Arguments rel {_} _.


(** ** Basics *)

Section basics_section.

  Context {X: Type}.

  Global Instance prop_relation : Rel Prop := fun _ _ => True.

  Instance true_relation : Rel X | 30 := fun _ _ => True.

  Instance true_relation_equivalence : Equivalence true_relation.
  Proof.
    split; intro; intros; exact I.
  Qed.

  (* Fallback to Leibniz' equality. *)
  Global Instance eq_relation : Rel X | 20 := eq.

  (* Is this useful? *)
  Global Instance eq_Rel_equivalence : Equivalence eq_relation := eq_equivalence.

  Context (RX: Rel X).

  Global Instance option_relation : Rel (option X) | 5 :=
    fun x x' =>
      match x, x' with
      | None, _ => True
      | Some _, None => False
      | Some x, Some x' => x ⊑ x'
      end.

  Global Instance option_relation_reflexive {HrX: Reflexive RX} : Reflexive option_relation.
  Proof.
    unfold option_relation. intros [x|]; reflexivity.
  Qed.

  Global Instance option_relation_transitive {HtX: Transitive RX} : Transitive option_relation.
  Proof.
    intros [x|] [y|] [z|] Hxy Hyz; cbn in *; try assumption.
    - transitivity y; assumption.
    - exfalso. assumption.
  Qed.

  Context {Y} (RY: Rel Y).

  Global Instance fun_relation : Rel (X -> Y) | 10 :=
    fun f f' => forall (x x': X), x ⊑ x' -> f x ⊑ f' x'.

  Global Instance fun_relation_transitive
         {HrX: Reflexive RX}
         {HtX: Transitive RX}
         {HtY: Transitive RY} : Transitive fun_relation.
  Proof.
    intros f g h Hfg Hgh x x' Hx.
    transitivity (g x').
    - apply Hfg. exact Hx.
    - apply Hgh. reflexivity.
  Qed.

  Global Instance prod_relation : Rel (X * Y) | 5 :=
    fun p p' =>
      match p, p' with
      | (x, y), (x', y') => x ⊑ x' /\ y ⊑ y'
      end.

  Global Instance prod_relation_reflexive {HrX: Reflexive RX} {HrY: Reflexive RY} : Reflexive prod_relation.
  Proof.
    intros [x y]. cbn. split; reflexivity.
  Qed.

  Global Instance prod_relation_symmetric {HsX: Symmetric RX} {HsY: Symmetric RY} : Symmetric prod_relation.
  Proof.
    intros [x y] [x1 y1] [Hx Hy]. split; symmetry; assumption.
  Qed.

  Global Instance prod_relation_transitive {HtX: Transitive RX} {HtY: Transitive RY} : Transitive prod_relation.
  Proof.
    intros [x1 y1] [x2 y2] [x3 y3] [Hx12 Hy12] [Hx23 Hy23].
    split.
    - transitivity x2; assumption.
    - transitivity y2; assumption.
  Qed.

  Context (RX': Rel X).

  Instance and_relation : Rel X | 30 := fun x x' => RX x x' /\ RX' x x'.

  Instance and_reflexive {HrX: Reflexive RX} {HrX': Reflexive RX'} : Reflexive and_relation.
  Proof.
    intros x; split; reflexivity.
  Qed.

  Instance and_symmetric {HrX: Symmetric RX} {HrX': Symmetric RX'} : Symmetric and_relation.
  Proof.
    intros x y [H H']; split; symmetry; assumption.
  Qed.

  Instance and_transitive {HrX: Transitive RX} {HrX': Transitive RX'} : Transitive and_relation.
  Proof.
    intros x1 x2 x3 [H12 H12'] [H23 H23']; split; transitivity x2; assumption.
  Qed.

End basics_section.


(** ** Lenses *)

Section lens_section.

  Context {S X} (LX: Lens S X).

  Context {RX: Rel X}.

  Definition lens_relation : relation S := fun s s' => proj s ⊑ proj s'.

  Global Instance lens_relation_reflexive {HrX: Reflexive RX} : Reflexive lens_relation.
  Proof.
    unfold lens_relation. intros s. reflexivity.
  Qed.

  Global Instance lens_relation_symmetric {HsX: Symmetric RX} : Symmetric lens_relation.
  Proof.
    unfold lens_relation. intros s s' H.
    symmetry; assumption.
  Qed.

  Hint Mode Lens - - : typeclass_instances.

  Global Instance lens_relation_transitive {HtX: Transitive RX} : Transitive lens_relation.
  Proof.
    unfold lens_relation. intros s1 s2 s3 H12 H23.
    transitivity (proj s2); assumption.
  Qed.

End lens_section.


(** ** Proper effects *)

(* TODO: Redefine as subclass of Proper? *)
(** Like [Proper], but for [Rel]. *)
Class PropR {X: Type} {RX: Rel X} (x: X) := propR : x ⊑ x.

Section proper_section.

  Context (S: Type) {RS: Rel S}
          (M: Type -> Type) {SM: SMonad S M} {RM: forall X (RX: Rel X), Rel (M X)}.

  Class SMonadPropR :=
  {
    ret_propr {X} (RX: Rel X) : PropR (ret (M:=M) (X:=X));
    bind_propr {X Y} (RX: Rel X) (RY: Rel Y) : PropR (bind (M:=M) (X:=X) (Y:=Y));
    err_least {X} (RX: Rel X) (mx: M X) : err (M:=M) (X:=X) ⊑ mx;
    get_propr : PropR (@get _ _ SM);
    put_propr : PropR (@put _ _ SM);
  }.

End proper_section.
