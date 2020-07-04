Require Export Equations.Equations.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.micromega.Lia.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Vectors.Vector. (** Does not open [vector_scope]. *)
Require Export Coq.Bool.Bvector.
Require Export Coq.Lists.List. (** Opens [list_scope]. *)
Require Export Coq.Program.Basics.

Export EqNotations.

(** This clearly does not work properly at the moment. *)
Unset Suggest Proof Using.


(** ** Tactics *)

Tactic Notation "by_lia" constr(P) "as" ident(H) := assert P as H; [lia|].

Ltac derive name term :=
  let H := fresh in
  let A := type of term in
  assert A as H;
  [ exact term | ];
  clear name;
  rename H into name.

(** From http://ropas.snu.ac.kr/gmeta/source/html/LibTactics.html. *)
Ltac destructs H :=
  let X := fresh in
  let Y := fresh in
  first [ destruct H as [X Y]; destructs X; destructs Y | idtac ].

Ltac idestructs := repeat (let X := fresh in intro X; destructs X).


(** ** Booleans *)

Derive NoConfusion for bool.

Goal true <> false.
Proof.
  intro H.
  exact (noConfusion_inv H).
Qed.

Coercion Is_true : bool >-> Sortclass.

Proposition true_is_true : true.
Proof. exact I. Qed.

Proposition false_is_false : not false.
Proof. exact id. Qed.

Proposition false_if_not_true {b: bool} : not b -> b = false.
Proof.
  destruct b.
  - intros H. contradict H. exact true_is_true.
  - intros _. reflexivity.
Qed.

(** See also [Is_true_eq_left], [Is_true_eq_right] and [Is_true_eq_true]. *)

Notation as_bool x := (if x then true else false).


(** ** Decidable propositions *)

(** We are not interested in Vector.eq_dec. *)
Notation eq_dec := (Classes.eq_dec).

Instance Z_EqDec: EqDec Z := Z.eq_dec.
Instance N_EqDec: EqDec N := N.eq_dec.

Class Decidable (P: Prop) : Type :=
  decide : { P } + { not P }.

Arguments decide P {_}.

Instance True_decidable : Decidable True := left I.
Instance False_decidable : Decidable False := right (@id False).
Instance equality_decidable {A} `{dec: EqDec A} (x y: A) : Decidable (x = y) := dec x y.
Instance is_true_decidable (x: bool) : Decidable (x) :=
  if x return (Decidable x)
  then left true_is_true
  else right false_is_false.

Section decidable_connectives.

  Context P `(DP: Decidable P).

  Global Instance not_decidable : Decidable (not P) :=
    match DP with
    | left H => right (fun f => f H)
    | right H => left H
    end.

  Context Q `(DQ: Decidable Q).

  Local Ltac cases := destruct DP; destruct DQ; constructor; tauto.

  Global Instance and_decidable : Decidable (P /\ Q). cases. Defined.
  Global Instance or_decidable : Decidable (P \/ Q). cases. Defined.
  Global Instance impl_decidable : Decidable (P -> Q). cases. Defined.

End decidable_connectives.


(** ** Options *)

Derive NoConfusion for option.

Goal forall {X} (x y: X) (H: Some x = Some y), x = y.
Proof. intros ? ? ?. exact noConfusion_inv. Qed.

Instance option_eqdec {A} {Ha: EqDec A} : EqDec (option A).
Proof.
  eqdec_proof. (* Tactic in Coq-Equations *)
Defined.

Definition is_some {X} (ox: option X) : bool := as_bool ox.

Coercion is_some : option >-> bool.

Instance is_some_decidable {X} (ox: option X) : Decidable ox.
Proof. apply is_true_decidable. Defined.

Instance is_none_decidable {X} (ox: option X) : Decidable (ox = None).
Proof. destruct ox as [x|]; [right|left]; congruence. Defined.

Proposition some_is_some {X} (x: X) : Some x.
Proof. exact true_is_true. Qed.

Proposition none_is_false {X} : @None X -> False.
Proof. exact false_is_false. Qed.

(** Shortcut *)
Definition none_rect {X Y} (H: @None X) : Y :=
  False_rect Y (none_is_false H).

Definition extract {X} {ox: option X} : ox -> X :=
  match ox return ox -> X with
  | Some x => fun _ => x
  | None => fun H => none_rect H
  end.

Proposition extract_some {X} (x: X) : extract (some_is_some x) = x.
Proof. reflexivity. Qed.

Lemma some_extract {X} {ox: option X} (H: ox) : Some (extract H) = ox.
Proof.
  destruct ox as [x|].
  - simpl. reflexivity.
  - exact (none_rect H).
Qed.

Proposition is_some_eq {X} {ox: option X} {x: X} : ox = Some x -> ox.
Proof. intro H. rewrite H. reflexivity. Qed.

Proposition extract_is_some_eq {X} {ox: option X} {x: X} (H: ox = Some x) : extract (is_some_eq H) = x.
Proof. subst ox. reflexivity. Qed.

Proposition extract_unique {X} {ox: option X} (H H': ox) : extract H = extract H'.
Proof.
  destruct ox as [x|].
  - reflexivity.
  - exact (none_rect H).
Qed.


(* ** Decidable match statements *)

Instance match_decide_decidable {P: Prop} {DP: Decidable P}
         (f: P -> Prop) {Df: forall H, Decidable (f H)}
         (g: not P -> Prop) {Dg: forall H, Decidable (g H)}:
  Decidable match decide P with
            | left H => f H
            | right H => g H
            end.
Proof.
  destruct (decide P) as [H|H].
  - apply Df.
  - apply Dg.
Defined.

Instance match_option_decidable {X}
         (f: X -> Prop) {Df: forall x, Decidable (f x)}
         (Q: Prop) {DQ: Decidable Q}
         {ox: option X} :
  Decidable match ox with
            | Some x => f x
            | None => Q
            end.
Proof.
  destruct ox as [x|].
  - apply Df.
  - exact DQ.
Defined.


(* ** Decidable predicates on integers *)

Instance nat_lt_decidable (x y: nat) : Decidable (x < y) := lt_dec x y.
Instance nat_le_decidable (x y: nat) : Decidable (x <= y) := le_dec x y.

Derive NoConfusion EqDec for comparison.

(** It follows that the comparison operators are decidable for [Z] and [N]. *)

Instance bounded_all_decidable0 (P: forall (x: nat), Prop) {DP: forall x, Decidable (P x)} (n: nat) :
  Decidable (forall x, x < n -> P x).
Proof. (* TODO: simplify? *)
  induction n as [|n IH].
  - left. lia.
  - destruct IH as [IH|IH].
    + destruct (DP n) as [H|H].
      * left.
        intros x H'.
        -- by_lia (x < n \/ x = n) as H''.
           destruct H'' as [H''|H''].
           ++ exact (IH x H'').
           ++ subst x. exact H.
      * right. contradict H. apply H. lia.
    + right. contradict IH. intros x H. apply IH. lia.
Defined.

(** Clearly, [N] has the same property. *)

Local Open Scope N.

Instance bounded_all_decidable0' (P: forall (x:N), Prop) {DP: forall x, Decidable (P x)} (n: N) :
  Decidable (forall x, x < n -> P x).
Proof.
  destruct (decide (forall y, (y < N.to_nat n)%nat -> P (N.of_nat y))) as [H|H]; [left|right].
  - intros x Hx. specialize (H (N.to_nat x)).
    rewrite Nnat.N2Nat.id in H.
    apply H, nat_compare_lt.
    rewrite <- Nnat.N2Nat.inj_compare.
    exact Hx.
  - intro H'. apply H. clear H.
    intros y Hy.
    apply H'.
    unfold N.lt.
    rewrite Nnat.N2Nat.inj_compare, Nnat.Nat2N.id.
    apply nat_compare_lt.
    exact Hy.
Defined.

(** We also have a slightly stronger property. *)

Instance bounded_all_decidable1
           (n: N) (P: forall (x: N), x < n -> Prop)
           {DP: forall x (H: x < n), Decidable (P x H)} : Decidable (forall x (H: x < n), P x H).
Proof. (* TODO: simplify? *)
  assert (forall x, Decidable (forall (H: x < n), P x H)) as D.
  - intros x.
    destruct (decide (x < n)) as [H|H].
    + destruct (DP x H) as [Hd|Hd].
      * left. intros H'. rewrite (uip H' H). assumption.
      * right. contradict Hd. apply (Hd H).
    + left. intros H'. contradict H. exact H'.
  - destruct (bounded_all_decidable0' (fun x => forall (H: x < n), P x H) n) as [H|H];
      [left|right]; firstorder.
Qed.

(** In order to prove the corresponding property for [nat], we seem to need
an axiom or a different definition of [nat.le] than the one in the current
standard library, cf. "Definitional Proof-Irrelevance without K" (2019). *)