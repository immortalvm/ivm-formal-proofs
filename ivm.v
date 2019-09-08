From Equations Require Import Equations.
Set Equations With UIP.

Require Import Coq.Bool.Bvector.
Require Import Nat.
Require Vector.
Require Import Arith Omega List.

Set Implicit Arguments.


Arguments Vector.cons : default implicits.
Arguments Bcons : default implicits.
Arguments Bneg : default implicits.
Arguments Bsign : default implicits.
Arguments BVand : default implicits.
Arguments BVor : default implicits.
Arguments BVxor : default implicits.

Import ListNotations.


(**** Monad basics *)


(* Special notation for the identity monad *)

(* Bind *)
Notation "x |> f" := (f x) (at level 98, left associativity, only parsing).


(* Based on https://github.com/coq/coq/wiki/AUGER_Monad. *)
Class Monad (m: Type -> Type): Type :=
{
  ret: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;

  monad_right: forall A (a: m A), a = bind a (@ret A);
  monad_left: forall A (a: A) B (f: A -> m B), f a = bind (ret a) f;
  monad_assoc: forall A (ma: m A) B f C (g: B -> m C),
      bind ma (fun x => bind (f x) g) = bind (bind ma f) g
}.
Notation "ma >>= f" := (bind ma _ f) (at level 98, left associativity).

Section monadic_functions.
  Context {m: Type -> Type} `{M: Monad m}.

  Definition wbind {A: Type} (ma: m A) {B: Type} (mb: m B) :=
    ma >>= fun _ => mb.

  Definition join {A: Type} (mma: m (m A)): m A :=
    mma >>= id.

  Definition liftM {A B: Type} (f: A -> B) (ma: m A): m B :=
    ma >>= fun a => ret (f a).

  Definition liftM2 {A B C: Type} (f: A -> B -> C) (ma: m A) (mb: m B): m C :=
    ma >>= (fun a => mb >>= (fun b => ret (f a b))).

  Definition traverse {A B: Type} (f: A -> m B) (lst: list A) : m (list B) :=
    fold_right (liftM2 cons) (ret []) (map f lst).

  Equations traverse_vector {A B: Type} (f: A -> m B) {n} (vec: Vector.t A n) : m (Vector.t B n) :=
    traverse_vector _ Vector.nil := ret (Vector.nil B);
    traverse_vector f (Vector.cons x v) with f x, traverse_vector f v := {
      traverse_vector _ _ mb mvb := mb >>= (fun b => mvb >>= (fun vb => ret (Vector.cons b vb)))
    }.

End monadic_functions.

Notation "ma ;; mb" := (wbind ma mb) (at level 60, right associativity).
Notation "a ::= mb ; mc" := (mb >>= (fun a => mc)) (at level 60, right associativity).

Instance Maybe: Monad option :=
{
  ret := @Some;
  bind A ma B f := match ma with None => None | Some a => f a end
}.
Proof.
  - abstract (intros A a; case a; split).
  - abstract (split).
  - abstract (intros A x B f C g; case x; split).
Defined.



(**** Bit vectors. TODO: Should we use BinNat instead of nat as well? *)

Definition Bits8 := Bvector 8.
Definition Bits16 := Bvector 16.
Definition Bits32 := Bvector 32.
Definition Bits64 := Bvector 64.

Equations fromBits {n} (v: Bvector n) : nat :=
  fromBits Vector.nil := 0 ;
  fromBits (Vector.cons b r) := 2 * fromBits r + (if b then 1 else 0).

Equations toBits n (k: nat) : Bvector n :=
  toBits 0 _ := Bnil ;
  toBits (S n) k :=
    Bcons (eqb 1 (modulo k 2)) (toBits n (div k 2)).

(* Compute (fromBits (toBits 8 (213 + 65536))). *)

Definition fromBits8 : Bits8 -> nat := fromBits. Coercion fromBits8 : Bits8 >-> nat.
Definition fromBits16 : Bits16 -> nat := fromBits. Coercion fromBits16 : Bits16 >-> nat.
Definition fromBits32 : Bits32 -> nat := fromBits. Coercion fromBits32 : Bits32 >-> nat.
Definition fromBits64 : Bits64 -> nat := fromBits. Coercion fromBits64 : Bits64 >-> nat.

Equations fromLittleEndian {n} (v: Vector.t Bits8 n): nat :=
  fromLittleEndian Vector.nil := 0;
  fromLittleEndian (Vector.cons x r) := 256 * (fromLittleEndian r) + x. (* Implicit coercion *)

Equations toLittleEndian n (k: nat) : Vector.t Bits8 n :=
  toLittleEndian 0 _ := Vector.nil Bits8;
  toLittleEndian (S n) k := Vector.cons (toBits 8 k) (toLittleEndian n (k / 256)).

(* Compute (fromLittleEndian (toLittleEndian 2 12345)). *)

Definition addNat64 k (x: Bits64) : Bits64 := k + x |> toBits 64. (* Implicit coercion *)
Definition neg64 (x: Bits64) : Bits64 := Bneg x |> addNat64 1.
Definition add64 (x y: Bits64) : Bits64 := x + y |> toBits 64. (* Implicit coercion *)
Definition subNat64 k (x: Bits64) : Bits64 := add64 (neg64 (toBits 64 k)) x.

Definition signExtend {n} (v: Bvector (S n)) : Bits64.
  refine (
      let sign := Bsign v in
      let extra := nat_rect Bvector Bnil (Bcons sign) (64 - n) in
      let bits := Vector.append v extra in
      Vector.take 64 _ bits). (* in case n > 64 *)
  omega.
Defined.

Definition zero64 : Bits64 := toBits 64 0.
Definition true64 : Bits64 := Bneg zero64.


(**** State *)

Equations addresses n (start: Bits64) : Vector.t Bits64 n :=
  addresses 0 _ := Vector.nil Bits64;
  addresses (S n) start := Vector.cons start (addresses n (addNat64 1 start)).

Definition Gray := Bits8.
Definition Color := (Bits16 * Bits16 * Bits16)%type.

(* Record types inspired by the 'sigma' type of Equations. *)

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Record InputFrame :=
  mkInputFrame {
      iWidth: Bits32;
      iHeight: Bits32;
      iPixel: nat -> nat -> option Gray;
      iDef: forall x y, x < iWidth -> y < iHeight -> iPixel x y <> None;
    }.

Record OutputImage :=
  mkOutputImage {
      oWidth: Bits32;
      oHeight: Bits32;
      oPixel: nat -> nat -> option Color;
      oDef: forall x y, x < oWidth -> y < oHeight -> oPixel x y <> None;
    }.

Record OutputSound := mkOutputSound { oRate: Bits32; oSamples: list (Bits16 * Bits16) }.

Record State :=
  mkState {
      terminated: bool;
      PC: Bits64; (* Program counter *)
      SP: Bits64; (* Stack pointer *)
      input: list InputFrame;
      output: list (OutputImage * OutputSound);
      memory: Bits64 -> option Bits8;
      allocation: Bits64 -> nat;

      allocations_defined:
        forall (a: Bits64),
          memory a <> None <->
          exists start, Vector.Exists (eq a) (addresses (allocation start) start);

      allocations_disjoint:
        forall start0 start1,
          (Vector.Exists
             (fun a => Vector.Exists (eq a) (addresses (allocation start0) start0))
             (addresses (allocation start1) start1)) ->
          start0 = start1;
    }.

Unset Primitive Projections.


Lemma State_expanion (s: State) :
  s = {|
    terminated := s.(terminated);
    PC := s.(PC);
    SP := s.(SP);
    input := s.(input);
    output := s.(output);
    memory := s.(memory);
    allocation := s.(allocation);
    allocations_defined := s.(allocations_defined);
    allocations_disjoint := s.(allocations_disjoint);
  |}.
Proof.
  reflexivity.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.


(* Since State is finite, we might be provable even without
PropExtensionality or Functionalextensionality, but this will have to wait. *)
Lemma State_extensionality : forall (s0 s1: State),
    s0.(terminated) = s1.(terminated)
    -> s0.(PC) = s1.(PC)
    -> s0.(SP) = s1.(SP)
    -> s0.(input) = s1.(input)
    -> s0.(output) = s1.(output)
    -> s0.(memory) = s1.(memory)
    -> s0.(allocation) = s1.(allocation)
    -> s0 = s1.
Proof.
  intros s0 s1.
  intros e1 e2 e3 e4 e5 e6 e7.
  rewrite (State_expanion s0).
  rewrite e1, e2, e3, e4, e5.
  clear e1 e2 e3 e4 e5.
  (* TODO: The rest involves dependent types, but it should be within reach. *)
Admitted.


(**** Relational state monad *)

Definition ST (A: Type) := State -> A -> State -> Prop.

(* Extensionality is needed since A is an arbitrary type.
   This can be avoided if we define monads in terms of a setoid.
 *)
Lemma ST_extensionality {A} (st0 st1: ST A):
  (forall s0 x1 s1, st0 s0 x1 s1 <-> st1 s0 x1 s1) -> st0 = st1.
Proof.
  intro H.
  repeat (intro || apply functional_extensionality).
  apply propositional_extensionality.
  apply H.
Qed.

Require Import Coq.Program.Tactics.

Instance StateMonad: Monad ST :=
{
  ret A x0 s0 x1 s1 := x1 = x0 /\ s0 = s1;
  bind A ma B f s0 b s2 := exists a s1, ma s0 a s1 /\ f a s1 b s2;
}.
Proof. (* TODO: Automate *)
  - intros; apply ST_extensionality; intros; split.
    + eauto.
    + intros [? [? [? [? ?]]]].
      subst.
      assumption.
  - intros; apply ST_extensionality; intros; split.
    + eauto.
    + intros [? [? [[? ?] ?]]].
      subst.
      assumption.
  - intros; apply ST_extensionality; intros; split.
    + intros [? [? [? [? [? [? ?]]]]]].
      exists x2, x3; split.
      * exists x, x0; split; assumption.
      * assumption.
    + intros [? [? [[? [? [? ?]]] ?]]].
      exists x2, x3; split.
      * assumption.
      * exists x, x0; split; assumption.
Defined.


(**** Change management *)

Definition intersect {A} (st1 st2: ST A): ST A :=
  fun s0 x1 s1 => st1 s0 x1 s1 /\ st2 s0 x1 s1.

Notation "st1 ⩀ st2" := (intersect st1 st2) (at level 50, left associativity).

Definition stateUnchangedST {A} : ST A :=
  fun s0 _ s1 => s0 = s1.

Lemma ret_characterized {A} (x: A) :
  stateUnchangedST ⩀ (fun _ x1 _ => x = x1) = ret x.
Proof.
  unfold stateUnchangedST, intersect.
  apply ST_extensionality.
  firstorder.
Qed.

Definition registersUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    s0.(terminated) = s1.(terminated)
    /\ s0.(PC) = s1.(PC)
    /\ s0.(SP) = s1.(SP).

Definition memoryUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    s0.(allocation) = s1.(allocation)
    /\ s0.(memory) = s1.(memory).

Definition ioUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    s0.(input) = s1.(input)
    /\ s0.(output) = s1.(output).

Lemma stateUnchanged_characterized {A} :
  @registersUnchangedST A ⩀ memoryUnchangedST ⩀ ioUnchangedST = stateUnchangedST.
Proof.
  unfold registersUnchangedST, memoryUnchangedST, ioUnchangedST, stateUnchangedST.
  repeat (unfold intersect).
  apply ST_extensionality.
  intros; firstorder; subst; try (reflexivity || assumption).
  apply State_extensionality; assumption.
Qed.


(**** Building blocks *)

Definition valueST {A} (p: State -> A -> Prop): ST A :=
  stateUnchangedST ⩀ (fun s0 x1 _ => p s0 x1).

Definition extractST {A} (f: State -> A): ST A :=
  valueST (fun s0 x1 => f s0 = x1).

Definition getPcST : ST Bits64 := extractST PC.

Definition getSpST : ST Bits64 := extractST SP.

(* Get the value at the n bytes starting at start. *)
Definition tryGetST (n: nat) (start: Bits64) : ST (option nat) :=
  extractST (fun s => addresses n start
                   |> traverse_vector s.(memory)
                   |> liftM fromLittleEndian).

(* We assume that even undefined operations do not roll back IO. *)
Definition undefinedST {A}: ST A :=
  fun s0 _ s1 =>
    (exists i, s0.(input) = i ++ s0.(input))
    /\ match s1.(output) with
      | [] => s0.(output) = []
      | _ :: r => exists o, o ++ s1.(output) = s1.(output)
      end.

Definition valueOrUndefinedST {A} (oa: option A) : ST A :=
  match oa with Some a => ret a | _ => undefinedST end.

(* NB: The behavior is completely undefined if there is an access violation! *)
Definition getST (n: nat) (start: Bits64) : ST nat :=
  tryGetST n start >>= valueOrUndefinedST.

Definition otherMemoryUnchangedST (start: Bits64) (n: nat): ST unit :=
  fun s0 _ s1 =>
    let other a := Vector.Forall (fun x => x <> a) (addresses n start) in
    forall a, other a -> s0.(memory) a = s1.(memory) a.

(* Observe that if (setST n start value s0 x1 s1), then we know that the
   addresses were allocated because of s1.(allocations_defined).
   Formally:
   Vector.Forall (fun a => s0.(memory) a <> None) (addresses n start)
 *)
Definition setST (n: nat) (start: Bits64) (value: nat) : ST unit :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ otherMemoryUnchangedST start n
    ⩀ fun s0 _ s1 =>
        s0.(allocation) = s1.(allocation)
        /\ getST n start s1 value s1.

Definition setPcST (a: Bits64): ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        s0.(terminated) = s1.(terminated)
        /\ s0.(SP) = s1.(SP)
        /\ a = s1.(PC).

Definition setSpST (a: Bits64): ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        (* Is this more readable? *)
        terminated s0 = terminated s1
        /\ PC s0 = PC s1
        /\ a = SP s1.

Definition nextST (n: nat) : ST nat :=
  a ::= getPcST;
  setSpST (addNat64 n a);;
  getST n a.

Definition popST: ST Bits64 :=
  a ::= getSpST;
  v ::= getST 8 a;
  setSpST (addNat64 8 a);;
  ret (toBits 64 v).

(* Clips value at 64 bits! *)
Definition pushST (value: nat): ST unit :=
  a0 ::= getSpST;
  let a1 := subNat64 8 a0 in
  setSpST a1;;
  setST 8 a1 value.


(**** Memory allocation *)

Definition otherAllocationsUnchanged (start: Bits64) : ST unit :=
  fun s0 _ s1 =>
    forall a, a <> start -> s0.(allocation) a = s1.(allocation) a.

Definition allocateST (n: nat) : ST Bits64 :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 start s1 =>
        s0.(allocation) start = 0
        /\ s1.(allocation) start = n
        /\ otherAllocationsUnchanged start s0 tt s1
        /\ otherMemoryUnchangedST start n s0 tt s1
        /\ getST n start s1 0 s1. (* Memory initialized to 0. *)

Definition deallocateST (start: Bits64) : ST unit :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ otherAllocationsUnchanged start
    ⩀ fun s0 _ s1 =>
        s1.(allocation) start = 0
        /\ otherMemoryUnchangedST start (s0.(allocation) start) s0 tt s1.

(* Observe that allocations_defined ensures that unallocated memory is
None and that it makes sense to allocate 0 bytes or deallocate an address
which was never allocated! *)


(**** Input and output *)

Definition newFrameST (width height sampleRate: nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        s0.(input) = s1.(input)
        /\ match s1.(output) with
          | [] => False
          | (image, sound) :: rest =>
            s0.(output) = rest
            /\ width = image.(oWidth)
            /\ height = image.(oHeight)
            /\ sampleRate = sound.(oRate)
            /\ sound.(oSamples) = []
          end.

(* Does not take into account that the operation may be undefined. *)
Definition trySetPixelST (x y r g b : nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        s0.(input) = s1.(input)
        /\ match s0.(output), s1.(output) with
          | (i0, s0) :: r0, (i1, s1) :: r1 =>
            r0 = r1
            /\ s0 = s1
            (* Redundant:
            /\ i0.(oWidth) = i1.(oWidth)
            /\ i0.(oHeight) = i1.(oHeight) *)
            /\ forall xx yy, i1.(oPixel) xx yy = if (xx =? x) && (yy =? y)
                                           then Some (toBits 16 r, toBits 16 g, toBits 16 b)
                                           else i0.(oPixel) xx yy
          | _, _ => False
          end.

Definition setPixelST (x y r g b : nat) : ST unit :=
  let wd (s: State) :=
      match s.(output) with
      | [] => false
      | (i, _) :: _ => (x <? i.(oWidth)) && (y <? i.(oHeight))
      end in
  wellDefined ::= extractST wd;
  if wellDefined
  then trySetPixelST x y r g b
  else undefinedST.

(* Does not take into account that the operation may be undefined. *)
Definition tryAddSampleST (left right : nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        s0.(input) = s1.(input)
        /\ match s0.(output), s1.(output) with
          | (i0, s0) :: r0, (i1, s1) :: r1 =>
            r0 = r1
            /\ i0 = i1
            /\ s0.(oRate) = s1.(oRate)
            /\ (toBits 16 left, toBits 16 right) :: s0.(oSamples) = s1.(oSamples)
          | _, _ => False
          end.

Definition addSampleST (left right : nat) : ST unit :=
  let wd (s: State) := match s.(output) with [] => false | _ => true end in
  wellDefined ::= extractST wd;
  if wellDefined
  then tryAddSampleST left right
  else undefinedST.



(**** Execution *)

Definition exitST : ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        terminated s1 = true
        /\ PC s0 = PC s1
        /\ SP s0 = SP s1.

Module Instructions.
  Notation "'EXIT'" := 0.
  Notation "'NOP'" := 1.
  Notation "'JUMP'" := 2.
  Notation "'JUMP_ZERO'" := 3.
  Notation "'SET_SP'" := 4.
  Notation "'GET_PC'" := 5.
  Notation "'GET_SP'" := 6.
  Notation "'PUSH0'" := 7.
  Notation "'PUSH1'" := 8.
  Notation "'PUSH2'" := 9.
  Notation "'PUSH4'" := 10.
  Notation "'PUSH8'" := 11.
  Notation "'SIGX1'" := 12.
  Notation "'SIGX2'" := 13.
  Notation "'SIGX4'" := 14.
  Notation "'LOAD1'" := 16.
  Notation "'LOAD2'" := 17.
  Notation "'LOAD4'" := 18.
  Notation "'LOAD8'" := 19.
  Notation "'STORE1'" := 20.
  Notation "'STORE2'" := 21.
  Notation "'STORE4'" := 22.
  Notation "'STORE8'" := 23.
  Notation "'ALLOCATE'" := 24.
  Notation "'DEALLOCATE'" := 25.
  Notation "'ADD'" := 32.
  Notation "'MULT'" := 33.
  Notation "'DIV'" := 34.
  Notation "'REM'" := 35.
  Notation "'LT'" := 36.
  Notation "'AND'" := 40.
  Notation "'OR'" := 41.
  Notation "'NOT'" := 42.
  Notation "'XOR'" := 43.
  Notation "'POW2'" := 44.
  Notation "'NEW_FRAME'" := 48.
  Notation "'SET_PIXEL'" := 49.
  Notation "'ADD_SAMPLE'" := 50.
End Instructions.

Section step_definition.
Import Instructions.

Definition stepST : ST unit :=
  nextST 1 >>= fun op => match op with
  | EXIT => exitST
  | NOP => stateUnchangedST

  | JUMP => popST >>= setPcST
  | JUMP_ZERO =>
      offset ::= nextST 1;
      v ::= popST;
      if v =? 0
      then pc ::= getPcST;
           setPcST (add64 pc (signExtend (toBits 8 offset)))
      else stateUnchangedST

  | SET_SP => popST >>= setSpST
  | GET_PC => getPcST >>= pushST
  | GET_SP => getSpST >>= pushST

  | PUSH0 => pushST 0
  | PUSH1 => nextST 1 >>= pushST
  | PUSH2 => nextST 2 >>= pushST
  | PUSH4 => nextST 4 >>= pushST
  | PUSH8 => nextST 8 >>= pushST

  | SIGX1 => v ::= popST; pushST (signExtend v)
  | SIGX2 => v ::= popST; pushST (signExtend v)
  | SIGX4 => v ::= popST; pushST (signExtend v)

  | LOAD1 => popST >>= getST 1 >>= pushST
  | LOAD2 => popST >>= getST 2 >>= pushST
  | LOAD4 => popST >>= getST 4 >>= pushST
  | LOAD8 => popST >>= getST 8 >>= pushST

  | STORE1 => a ::= popST; v ::= popST; setST 1 a v
  | STORE2 => a ::= popST; v ::= popST; setST 2 a v
  | STORE4 => a ::= popST; v ::= popST; setST 4 a v
  | STORE8 => a ::= popST; v ::= popST; setST 8 a v

  | ALLOCATE => popST >>= allocateST >>= pushST
  | DEALLOCATE => popST >>= deallocateST

  (* Clip to 64 bits *)
  | ADD => x ::= popST; y ::= popST; pushST (x + y)
  | MULT => x ::= popST; y ::= popST; pushST (x * y)
  | DIV =>
      x ::= popST;
      y ::= popST;
      pushST (if x =? 0 then 0 else y / x)
  | REM =>
      x ::= popST;
      y ::= popST;
      pushST (if x =? 0 then 0 else modulo y x)
  | LT =>
      x ::= popST;
      y ::= popST;
      pushST (if y <? x then true64 else zero64) (* multiple coercions *)
  | AND =>
      x ::= popST;
      y ::= popST;
      pushST (BVand x y : Bits64)
  | OR =>
      x ::= popST;
      y ::= popST;
      pushST (BVor x y : Bits64)
  | XOR =>
      x ::= popST;
      y ::= popST;
      pushST (BVxor x y : Bits64)
  | NOT =>
      x ::= popST;
      pushST (Bneg x : Bits64)
  | POW2 =>
      n ::= popST;
      pushST (2 ^ n)

  | NEW_FRAME =>
      rate ::= popST;
      height ::= popST;
      width ::= popST;
      newFrameST width height rate
  | SET_PIXEL =>
      b ::= popST;
      g ::= popST;
      r ::= popST;
      y ::= popST;
      x ::= popST;
      setPixelST x y r g b
  | ADD_SAMPLE =>
      right ::= popST;
      left ::= popST;
      addSampleST left right

  (* TODO: Handle input instructions when they are ready. *)

  | _ => undefinedST
  end.

End step_definition. (* This limits the scope of the instruction notation. *)

Equations nStepsST (n: nat): ST unit :=
  nStepsST 0 := stateUnchangedST;
  nStepsST (S n) := stepST ;; nStepsST n.

(* Transitive closure *)
Definition multiStepST: ST unit :=
  fun s0 _ s1 => exists n, nStepsST n s0 tt s1.

Definition runST: ST unit:=
  fun s0 _ s1 =>
    multiStepST s0 tt s1
    /\ s1.(terminated) = true.

(* Avoid complaints from Equations when using depelim. *)
Derive Signature for Vector.Exists.

Definition initialState (inputList: list InputFrame) : State.
  refine ({|
             terminated := false;
             PC := zero64;
             SP := zero64;
             input := inputList;
             output := [];
             memory := fun _ => None;
             allocation := fun _ => 0;
           |}).
  (* TODO: Automate *)
  - firstorder.
    exfalso.
    revert_last.
    funelim (addresses 0 x).
    simpl.
    intro H.
    depelim H.
  - intros x y.
    funelim (addresses 0 x).
    simpl.
    intro H.
    exfalso.
    depelim H.
Defined.

Equations fillST (start: Bits64) (bytes: list Bits8) : ST unit :=
  fillST _ [] := stateUnchangedST;
  fillST a (x :: r) := setST 1 a x ;; fillST (addNat64 1 a) r.

(* Because of non-determinism and Coq's lack of general recursion, this
   must be defined as a predicate rather than a (partial) function. *)
Definition execution (prog: list Bits8) (arg: list Bits8) (inputList: list InputFrame) (outputList: list (OutputImage * OutputSound)) : Prop :=
  let s0 :=
      initialState inputList in
  let prepST: ST unit :=
      prog_start ::= allocateST (length prog);
      fillST prog_start prog;;
      setPcST prog_start;;
      let restSize := length arg + 3 * 8 in
      arg_start ::= allocateST restSize;
      fillST arg_start arg;;
      setSpST (addNat64 restSize arg_start) in
  let checkOutputST: ST unit :=
      (* Observe that we reverse the output list. *)
      fun s0 _ s1 => s0 = s1 /\ s1.(output) = rev outputList in
  let st :=
      prepST ;; runST ;; checkOutputST in
  exists s1, st s0 tt s1.
