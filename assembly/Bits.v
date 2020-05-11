Require Import Utf8.

Require Export Assembly.Convenience.
Require Export Coq.ZArith.ZArith.
Require Export Coq.micromega.Lia.

Set Implicit Arguments.


(** ** Booleans and numbers *)

Open Scope bool_scope.
Coercion is_true : bool >-> Sortclass.

Coercion Z.of_nat : nat >-> Z.


(** ** Bits *)

Definition BitList := list bool.
Identity Coercion Id_BitList_List : BitList >-> list.

Definition boolToNat (x: bool) : nat := if x then 1 else 0.
Coercion boolToNat : bool >-> nat.

(** Little-endian (reverse of binary notation) *)
Equations bitListToNat (_: BitList) : nat :=
  bitListToNat [ ] := 0;
  bitListToNat (x :: u) := 2 * bitListToNat u + x.

Coercion bitListToNat : BitList >-> nat.

(** Specialize [to_list] to get coercion [Bits >-> nat]. *)
Definition Bits: nat -> Type := Vector.t bool.
Definition to_BitList {n} (u: Bits n) : BitList := u.
Coercion to_BitList : Bits >-> BitList.

Open Scope vector.
Open Scope Z_scope.

Equations toBits (n: nat) (_: Z) : Bits n :=
  toBits O _ := [];
  toBits (S n) z := (z mod 2 =? 1) :: toBits n (z / 2).

Close Scope Z_scope.
Close Scope vector.

Equations signed (_: list bool) : Z :=
  signed [] := 0;
  signed (x :: u) := match u with
                    | [] => -x
                    | _ => 2 * signed u + x
                    end.

Notation B8 := (Bits 8).
Notation B16 := (Bits 16).
Notation B32 := (Bits 32).
Notation B64 := (Bits 64).

Notation toB8 := (toBits 8).
Notation toB16 := (toBits 16).
Notation toB32 := (toBits 32).
Notation toB64 := (toBits 64).

(*
Definition fromLittleEndian (u: list Cell) : nat :=
  bitListToNat (concat (map to_BitList u)).
 *)

Equations fromLittleEndian (_: list B8): nat :=
  fromLittleEndian [] := 0;
  fromLittleEndian (x :: r) := 256 * (fromLittleEndian r) + x.

Open Scope vector_scope.

Equations toLittleEndian n (_: Z) : Vector.t B8 n :=
  toLittleEndian 0 _ := [];
  toLittleEndian (S n) z := (toB8 z) :: (toLittleEndian n (z / 256)).

Close Scope vector_scope.


(** ** Bitmap images *)

Record Image (C: Type) :=
  mkImage {
      width: nat;
      height: nat;
      pixel (x: nat) (Hx: x < width) (y: nat) (Hy: y < height): C;
    }.

Definition noImage {C}: Image C.
  refine {|
      width := 0;
      height := 0;
      pixel x Hx y Hy := _;
    |}.
  lia.
Defined.