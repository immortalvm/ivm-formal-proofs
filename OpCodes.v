Require Import Coq.ZArith.ZArith.

Local Open Scope Z.

Notation EXIT := 0.
Notation NOP := 1.
Notation JUMP := 2.
Notation JZ_FWD := 3.
Notation JZ_BACK := 4.
Notation SET_SP := 5.
Notation GET_PC := 6.
Notation GET_SP := 7.
Notation PUSH0 := 8.
Notation PUSH1 := 9.
Notation PUSH2 := 10.
Notation PUSH4 := 11.
Notation PUSH8 := 12.
Notation LOAD1 := 16.
Notation LOAD2 := 17.
Notation LOAD4 := 18.
Notation LOAD8 := 19.
Notation STORE1 := 20.
Notation STORE2 := 21.
Notation STORE4 := 22.
Notation STORE8 := 23.
Notation ADD := 32.
Notation MULT := 33.
Notation DIV := 34.
Notation REM := 35.
Notation LT := 36.
Notation AND := 40.
Notation OR := 41.
Notation NOT := 42.
Notation XOR := 43.
Notation POW2 := 44.

Notation READ_FRAME := 255.
Notation READ_PIXEL := 254.
Notation NEW_FRAME := 253.
Notation SET_PIXEL := 252.
Notation ADD_SAMPLE := 251.
Notation PUT_CHAR := 250.
Notation PUT_BYTE := 249.
