From iVM Require Import DSet Mono Cert0.
Import DSetNotations.

Unset Suggest Proof Using.

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(*****************)

Global Opaque pushMany. (* TODO *)

(* TODO: Move *)
Instance swallow_propr {n} (ops: vector Z n) : PropR (swallow ops).
Proof.
  rewrite swallow_spec.
  crush.
Qed.

(*************)

Proposition nCert_monotone n {ma mb: M bool} (Hab: ma ⊑ mb) (Hb: nCert n mb) :
  nCert n ma.
Proof.
  unfold nCert in *. transitivity mb; assumption.
Qed.

Corollary nCertN_monotone n {X} {RX: Rel X}
  (mx mx': M X) (Hmx: mx ⊑ mx') (H: nCertN n mx') : nCertN n mx.
Proof.
  unfold nCertN in *.
  assert (mx;; ret true ⊑ mx';; ret true) as HH.
  - crush. exact Hmx.
  - apply (nCert_monotone n HH H).
Qed.

(****)

Proposition wipe_swallow_precondition' u {n} (ops: vector Z n) :
  wipe u;;
  swallow ops ⊑ let* pc := get' PC in
                assume' (u # nAfter n pc);;
                swallow ops.
Proof.
  rewrite wipe_swallow_precondition.
  setoid_rewrite simplify_assume.
  transitivity (
    let* pc := get' PC in
    assume' (u # nAfter n pc);;
    ret tt;;
    swallow ops);
  [ | crush ].
  apply bind_propr'; [ apply getPc_propr | ].
  intros p p' Hp. destruct Hp.
  setoid_rewrite <- simplify_assume.
  apply assume_rel.
  intros H.
  apply bind_propr'; [ apply wipe_less | ].
  crush.
Qed.

(*********************)

Definition wipeStack n :=
  let* a := get' SP in
  wipe (nBefore (n * 8) a).

Proposition wipeStack_less n : wipeStack n ⊑ ret tt.
Proof.
  unfold wipeStack. rewrite get_spec. cbn.
  rewrite bind_assoc. rewrite <- get_ret. crush.
  rewrite ret_bind. apply wipe_less.
Qed.

Proposition wipeStack_less' {X} {RX: Rel X}
  {mx mx': M X} (Hmx: mx ⊑ mx') n : wipeStack n;; mx ⊑ mx'.
Proof.
  rewrite <- ret_tt_bind.
  apply bind_propr'.
  apply wipeStack_less.
  crush. apply Hmx.
Qed.

Corollary wipeStack_nCert
  {ma mb: M bool} (Hab: ma ⊑ mb)
  {n} (H: nCert n mb) m : nCert n (wipeStack m;; ma).
Proof.
  exact (nCert_monotone _ (wipeStack_less' Hab m) H).
Qed.

Corollary wipeStack_nCertN
  {ma mb: M unit} (Hab: ma ⊑ mb)
  {n} (H: nCertN n mb) m : nCertN n (wipeStack m;; ma).
Proof.
  unfold nCertN in *.
  rewrite bind_assoc.
  assert (ma;; ret true ⊑ mb;; ret true) as HH.
  - crush. exact Hab.
  - apply (wipeStack_nCert HH H).
Qed.

(***)

Proposition rel_ret_tt
            mu Y (my my' : M Y)
            `(mu ⊑ ret tt)
            `(my ⊑ my') : mu;; my ⊑ my'.
Proof.
  assert (my' = ret tt;; my') as HH.
  - rewrite ret_bind. reflexivity.
  - rewrite HH. crush; assumption.
Qed.

(* TODO: Postpone? *)
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

(* TODO: Postpone *)
Definition stdStart m n {o} (ops: vector Z o) : M (vector B64 n) :=
  let* v := popN n in
  wipeStack (m + n);;
  swallow ops;;
  ret v.

(** By putting [swallow] after [wipeStack] we ensure that [stdStart] fails
    if the operations overlap with (the relevant parts of) the stack. *)

(***)

Definition clearMem (mem: Memory) (a: Addr) (n: nat) : Memory :=
  update (Lens := restrLens (nAfter n a)) mem (fun _ _ _ => None).

Proposition wipe_nAfter a n :
  wipe (nAfter n a) =
    let* mem := get' MEM in
    put' MEM (clearMem mem a n).
Proof.
  unfold wipe.
  repeat rewrite put_spec. cbn.
  repeat rewrite get_spec. cbn.
  smon_rewrite.
Qed.

(***)

Instance restr_relation (u: DSet B64) : Rel (Memory' u) :=
  fun f g => forall a, forall (Hu: a ∈ u),
    forall (Ha: Machine.available' a), f a Hu Ha ⊑ g a Hu Ha.

Instance getMem'_propr u : PropR (get' (MEM' u)).
Proof.
  rewrite get_spec. cbn. crush. unfold rel.
  intros a Hu Ha.
  apply Hst.
Qed.

Instance putMem'_propr u : PropR (put' (MEM' u)).
Proof.
  intros f g Hfg. rewrite put_spec. cbn.
  unfold compose. crush. srel_destruct Hst.
  repeat split; unfold lens_relation; lens_rewrite; try assumption.
  do 2 rewrite proj_update. crush.
  destruct (decide _) as [H|_].
  - apply Hfg.
  - apply Hst_mem.
Qed.
