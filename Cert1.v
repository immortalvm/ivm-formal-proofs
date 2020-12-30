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

(* TODO: Do we have this already? *)
Proposition decide_equiv P {DP: Decidable P} : Is_true (as_bool (decide P)) <-> P.
Proof.
  destruct (decide P) as [H|H]; intuition.
  exfalso. assumption.
Qed.

Equations vector_option {X n} (u: vector (option X) n) : option (vector X n) :=
vector_option [] := Some [];
vector_option (x :: u) :=
  match x, vector_option u with
  | Some y, Some v => Some (y :: v)
  | _, _ => None
  end.

(* TODO: Rename instead *)
Notation nAfter_head := (nAfter_zero).

Definition nAfter_tail {n a} : nAfter n (offset 1 a) ⊆ nAfter (S n) a.
Proof.
  intros x.
  by_lia (S n = (1 + n)%nat) as HH.
  rewrite HH, nAfter_action, union_spec.
  right. exact H.
Defined.

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

(****)

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

(************************************)

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

(*****************************)

Inductive nAvailable : nat -> Addr -> Prop :=
| nAvailable_O a : nAvailable 0 a
| nAvailable_S {n a} (H0: available a) (H1: nAvailable n (offset 1 a)) : nAvailable (S n) a.

Proposition nAvailable_unique {n a} (H H': nAvailable n a) : H = H'.
Proof.
  revert a H H'. induction n; intros a H H'.
  - dependent elimination H.
    dependent elimination H'.
    reflexivity.
  - dependent elimination H as [nAvailable_S H0 H1].
    dependent elimination H' as [nAvailable_S H0' H1'].
    f_equal.
    + apply is_true_unique.
    + apply IHn.
Qed.

Proposition nAvailable_spec n a :
  nAvailable n a <-> forall (i:nat), (i < n)%nat -> available (offset i a).
Proof.
  revert a. induction n; intros a.
  - split; intros H.
    + dependent elimination H. lia.
    + constructor.
  - specialize (IHn (offset 1 a)).
    destruct IHn as [IH1 IH2].
    split; intros H.
    + dependent elimination H as [ @nAvailable_S n a H0 H1 ].
      intros i Hi.
      by_lia (i = 0 \/ 0 < i)%nat as Hor.
      destruct Hor as [HO|HS].
      * subst i. rewrite Z_action_zero. exact H0.
      * specialize (IH1 H1 (i - 1)%nat). by_lia (i - 1 < n)%nat as HH.
        specialize (IH1 HH). revert IH1. rewrite <- Z_action_add.
        lia_rewrite (1 + (i - 1)%nat = i).
        tauto.
    + constructor.
      * specialize (H 0%nat). rewrite Z_action_zero in H.
        apply H. lia.
      * apply IH2. intros i Hi.
        rewrite <- Z_action_add.
        lia_rewrite (1 + i = S i).
        apply H. lia.
Qed.

Instance nAvailable_decidable n a : Decidable (nAvailable n a).
Proof.
  apply (decidable_proper (nAvailable_spec n a)).
Qed.

(* TODO: Needed? *)
Definition nAvailable_split {n a} (Ha: nAvailable (S n) a) :
    available a * nAvailable n (offset 1 a) :=
  ltac:(now dependent elimination Ha).

(****************)

Section LastWitness_section.

  Context
    (P: nat -> Prop)
    {DP: forall i, Decidable (P i)}.

  Inductive LastWitness n :=
  | SomeWitness
    {i:nat} (Hi: (i<n)%nat) (Hp: P i)
    (Ho: forall (j: nat), (i<j<n)%nat -> ~ P j)
  | NoWitness
    (Ho: forall i, (i<n)%nat -> ~ P i).

  Equations? findLast n : LastWitness n :=
    findLast 0 := NoWitness 0 _;
    findLast (S n) :=
      match decide (P n) with
      | left Hp => @SomeWitness _ n (Nat.lt_succ_diag_r n) Hp _
      | right Hp' =>
        match findLast n with
        | SomeWitness _ Hi Hp Ho => @SomeWitness _ _ _ Hp _
        | NoWitness _ _ => @NoWitness _ _
        end
      end.
  Proof.
    1,2: lia.
    - by_lia ((j < n)%nat \/ j = n) as Hjn. destruct Hjn as [Hjn|Hjn].
      + apply Ho. lia.
      + subst j. exact Hp'.
    - by_lia ((i < n)%nat \/ i = n) as Hin. destruct Hin as [Hin|Hin].
      + apply n0. exact Hin.
      + subst i. exact Hp'.
  Qed.

End LastWitness_section.

(********************)

Definition Memory' u := @restr B64 (fun a => Machine.available' a -> option B8) u.

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

Definition memoryAfter_head {n a} (f: Memory' (nAfter (S n) a)) (Ha: available a) : option Cell :=
  f a (nAfter_head n a) Ha.

Definition memoryAfter_head' {n a} (f: Memory' (nAfter (S n) a)) : option Cell :=
  match decide (available a) with
  | left Ha => memoryAfter_head f Ha
  | _ => None
  end.

Definition memoryAfter_tail {n a} (f: Memory' (nAfter (S n) a)) :
    Memory' (nAfter n (offset 1 a)) := fun x H Hx => f x (nAfter_tail _ H) Hx.

Equations fromMem {n a} (f: Memory' (nAfter n a)) : option (Cells n) :=
  fromMem (n:=0) f := Some [];
  fromMem (n:=S n) (a:=a) f :=
    match memoryAfter_head' f, fromMem (memoryAfter_tail f) with
    | Some x, Some u => Some (x :: u)
    | _, _ => None
    end.

Definition toMem a {n} (u: Cells n) : Memory' (nAfter n a) :=
  fun x Hn Ha =>
    match findLast (fun i => offset i a = x) n with
    | SomeWitness _ _ Hi _ _ => Some (Vector.nth u (Fin.of_nat_lt Hi))
    | _ => None
    end.

Proposition toMem_head a x {n} (u: Cells n) (Hadd: addressable (S n)) (Ha: available a) :
  memoryAfter_head (toMem a (x :: u)) Ha = Some x.
Proof.
  unfold memoryAfter_head.
  unfold toMem.
  set (fl := findLast _ _).
  specialize (Hadd a). cbn beta in Hadd.
  dependent elimination fl as [ @SomeWitness _ _ i Hi Hp Ho | NoWitness _ _ Ho ];
  cbn match beta.
  - f_equal.
    enough (i = 0%nat) as Hi'; [ subst i; reflexivity | ].
    apply decidable_raa.
    intros Hi'.
    apply (Hadd i).
    + lia.
    + apply Hp.
  - exfalso.
    apply (Ho 0%nat).
    + lia.
    + apply Z_action_zero.
Qed.

Proposition toMem_tail a x {n} (u: Cells n) :
  memoryAfter_tail (toMem a (x :: u)) = toMem (offset 1 a) u.
Proof.
  unfold memoryAfter_tail.
  extensionality b.
  extensionality Hin.
  extensionality Ha.
  unfold toMem.
  set (fl := findLast _ (S n)).
  set (fl' := findLast _ n).
  dependent elimination fl as [ @SomeWitness _ _ i Hi Hp Ho | NoWitness _ _ Ho ].
  - assert (i <> 0)%nat as Hi0.
    {
      intro. subst i.
      unfold nAfter in Hin.
      rewrite def_spec in Hin.
      destruct Hin as [j [Hj0 Hj1]].
      apply (Ho (S j)); [ lia | ].
      change (toB64 _) with (offset j (offset 1 a)) in Hj1.
      rewrite <- Z_action_add in Hj1.
      lia_rewrite (S j = 1 + j :> Z).
      apply Hj1.
    }
    by_lia (0 < i)%nat as H0i.
    dependent elimination fl' as [ @SomeWitness _ _ i' Hi' Hp' Ho' | NoWitness _ _ Ho' ];
    cbn match beta;
    [ f_equal | exfalso ].
    + enough (i = S i') as He.
      * subst i. cbn. f_equal. apply Fin.of_nat_ext.
      * cbn beta in Hp, Hp'.
        apply decidable_raa. intro Hne.
        rewrite <- Z_action_add in Hp'.
        by_lia (i < S i' \/ S i' < i)%nat as Hor.
        destruct Hor as [Hl|Hl].
        -- apply (Ho (S i')); [ lia | ]. rewrite <- Hp'. f_equal. lia.
        -- apply (Ho' (Nat.pred i)); [ lia | ].
          rewrite <- Z_action_add.
          lia_rewrite (1 + Nat.pred i = i).
          exact Hp.
    + apply (Ho' (pred i)); [ lia | ].
      rewrite <- Z_action_add.
      lia_rewrite (1 + Nat.pred i = i).
      exact Hp.
  - dependent elimination fl' as [ @SomeWitness _ _ i' Hi' Hp' Ho' | NoWitness _ _ Ho' ];
    cbn match beta;
    [ exfalso | reflexivity ].
    apply (Ho (S i')); [ lia | ].
    cbn in Hp'.
    rewrite <- Z_action_add in Hp'.
    lia_rewrite (S i' = 1 + i' :> Z).
    exact Hp'.
Qed.

Lemma fromMem_toMem a {n} (u: Cells n) (Hadd: addressable n) (Hav: nAvailable n a) :
  fromMem (toMem a u) = Some u.
Proof.
  revert a u Hadd Hav. induction n; intros a u Hadd Hav.
  - dependent elimination u. simp fromMem. reflexivity.
  - dependent elimination u as [ x :: u ].
    dependent elimination Hav as [ @nAvailable_S n a H0 H1 ].
    simp fromMem.
    unfold memoryAfter_head'. decided H0.
    rewrite toMem_head, toMem_tail, IHn.
    + reflexivity.
    + apply (addressable_le Hadd (m := n)). lia.
    + exact H1.
    + exact Hadd.
Qed.

(****)

Proposition getMem''_spec_member {a u} (H: a ∈ u) :
  get' (MEM'' a) =
    let* um := get' (MEM' u) in
    ret (um a H).
Proof.
  repeat rewrite get_spec. cbn. smon_rewrite.
Qed.

Proposition getMem'_spec_subset {u v} (H: u ⊆ v) :
  get' (MEM' u) =
    let* vm := get' (MEM' v) in
    ret (proj (Lens:=subsetLens H) vm).
Proof.
  repeat rewrite get_spec. cbn. smon_rewrite.
Qed.

Proposition loadMany_spec_fromMem n a :
  loadMany n a =
    let* f := get' (MEM' (nAfter n a)) in
    extr (fromMem f).
Proof.
  revert a. induction n; intros a.
  - simp loadMany.
    setoid_rewrite fromMem_equation_1.
    rewrite extr_spec.
    smon_rewrite.
  - simp loadMany.
    setoid_rewrite fromMem_equation_2.
    setoid_rewrite (IHn (offset 1 a)).
    rewrite load_spec''.
    change Machine.available' with available.
    unfold memoryAfter_head'.
    destruct (decide (available a)) as [Ha|Ha];
    smon_rewrite.

    smon_ext' (MEM' (nAfter (S n) a)) f.
    rewrite lens_put_get.

    unfold memoryAfter_head.
    setoid_rewrite (getMem''_spec_member (nAfter_head n a)).
    smon_rewrite.
    rewrite <- confined_put; [ | apply confined_neutral; typeclasses eauto ].

    setoid_rewrite (getMem'_spec_subset nAfter_tail).
    setoid_rewrite bind_assoc.
    setoid_rewrite lens_put_get.
    rewrite confined_put; [ | apply confined_neutral; typeclasses eauto ].
    apply bind_extensional. intros [].
    repeat rewrite extr_spec.

    destruct (f a (nAfter_head n a) Ha) as [x|]; smon_rewrite.
    cbn.
    unfold memoryAfter_tail.
    set (ov := fromMem _).
    destruct ov as [v|]; smon_rewrite.
Qed.
