From iVM Require Export Restr Mon.
From iVM Require Import DSet.
Import DSetNotations.

Unset Suggest Proof Using.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.


(** ** Images *)

Local Open Scope N.

Record Image (C: Type) :=
  mkImage {
      width: N;
      height: N;
      pixel (x: N) (Hx: x < width) (y: N) (Hy: y < height): C;
    }.

Arguments width {_} _.
Arguments height {_} _.
Arguments pixel {_} _ {_} Hx {_} Hy.

Definition noImage {C}: Image C.
  refine {|
      width := 0;
      height := 0;
      pixel x Hx y Hy := _;
    |}.
  lia.
Defined.

Local Definition image_telescope {C} (img: Image C) :
  sigma(fun w => sigma(fun h => forall x (Hx: x<w) y (Hy: y<h), C)) :=
  match img with @mkImage _ w h p => sigmaI _ w (sigmaI _ h p) end.

Lemma inj_right_image {C} {w h p p'} :
  {|width:=w; height:=h; pixel:=p|} = {|width:=w; height:=h; pixel:=p'|} :> Image C
  -> p = p'.
Proof.
  intros Hi.
  match type of Hi with
  | ?i = ?i' => assert (image_telescope i = image_telescope i') as Ht;
                 [f_equal; exact Hi | ]
  end.
  unfold image_telescope in Ht.
  do 2 derive Ht (EqDec.inj_right_sigma _ _ _ Ht).
  exact Ht.
Qed.

Definition updatePixel {C} (x y: N) (c: C) (im: Image C) : Image C :=
{|
  width := width im;
  height := height im;
  pixel x' Hx y' Hy :=
    if decide ((x' = x) /\ (y' = y))
    then c
    else pixel im Hx Hy
|}.


(** ** [Z]-actions *)

Local Open Scope Z.

Class Z_action {X} (f: Z -> X -> X) : Prop :=
{
  Z_action_zero x : f 0 x = x;
  Z_action_add z z' x : f (z + z') x = f z' (f z x);
}.

Local Notation "0" := 0%nat.


(** ** Machine parameters

Abstractions makes working with Coq much easier. *)

Module Type MachineParameters.
  Parameter Inline Addr: Type.

  (** In combination with [Existing Instance] this works much better
  than [Declare Instance] for some reason. *)
  Parameter Inline H_eqdec: EqDec Addr.
  Parameter Inline available: Addr -> bool.
  Parameter Inline offset: Z -> Addr -> Addr.
  Parameter Inline offset_action: Z_action offset.
  Parameter Inline Cell: Type.

  Parameter Inline InputColor: Type.
  Parameter Inline allInputImages: list (Image InputColor).

  Parameter Inline OutputColor: Type.
  Parameter Inline Char: Type.
  Parameter Inline Byte: Type.
  Parameter Inline Sample: Type.
End MachineParameters.

Module Core (MP: MachineParameters).

  Export MP.

  Definition Cells := vector Cell.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Record Sound := mkSound
  {
    rate: N;
    samples (Hr: rate <> 0) : list (Sample * Sample); (* reversed *)
  }.

  Record OutputFrame := mkFrame
  {
    image: Image OutputColor;
    sound: Sound;
    chars: list Char;  (* reversed *)
    bytes: list Byte;  (* reversed *)
  }.

  Class MachineParams1 :=
  {
    State: Type;

    MEM: Lens State Memory;
    PC: Lens State Addr;
    SP: Lens State Addr;

    INP: Lens State N; (* Index of current input frame. *)

    (** The following lists all have the latest element first. *)
    OUT_CHARS : Lens State (list Char);
    OUT_BYTES : Lens State (list Byte);
    OUT_SOUND : Lens State Sound;
    OUT_IMAGE : Lens State (Image (option OutputColor));

    LOG: Lens State (list OutputFrame);

    (** Pairwise independent lenses

    We choose the pairs with MEM and OUT_IMAGE on the left to avoid relying
    on the symmetry of [Independent] later (which easily leads to inifinite
    loops). *)

    independent_MEM_IMAGE: Independent MEM OUT_IMAGE;
    independent_MEM_BYTES: Independent MEM OUT_BYTES;
    independent_MEM_CHARS: Independent MEM OUT_CHARS;
    independent_MEM_SOUND: Independent MEM OUT_SOUND;
    independent_MEM_LOG:   Independent MEM LOG;
    independent_MEM_INP:   Independent MEM INP;
    independent_MEM_PC:    Independent MEM PC;
    independent_MEM_SP:    Independent MEM SP;

    independent_IMAGE_BYTES: Independent OUT_IMAGE OUT_BYTES;
    independent_IMAGE_CHARS: Independent OUT_IMAGE OUT_CHARS;
    independent_IMAGE_SOUND: Independent OUT_IMAGE OUT_SOUND;
    independent_IMAGE_LOG:   Independent OUT_IMAGE LOG;
    independent_IMAGE_INP:   Independent OUT_IMAGE INP;
    independent_IMAGE_PC:    Independent OUT_IMAGE PC;
    independent_IMAGE_SP:    Independent OUT_IMAGE SP;

    independent_BYTES_CHARS: Independent OUT_BYTES OUT_CHARS;
    independent_BYTES_SOUND: Independent OUT_BYTES OUT_SOUND;
    independent_BYTES_LOG:   Independent OUT_BYTES LOG;
    independent_BYTES_INP:   Independent OUT_BYTES INP;
    independent_BYTES_PC:    Independent OUT_BYTES PC;
    independent_BYTES_SP:    Independent OUT_BYTES SP;

    independent_CHARS_SOUND: Independent OUT_CHARS OUT_SOUND;
    independent_CHARS_LOG:   Independent OUT_CHARS LOG;
    independent_CHARS_INP:   Independent OUT_CHARS INP;
    independent_CHARS_PC:    Independent OUT_CHARS PC;
    independent_CHARS_SP:    Independent OUT_CHARS SP;

    independent_SOUND_LOG: Independent OUT_SOUND LOG;
    independent_SOUND_INP: Independent OUT_SOUND INP;
    independent_SOUND_PC:  Independent OUT_SOUND PC;
    independent_SOUND_SP:  Independent OUT_SOUND SP;

    independent_LOG_INP: Independent LOG INP;
    independent_LOG_PC:  Independent LOG PC;
    independent_LOG_SP:  Independent LOG SP;

    independent_INP_PC: Independent INP PC;
    independent_INP_SP: Independent INP SP;

    independent_PC_SP: Independent PC SP;
  }.

 Section core_section.

  Context {MP1: MachineParams1}.

  Global Existing Instance independent_MEM_IMAGE.
  Global Existing Instance independent_MEM_BYTES.
  Global Existing Instance independent_MEM_CHARS.
  Global Existing Instance independent_MEM_SOUND.
  Global Existing Instance independent_MEM_LOG.
  Global Existing Instance independent_MEM_INP.
  Global Existing Instance independent_MEM_PC.
  Global Existing Instance independent_MEM_SP.
  Global Existing Instance independent_IMAGE_BYTES.
  Global Existing Instance independent_IMAGE_CHARS.
  Global Existing Instance independent_IMAGE_SOUND.
  Global Existing Instance independent_IMAGE_LOG.
  Global Existing Instance independent_IMAGE_INP.
  Global Existing Instance independent_IMAGE_PC.
  Global Existing Instance independent_IMAGE_SP.
  Global Existing Instance independent_BYTES_CHARS.
  Global Existing Instance independent_BYTES_SOUND.
  Global Existing Instance independent_BYTES_LOG.
  Global Existing Instance independent_BYTES_INP.
  Global Existing Instance independent_BYTES_PC.
  Global Existing Instance independent_BYTES_SP.
  Global Existing Instance independent_CHARS_SOUND.
  Global Existing Instance independent_CHARS_LOG.
  Global Existing Instance independent_CHARS_INP.
  Global Existing Instance independent_CHARS_PC.
  Global Existing Instance independent_CHARS_SP.
  Global Existing Instance independent_SOUND_LOG.
  Global Existing Instance independent_SOUND_INP.
  Global Existing Instance independent_SOUND_PC.
  Global Existing Instance independent_SOUND_SP.
  Global Existing Instance independent_LOG_INP.
  Global Existing Instance independent_LOG_PC.
  Global Existing Instance independent_LOG_SP.
  Global Existing Instance independent_INP_PC.
  Global Existing Instance independent_INP_SP.
  Global Existing Instance independent_PC_SP.

  Class MachineParams2 :=
  {
    M: Type -> Type;
    H_mon: SMonad State M;
  }.

  Context {MP2: MachineParams2}.

  Global Existing Instance H_eqdec.
  Global Existing Instance offset_action.
  Global Existing Instance H_mon.

  Existing Instance submixer_fst.


  (** *** Addressable  *)

  (** The address space may consist of multiple disjoint pieces. The
      following predicate states that each piece containing [a] has at
      least [n] distinct addresses. *)
  Definition addressable (n: nat) a : Prop := forall i, 0 < i < n -> offset i a <> a.

  Proposition addressable_neg {n a} (Hn: addressable n a) : forall i, 0 < i < n -> offset (-i) a <> a.
  Proof.
    intros i Hi H.
    apply (Hn i Hi).
    rewrite <- H at 1.
    rewrite <- Z_action_add.
    lia_rewrite (-i + i = 0%Z).
    apply Z_action_zero.
  Qed.

  Proposition addressable_le {n a} (Hn: addressable n a) {m: nat} (Hm: m <= n):
    addressable m a.
  Proof.
    unfold addressable in *.
    intros. apply Hn. lia.
  Qed.

  Proposition addressable_offset {n a} (Hn: addressable n a) z :
    addressable n (offset z a).
  Proof.
    intros i Hi.
    rewrite <- Z_action_add.
    intros Ha.
    apply (Hn i Hi).
    apply (f_equal (offset (-z))) in Ha.
    revert Ha.
    setoid_rewrite <- Z_action_add.
    lia_rewrite (z + i + -z = i).
    lia_rewrite (z + -z = 0%Z).
    now rewrite Z_action_zero.
  Qed.

  Ltac addressable_tac :=
    try match goal with
        | H : addressable ?n ?a |- addressable ?m ?b =>
          try apply addressable_offset;
          apply (addressable_le H (m:=m));
          repeat (simpl length
                  || rewrite app_length
                  || rewrite rev_length);
          repeat rewrite length_to_list;
          try lia
        end.


  (** *** Decidable subsets of the memory *)

  Definition Memory' u := @restr Addr (fun a => available a -> option Cell) u.

  Instance MEM' u : Lens State (restr u) :=
    (restrLens u) ∘ MEM.

  Proposition subset_mem u : (MEM' u | MEM).
  Proof.
    unfold MEM'. typeclasses eauto.
  Qed.

  Global Instance subset_mem2 f {Hf: (MEM | f)} u : (MEM' u | f).
  Proof.
    transitivity MEM.
    - apply subset_mem.
    - exact Hf.
  Qed.

  Instance MEM'' a : Lens State (available a -> option Cell) :=
    (pointLens a) ∘ MEM.

  Proposition point_mem a : (MEM'' a | MEM).
  Proof.
    unfold MEM''. typeclasses eauto.
  Qed.

  Global Instance point_mem2 f {Hf: (MEM | f)} a : (MEM'' a | f).
  Proof.
    transitivity MEM.
    - apply point_mem.
    - exact Hf.
  Qed.

  Global Instance point_mem' {a u} (Hau: a ∈ u) : (MEM'' a | MEM' u).
  Proof.
    unfold MEM'', MEM'.
    apply sublens_comp.
    refine (pointLens_sublens Hau).
  Qed.

  Global Instance point_mem'' {a} : (MEM'' a | MEM' !{a}) :=
    point_mem' DSet.refl.

  Global Instance point_independent {a a'} (H:a<>a') :
    Independent (MEM'' a) (MEM'' a').
  Proof.
    unfold MEM''.
    apply composite_independent_r.
    refine (pointLens_independent H).
  Qed.


  (** *** Extract the boxed element from an [option] type or fail. *)

  Definition extr {X} (ox: option X) : M X :=
    match ox with
    | Some x => ret x
    | None => err
    end.
  Definition extr_spec := unfolded_eq (@extr).

  Global Instance confined_extr
         {X} (ox: option X) : Confined fstMixer (extr ox).
  Proof.
    typeclasses eauto.
  Qed.

  Global Opaque extr.


  (** ** [load] and [store] *)

  (** *** [load] *)

  Definition load (a: Addr): M Cell :=
    let* Ha := assume (available a) in
    let* c := get' (MEM'' a) in
    extr (c Ha).

  Definition load_spec'' := unfolded_eq load.

  Proposition load_spec a :
    load a = let* Ha := assume (available a) in
             let* mem := get' MEM in
             extr (mem a Ha).
  Proof.
    unfold load.
    destruct (decide (available a));
      repeat rewrite get_spec;
      smon_rewrite.
  Qed.

  Global Instance confined_load {a} : Confined (MEM'' a) (load a).
  Proof.
    typeclasses eauto.
  Qed.

  (* TODO: Make global opaque *)
  Opaque load.


  (** *** [store] *)

  Definition store (a: Addr) (x: Cell) : M unit :=
    assume (available a);;
    put' (MEM'' a) (fun _ => Some x).

  Definition store_spec'' := unfolded_eq store.

  Proposition store_spec a x :
    store a x = assume (available a);;
                let* s := get' MEM in
                let s' a' H := if decide (a = a') then Some x else s a' H in
                put' MEM s'.
  Proof.
    unfold store.
    repeat rewrite get_spec.
    repeat rewrite put_spec.
    destruct (decide (available a));
      smon_rewrite.
    apply bind_extensional. intro s.
    f_equal. cbn. unfold compose. f_equal.
    extensionality a'.
    destruct (decide _) as [[]|_];
      reflexivity.
  Qed.

  (* TODO: [unfold compose] is annoying. Use notation instead? *)

  Global Instance confined_store a x : Confined (MEM'' a) (store a x).
  Proof.
    typeclasses eauto.
  Qed.

  (* TODO: Make global opaque *)
  Opaque store.

  (** *** Reordering load and store operations *)

  Lemma store_load a x {Y} (f: unit -> Cell -> M Y) : let* u := store a x in
                                                 let* x' := load a in
                                                 f u x' = store a x;;
                                                          f tt x.
  Proof.
    rewrite
      store_spec'', load_spec'',
      extr_spec.
    smon_rewrite.
    destruct (decide _);
      smon_rewrite.
  Qed.

  Lemma store_store a a' x x' Y (H: a <> a') (f: unit -> unit -> M Y) :
    let* u := store a x in
    let* v := store a' x' in
    f u v = let* v := store a' x' in
            let* u := store a x in
            f u v.
  Proof.
    rewrite store_spec''.
    destruct (decide (available a));
      destruct (decide (available a'));
      smon_rewrite.
    rewrite <- flip_put_put.
    - reflexivity.
    - apply (point_independent H).
  Qed.


  (** ** [loadMany] and [next] *)

  Open Scope vector.

  Proposition offset_inc (n: nat) a : offset n (offset 1 a) = offset (S n) a.
  Proof.
    setoid_rewrite <- Z_action_add.
    f_equal. lia.
  Qed.

  Definition nAfter (n: nat) (a: Addr) : DSet Addr :=
    def (fun a' => exists i, (i<n)%nat /\ offset i a = a').

  Proposition nAfter_head n a : a ∈ nAfter (S n) a.
  Proof.
    apply def_spec. exists 0. split.
    - lia.
    - apply Z_action_zero.
  Qed.

  (* TODO: Repeat after section if necessary. *)
  Hint Extern 3 (_ ∈ nAfter _ _) => rapply nAfter_head : typeclass_instances.

  Proposition nAfter_succ n a : nAfter n (offset 1 a) ⊆ nAfter (S n) a.
  Proof.
    unfold subset.
    intros a'.
    unfold nAfter.
    setoid_rewrite def_spec.
    intros [i [Hi Ho]].
    exists (S i).
    split.
    - lia.
    - rewrite <- offset_inc. exact Ho.
  Qed.

  Hint Extern 3 (_ ⊆ nAfter _ _) => rapply nAfter_succ : typeclass_instances.

  Definition nBefore n a := nAfter n (offset (-n) a).

  (* TODO: noind is used to circumvent what appears to be an Equation bug. *)
  Equations(noind) loadMany (n: nat) (_: Addr): M (Cells n) :=
    loadMany 0 _ := ret [];
    loadMany (S n) a :=
      let* x := load a in
      let* r := loadMany n (offset 1 a) in
      ret (x :: r).

  Global Instance subset_mem' {u v} {Huv: u ⊆ v} : (MEM' u | MEM' v).
  Proof.
    apply sublens_comp, submixer_subset.
    exact Huv.
  Qed.

  Global Instance confined_loadMany n a : Confined (MEM' (nAfter n a)) (loadMany n a).
  Proof.
    revert a.
    induction n;
      intros a;
      simp loadMany.
    - typeclasses eauto.
    - specialize (IHn (offset 1 a)).
      typeclasses eauto.
  Qed.

  (** [simp] does not work under binders (yet), and (for some reason)
      [setoid_rewrite] requires an unneccessary Addr argument. *)
  Ltac simp_loadMany := rewrite_strat (outermost (hints loadMany)).

  Equations(noind) next (n: nat) : M (Cells n) :=
    next 0 := ret [];
    next (S n) :=
      let* pc := get' PC in
      let* x := load pc in
      put' PC (offset 1 pc);;
      let* r := next n in
      ret (x :: r).

  Lemma next_spec n : next n = let* pc := get' PC in
                               put' PC (offset n pc);;
                               loadMany n pc.
  Proof.
    induction n; simp next.
    - simpl (offset _ _).
      setoid_rewrite Z_action_zero.
      simp_loadMany.
      smon_rewrite.
    - rewrite IHn. clear IHn.
      simp_loadMany.
      smon_rewrite.
      setoid_rewrite offset_inc.
      setoid_rewrite (confined_load _ _ _ _).
      reflexivity.
  Qed.

  Global Instance confined_next n : Confined (MEM * PC) (next n).
  Proof.
    rewrite next_spec.
    typeclasses eauto.
  Qed.

  (* TODO: Does this have a useful form? *)
  Global Instance confined_next' a n :
    Confined (MEM' (nAfter n a) * PC)
             (put' PC a;; next n).
  Proof.
    rewrite next_spec.
    smon_rewrite.
    typeclasses eauto.
  Qed.


  (** *** POP *)

  (** Pop a single cell. Later we will always pop multiple cells at once.
      Instead of marking the freed stack as undefined here, we will
      express this later in the corresponding [Cert]s. *)
  Definition pop : M Cell :=
    let* sp := get' SP in
    put' SP (offset 1 sp);;
    load sp.
  Definition pop_spec := unfolded_eq (pop).

  Global Instance confined_pop : Confined (MEM * SP) pop.
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance confined_pop' sp :
    Confined (MEM'' sp * SP) (put' SP sp;;
                              pop).
  Proof.
    smon_rewrite.
    typeclasses eauto.
  Qed.

  Global Opaque pop.

  Equations(noind) popMany (n: nat): M (Cells n) :=
    popMany 0 := ret [];
    popMany (S n) := let* x := pop in
                     let* r := popMany n in
                     ret (x :: r).

  (* TODO: Useful? *)
  Proposition popMany_action m n :
    popMany (m + n) = let* u := popMany m in
                      let* v := popMany n in
                      ret (u ++ v).
  Proof.
    induction m.
    - simp popMany. smon_rewrite.
    - cbn. simp popMany.
      rewrite IHm. clear IHm.
      smon_rewrite.
  Qed.

  Lemma popMany_spec n : popMany n = let* sp := get' SP in
                                     put' SP (offset n sp);;
                                     loadMany n sp.
  Proof.
    induction n; simp popMany; simp_loadMany.
    - smon_rewrite.
      setoid_rewrite Z_action_zero.
      smon_rewrite.
    - rewrite IHn. clear IHn.
      rewrite pop_spec.
      smon_rewrite.
      setoid_rewrite (confined_load _ _ _ _).
      smon_rewrite.
      setoid_rewrite offset_inc.
      smon_rewrite.
  Qed.

  Global Instance confined_popMany n : Confined (MEM * SP) (popMany n).
  Proof.
    rewrite popMany_spec.
    typeclasses eauto.
  Qed.

  Global Instance confined_popMany' sp n :
    Confined (MEM' (nAfter n sp) * SP) (put' SP sp;;
                                        popMany n).
  Proof.
    rewrite popMany_spec.
    smon_rewrite.
    typeclasses eauto.
  Qed.

  Close Scope vector.


  (** ** [storeMany] *)

  Equations storeMany (_: Addr) (_: list Cell) : M unit :=
    storeMany _ [] := ret tt;
    storeMany a (x :: u) :=
      store a x;;
      storeMany (offset 1 a) u.

  (** Cf. [simp_loadMany] *)
  Ltac simp_storeMany := rewrite_strat (outermost (hints storeMany)).

  Proposition storeMany_one a x : storeMany a [x] = store a x.
  Proof.
    simp storeMany. smon_rewrite.
  Qed.

  Lemma storeMany_action a u v :
    storeMany a (u ++ v) = storeMany a u;;
                           storeMany (offset (length u) a) v.
  Proof.
    revert a.
    induction u as [|x u IH]; intros a.
    - cbn. simp storeMany. rewrite Z_action_zero. smon_rewrite.
    - simpl length.
      simpl app.
      simp storeMany.
      rewrite IH. clear IH.
      smon_rewrite.
      setoid_rewrite <- Z_action_add.
      lia_rewrite (1 + length u = S (length u)).
      reflexivity.
  Qed.

  Global Instance confined_storeMany a u :
    Confined (MEM' (nAfter (length u) a))
             (storeMany a u).
  Proof.
    (* TODO: Very similar to the proof of [confined_loadMany].*)
    revert a.
    induction u as [|x u IH];
      intros a;
      simp storeMany.
    - typeclasses eauto.
    - specialize (IH (offset 1 a)).
      typeclasses eauto.
  Qed.

  Lemma storeMany_rev a x u :
    storeMany a (rev (x :: u)) = storeMany a (rev u);;
                                store (offset (length u) a) x.
  Proof.
    induction u as [|y u IH];
      simpl rev;
      simpl length;
      simp storeMany;
      smon_rewrite.
    - rewrite Z_action_zero. reflexivity.
    - repeat setoid_rewrite storeMany_action.
      smon_rewrite.
      setoid_rewrite storeMany_one.
      setoid_rewrite app_length.
      simpl length.
      setoid_rewrite rev_length.
      lia_rewrite (length u + 1 = S (length u))%nat.
      reflexivity.
  Qed.

  Lemma storeMany_equation_2' a x u (H: addressable (S (length u)) a) :
    storeMany a (x :: u) = storeMany (offset 1 a) u;;
                          store a x.
  Proof.
    rewrite <- (rev_involutive u).
    rewrite <- (rev_length u) in H.
    revert H.
    generalize (rev u). clear u. intros u H.
    simp storeMany.
    revert a H x.
    induction u as [|y u IH];
      intros a H x;
      simp storeMany;
      smon_rewrite.

    cbn in H.
    rewrite storeMany_rev.
    setoid_rewrite <- bind_assoc.
    setoid_rewrite IH; [ | addressable_tac ].

    smon_rewrite.
    apply bind_extensional. intros [].
    setoid_rewrite <- bind_ret_tt.
    setoid_rewrite bind_assoc.
    rewrite store_store.
    - reflexivity.
    - apply not_eq_sym.
      rewrite <- Z_action_add.
      apply H.
      lia.
  Qed.

  Lemma storeMany_action' a u v (H: addressable (length u + length v) a) :
    storeMany a (u ++ v) =
    storeMany (offset (length u) a) v;; storeMany a u.
  Proof.
    revert a H.
    induction u as [|x u IH]; intros a H.
    - cbn. rewrite Z_action_zero. simp storeMany. smon_rewrite.
    - simpl (_ ++ _).
      setoid_rewrite storeMany_equation_2'.
      rewrite IH.
      rewrite offset_inc.
      simpl length.
      smon_rewrite.
      all: addressable_tac.
  Qed.

  Lemma storeMany_loadMany' a n (u: Cells n) {Y} (f: unit -> Cells n -> M Y) :
    addressable n a ->
      let* x := storeMany a (to_list u) in
      let* v := loadMany n a in
      f x v =
        storeMany a (to_list u);;
        f tt u.
  Proof.
    intros H.
    smon_rewrite.
    revert a H; induction n; intros a H.
    - dependent elimination u. cbn.
      simp storeMany loadMany. smon_rewrite.
    - dependent elimination u as [Vector.cons (n:=n) x u]. simp to_list.
      rewrite storeMany_equation_2' at 1; [|addressable_tac].
      simp loadMany.
      smon_rewrite.
      rewrite store_load.
      rewrite <- bind_assoc.
      setoid_rewrite <- storeMany_equation_2'; [|addressable_tac].
      simp storeMany.
      smon_rewrite.
      apply bind_extensional. intros [].
      rewrite (IHn u (fun _ v => f tt (x :: v)%vector)).
      + smon_rewrite.
      + addressable_tac.
  Qed.


  (** ** [push] and [pushMany] *)

  (** Push a single cell *)
  Definition push (x: Cell) : M unit :=
    let* sp := get' SP in
    let a := offset (- 1) sp in
    put' SP a;;
    store a x.
  Definition push_spec := unfolded_eq (push).

  Global Instance confined_push x : Confined (MEM * SP) (push x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance confined_push' sp x :
    Confined (MEM'' (offset (-1) sp) * SP) (put' SP sp;;
                                            push x).
  Proof.
    smon_rewrite.
    typeclasses eauto.
  Qed.

  Global Opaque push.

  (** NB: Stores the elements in reversed order. *)
  Equations(noind) pushManyR (u: list Cell): M unit :=
    pushManyR [] := ret tt;
    pushManyR (x :: u) := push x;;
                         pushManyR u.

  Global Instance confined_pushManyR u :
    Confined (MEM * SP) (pushManyR u).
  Proof.
    induction u;
      simp pushManyR;
      typeclasses eauto.
  Qed.

  Proposition nBefore_zero n a : offset (-1) a ∈ nBefore (S n) a.
  Proof.
    unfold nBefore, nAfter.
    rewrite def_spec, bounded_ex_succ.
    left. setoid_rewrite <- Z_action_add.
    f_equal. lia.
  Qed.

  Hint Extern 3 (_ ∈ nBefore _ _) => rapply nBefore_zero : typeclass_instances.

  Proposition nBefore_succ n a : nBefore n (offset (-1) a) ⊆ nBefore (S n) a.
  Proof.
    unfold nBefore, nAfter.
    intros a'.
    repeat rewrite def_spec.
    repeat setoid_rewrite <- Z_action_add.
    rewrite bounded_ex_succ.
    lia_rewrite (forall i, -1 + (- n + i) = - S n + i).
    intros H. right. exact H.
  Qed.

  Hint Extern 3 (_ ⊆ nBefore _ _) => rapply nBefore_succ : typeclass_instances.

  Global Instance confined_pushManyR' sp u :
    Confined (MEM' (nBefore (length u) sp) * SP)
             (put' SP sp;;
              pushManyR u).
  Proof.
    revert sp.
    induction u as [|x r IH];
      intros sp;
      (* Too slow: simp pushManyR; *)
      autorewrite with pushManyR;
    [ typeclasses eauto | ].

    simpl length. rewrite push_spec. smon_rewrite.

    setoid_rewrite (confined_store _ _ _ _ _).
    apply confined_bind; [ typeclasses eauto | ].
    intros [].
    (* [typeclasses eauto] needs help, since it is not able to deconstruct IH. *)
    apply (confined_sub (IH (offset (-1) sp))).
    typeclasses eauto.
  Qed.

 Lemma pushManyR_action u v : pushManyR (u ++ v) = pushManyR u;; pushManyR v.
  Proof.
    revert v.
    induction u as [|x u IH];
      intros v;
      cbn;
      simp pushManyR;
      smon_rewrite.
    rewrite IH.
    reflexivity.
  Qed.

  (** Stores the elements correct order. *)
  Definition pushMany u := pushManyR (rev u).

  Corollary pushMany_action u v : pushMany (u ++ v) = pushMany v;; pushMany u.
  Proof.
    unfold pushMany.
    rewrite rev_app_distr.
    apply pushManyR_action.
  Qed.

  Proposition confined_swap
              {A} {LA: Lens State A} {X} {ma: M X} (Ha: Confined LA ma)
              {B} {LB: Lens State B} {Y} {mb: M Y} (Hb: Confined LB mb)
              {Hi: Independent LA LB} {Z} (f: X -> Y -> M Z) :
    let* x := ma in
    let* y := mb in
    f x y = let* y := mb in
            let* x := ma in
            f x y.
  Proof.
    setoid_rewrite <- Ha.
    - reflexivity.
    - Hint Mode Neutral - - - - - - : typeclass_instances.
    Hint Mode Confined - - - - - - : typeclass_instances.
    Existing Instance lensmonad.
    Hint Mode Lens - - : typeclass_instances.
    Set Typeclasses Depth 1000.
    (* Set Typeclasses Debug. *)
    typeclasses eauto.
  Qed.

  Lemma pushMany_alt u (H: forall a, addressable (length u) a) :
    pushMany u = let* sp := get' SP in
                 let a := offset (- List.length u) sp in
                 put' SP a;;
                 storeMany a u.
  Proof.
    (* TODO: AUTOMATE! *)
    induction u as [|x u IH].
    - unfold pushMany. cbn.
      setoid_rewrite Z_action_zero.
      simp pushManyR.
      simp_storeMany.
      smon_rewrite.

    - change (x :: u) with ([x] ++ u).
      rewrite pushMany_action.
      smon_rewrite.
      set (f := offset (- length ([x] ++ u))).
      rewrite IH; [|intros sp; specialize (H sp); addressable_tac].
      clear IH.
      unfold pushMany.
      simpl rev.
      simp pushManyR.
      rewrite push_spec.
      smon_rewrite.
      apply bind_extensional. intros sp.
      setoid_rewrite <- (confined_storeMany _ _ _ _ _).
      setoid_rewrite <- (confined_storeMany _ _ _ _ _).
      smon_rewrite.
      setoid_rewrite <- Z_action_add.
      subst f.
      apply bind_extensional'.
      + f_equal. f_equal. cbn. lia.
      + intros [].
        specialize (H sp).
        setoid_rewrite (storeMany_action' _ [x] u); [|addressable_tac].
        simp storeMany.
        smon_rewrite.
        apply bind_extensional'.
        * f_equal. rewrite <- Z_action_add.
          f_equal. rewrite app_length.
          simpl length. lia.
        * intros [].
          f_equal.
          f_equal.
          rewrite app_length.
          simpl length.
          lia.
  Qed.

  Close Scope Z. (* Back to N for the rest of this file. *)


  (** ** Input *)

  Local Definition Input := Image InputColor.

  Definition readFrame (i: N) : M (N * N) :=
    put' INP i;;
    let img := nth (N.to_nat i) allInputImages noImage in
    ret (width img, height img).

  Definition readFrame_spec := unfolded_eq (readFrame).

  Global Opaque readFrame.

  Global Instance confined_readFrame i : Confined INP (readFrame i).
  Proof.
    rewrite readFrame_spec.
    typeclasses eauto.
  Qed.

  Definition readPixel (x y : N) : M InputColor :=
    let* i := get' INP in
    let img := nth (N.to_nat i) allInputImages noImage in
    let* Hx := assume (x < width img) in
    let* Hy := assume (y < height img) in
    ret (pixel img Hx Hy).

  Definition readPixel_spec := unfolded_eq (readPixel).

  Global Opaque readPixel.

  Global Instance confined_readPixel x y : Confined INP (readPixel x y).
  Proof.
    rewrite readPixel_spec.
    typeclasses eauto.
  Qed.


  (** ** Current output *)

  Definition extendSamples (l r: Sample) (sn: Sound) :=
  {|
    rate := rate sn;
    samples Hr := (l, r) :: (samples sn Hr);
  |}.

  Definition putChar (c: Char) : M unit :=
    let* chars := get' OUT_CHARS in
    put' OUT_CHARS (cons c chars).
  Definition putChar_spec := unfolded_eq (putChar).
  Global Opaque putChar.
  Global Instance confined_putChar c : Confined OUT_CHARS (putChar c).
  Proof. rewrite putChar_spec. typeclasses eauto. Qed.

  Definition putByte (b: Byte) : M unit :=
    let* bytes := get' OUT_BYTES in
    put' OUT_BYTES (cons b bytes).
  Definition putByte_spec := unfolded_eq (putByte).
  Global Opaque putByte.
  Global Instance confined_putByte c : Confined OUT_BYTES (putByte c).
  Proof. rewrite putByte_spec. typeclasses eauto. Qed.

  Definition addSample (l r: Sample) : M unit :=
    let* samples := get' OUT_SOUND in
    put' OUT_SOUND (extendSamples l r samples).
  Definition addSample_spec := unfolded_eq (addSample).
  Global Opaque addSample.
  Global Instance confined_addSample l r : Confined OUT_SOUND (addSample l r).
  Proof. rewrite addSample_spec. typeclasses eauto. Qed.

  Definition setPixel (x y: N) (c: OutputColor) : M unit :=
    let* img := get' OUT_IMAGE in
    assume (x < width img);;
    assume (y < height img);;
    put' OUT_IMAGE (updatePixel x y (Some c) img).
  Definition setPixel_spec := unfolded_eq (setPixel).
  Global Opaque setPixel.
  Global Instance confined_setPixel x y c : Confined OUT_IMAGE (setPixel x y c).
  Proof. rewrite setPixel_spec. typeclasses eauto. Qed.


  (** ** Output log *)

  Definition image_complete (img: Image (option OutputColor)) : Prop :=
    forall x (Hx: x < width img) y (Hy: y < height img), pixel img Hx Hy.

  Definition extractImage (img: Image (option OutputColor)) : M (Image OutputColor) :=
    let* H_complete := assume (image_complete img) in
    ret {|
        width := width img;
        height := height img;
        pixel x Hx y Hy := extract (H_complete x Hx y Hy);
      |}.
  Definition extractImage_spec := unfolded_eq (extractImage).

  Global Instance extractImage_confined img : Confined fstMixer (extractImage img).
  Proof. typeclasses eauto. Qed.

  Global Opaque extractImage.

  Definition newFrame (w r h: N) : M unit :=
    let* bytes := get' OUT_BYTES in
    let* chars := get' OUT_CHARS in
    let* sound := get' OUT_SOUND in
    let* img := get' OUT_IMAGE in
    let* image := extractImage img in
    let frame :=
        {|
          bytes := bytes;
          chars := chars;
          sound := sound;
          image := image;
        |} in
    let* current := get' LOG in
    put' LOG (frame :: current);;
    put' OUT_BYTES [];;
    put' OUT_CHARS [];;
    put' OUT_SOUND {|
           rate := r;
           samples _ := [];
         |};;
    put' OUT_IMAGE {|
           width := w;
           height := h;
           pixel _ _ _ _ := None;
         |}.
  Definition newFrame_spec := unfolded_eq (newFrame).

  Global Instance confined_newFrame w r h :
    Confined (OUT_IMAGE * OUT_BYTES * OUT_CHARS * OUT_SOUND * LOG)
             (newFrame w r h).
  Proof.
    typeclasses eauto.
  Qed.

  Global Opaque newFrame.

  (****************************)

  Close Scope N.

  Proposition addressable_pred {n a} : addressable (S n) a -> addressable n a.
  Proof.
    intros H. apply (@addressable_le (S n)).
    - exact H.
    - lia.
  Qed.

  (***)

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
    nAvailable n a <-> forall (i:nat), i < n -> available (offset i a).
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
        by_lia (i = 0 \/ 0 < i) as Hor.
        destruct Hor as [HO|HS].
        * subst i. rewrite Z_action_zero. exact H0.
        * specialize (IH1 H1 (i - 1)). by_lia (i - 1 < n) as HH.
          specialize (IH1 HH). revert IH1. rewrite <- Z_action_add.
          lia_rewrite (1 + (i - 1)%nat = i)%Z.
          tauto.
      + constructor.
        * specialize (H 0). rewrite Z_action_zero in H.
          apply H. lia.
        * apply IH2. intros i Hi.
          rewrite <- Z_action_add.
          lia_rewrite (1 + i = S i)%Z.
          apply H. lia.
  Qed.

  Global Instance nAvailable_decidable n a : Decidable (nAvailable n a).
  Proof.
    apply (decidable_transfer (nAvailable_spec n a)).
  Qed.

  Proposition nAvailable_succ n a :
    nAvailable (S n) a <-> available a /\ nAvailable n (offset 1 a).
  Proof.
    split.
    - intros H. dependent elimination H. split; assumption.
    - intros [H0 H1]. constructor; assumption.
  Qed.

  (***)

  Proposition nAfter_disjoint_spec u n a :
    u # nAfter n a <-> forall i, (i<n)%nat -> not (offset i a ∈ u).
  Proof.
    unfold nAfter, disjoint.
    setoid_rewrite def_spec.
    split; intro H.
    - intros i Hi Ho.
      apply (H (offset i a)).
      split.
      + exact Ho.
      + now exists i.
    - intros x [Hx [i [Hi Ha]]].
      apply (H i Hi).
      rewrite Ha.
      exact Hx.
  Qed.

  Global Instance nAfter_disjoint_decidable u n a : Decidable (u # nAfter n a).
  Proof.
    refine (decidable_transfer (nAfter_disjoint_spec _ _ _)).
  Defined.
  
  Proposition not_nAfter_disjoint_spec u n a :
    not (u # nAfter n a) -> exists i, (i<n)%nat /\ offset i a ∈ u.
  Proof.
    rewrite nAfter_disjoint_spec.
    intros H.
    apply bounded_all_neg in H.
    - setoid_rewrite decidable_raa in H. exact H.
    - typeclasses eauto.
  Qed.
  
  Definition not_nAfter_disjoint_evidence u n a (H : not (u # nAfter n a)) :
    { x: Addr | x ∈ u /\ exists i, (i < n)%nat /\ offset i a = x }.
  Proof.
    apply not_nAfter_disjoint_spec in H.
    apply bounded_evidence in H; [ | typeclasses eauto ].
    destruct H as [i [Hi Hu]].
    refine (exist _ (offset i a) _).
    split.
    - exact Hu.
    - now exists i.
  Defined.

  Proposition nAfter_empty a : nAfter 0 a = ∅%DSet.
  Proof.
    apply extensionality.
    intros x.
    unfold nAfter.
    rewrite def_spec.
    transitivity False.
    - split.
      + intros [i [Hi _]]. lia.
      + tauto.
    - set (H := @empty_spec _ x). tauto.
  Qed.

  Hint Rewrite nAfter_empty : nAfter.

  (* TODO: Useful? *)
  Lemma nAfter_action (a: Addr) (m n: nat) :
    nAfter (m + n) a = (nAfter m a ∪ nAfter n (offset m a))%DSet.
  Proof.
    revert a; induction m; intros a.
    - cbn. rewrite nAfter_empty. rewrite Z_action_zero.
      apply extensionality. intro x.
      rewrite union_spec.
      unfold nAfter.
      setoid_rewrite def_spec.
      split.
      + intros H. right. exact H.
      + intros [H|H].
        * contradict H.
        * exact H.

    - apply extensionality. intro x.
      rewrite union_spec.
      unfold nAfter.
      setoid_rewrite def_spec.
      split.
      + intros [i [H1 H2]].
        by_lia (i < S m \/ S m <= i < S m + n)%nat as H.
        destruct H as [H|H].
        * left. exists i. split.
          -- exact H.
          -- exact H2.
        * right. exists (i - S m)%nat. split.
          -- lia.
          -- rewrite <- H2, <- Z_action_add. f_equal. lia.
      + intros [[i [H1 H2]] | [i [H1 H2]]].
        * exists i. split.
          -- lia.
          -- exact H2.
        * exists (S m + i)%nat. split.
          -- lia.
          -- rewrite <- H2, <- Z_action_add. f_equal. lia.
  Qed.

  Proposition nAfter_succ_spec n a x :
    x ∈ nAfter (S n) a <-> x = a \/ x ∈ nAfter n (offset 1 a).
  Proof.
    unfold nAfter. repeat rewrite def_spec. split.
    - intros [i [Hi Hx]].
      by_lia (i = 0 \/ 0 < i) as Hor.
      destruct Hor as [H0|H1].
      + subst i.
        rewrite Z_action_zero in Hx.
        left. symmetry. exact Hx.
      + right. exists (Nat.pred i). split; [lia | ].
        rewrite <- Z_action_add. rewrite <- Hx.
        f_equal. lia.
    - intros [He|[i [Hi Hx]]].
      + subst x. exists 0. split.
        * lia.
        * apply Z_action_zero.
      + exists (S i). split.
        * lia.
        * lia_rewrite (S i = (1 + i)%Z :> Z). rewrite Z_action_add.
          exact Hx.
  Qed.

  Definition nAfter_tail {n a} : nAfter n (offset 1 a) ⊆ nAfter (S n) a.
  Proof.
    intros x.
    by_lia (S n = (1 + n)%nat) as HH.
    rewrite HH, nAfter_action, union_spec.
    right. exact H.
  Defined.

  (***)

  Proposition emptyMem_is_void : MEM' ∅ ≃ fstMixer.
  Proof.
    unfold MEM'.
    rewrite composite_compositeMixer, emptyLens_is_void.
    apply fstMixer_composite.
  Qed.

  Proposition put_void {A} (LA: Lens State A) (H: (LA|fstMixer)) a : put' LA a = ret tt.
  Proof.
    unfold Submixer in H. cbn in H.
    rewrite put_spec. cbn.
    enough (forall s, update s a = s) as Hu.
    - setoid_rewrite Hu. smon_rewrite.
    - intros s. specialize (H s s (update s a)).
      revert H. lens_rewrite. tauto.
  Qed.

  Corollary put_empty f : put' (MEM' ∅) f = ret tt.
  Proof.
    apply put_void.
    clear f.
    rewrite emptyMem_is_void.
    reflexivity.
  Qed.

  (*******)

  Definition memoryAfter_head {n a} (f: Memory' (nAfter (S n) a)) (Ha: available a) : option Cell :=
    f a (nAfter_head n a) Ha.

  Definition memoryAfter_head' {n a} (f: Memory' (nAfter (S n) a)) : option Cell :=
    match decide (available a) with
    | left Ha => memoryAfter_head f Ha
    | _ => None
    end.

  Definition memoryAfter_tail {n a} (f: Memory' (nAfter (S n) a)) :
      Memory' (nAfter n (offset 1 a)) := fun x H Hx => f x (nAfter_tail _ H) Hx.

  Local Open Scope vector.

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

  Proposition toMem_head a x {n} (u: Cells n) (Hadd: addressable (S n) a) (Ha: available a) :
    memoryAfter_head (toMem a (x :: u)) Ha = Some x.
  Proof.
    unfold memoryAfter_head.
    unfold toMem.
    set (fl := findLast _ _).
    (* specialize (Hadd a). *)
    cbn beta in Hadd.
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

  Local Open Scope Z.

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

  Lemma fromMem_toMem a {n} (u: Cells n) (Hadd: addressable n a) (Hav: nAvailable n a) :
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
      + apply addressable_offset. apply (addressable_pred Hadd).
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

  Lemma loadMany_spec_fromMem n a :
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

  (***)

  Lemma storeMany_spec_toMem a {n} (u: Cells n) :
    storeMany a (to_list u) =
      assume' (nAvailable n a);;
      put' (MEM' (nAfter n a)) (toMem a u).
  Proof.
    (* TODO: Simplify / automate *)
    revert a u. induction n; intros a u.
    - dependent elimination u. simp storeMany. unfold toMem.
      rewrite decide_true; [ | constructor ].
      now rewrite nAfter_empty, put_empty, ret_tt_bind.
    - dependent elimination u as [ @Vector.cons x n u ].
      simp to_list storeMany. rewrite IHn. clear IHn.
      rewrite store_spec''.
      rewrite simplify_assume.
      rewrite bind_assoc.
      rewrite <- confined_put; [ | apply confined_neutral; typeclasses eauto ].
      rewrite <- bind_assoc.
      apply bind_extensional'.
      + rewrite <- assume'_and.
        apply assume'_proper.
        symmetry.
        apply nAvailable_succ.
      + intros [].
        repeat rewrite put_spec.
        smon_rewrite.
        apply bind_extensional'; [ reflexivity | intros s ].
        Opaque Z.add. (* TODO*)
        cbn.
        unfold compose.
        rewrite update_update.
        f_equal.
        f_equal.
        extensionality b.

        destruct (decide (b ∈ nAfter (S n) a)) as [Ht|Hf].
        * pose (Ht' := Ht).
          setoid_rewrite nAfter_succ_spec in Ht'.
          destruct Ht' as [Heq|Ho].
          -- subst b.
            rewrite proj_update, eqdec_eqrefl. cbn.
            extensionality Ha.

            destruct (decide _) as [Htt|Hff].
            ++ rewrite <- (toMem_tail a x).
              generalize (toMem a (x :: u)). intros mm.
              unfold memoryAfter_tail.
              f_equal.
              apply membership_unique.
            ++ transitivity (memoryAfter_head (toMem a (x :: u)) Ha).
              ** symmetry. apply toMem_head.
                intros i Hi Ho.
                apply Hff.
                unfold nAfter. rewrite def_spec.
                exists (Z.to_nat (i - 1)).
                split; [ lia | ].
                rewrite <- Z_action_add.
                rewrite nat_N_Z.
                rewrite Z2Nat.id; [ | lia ].
                lia_rewrite (1 + (i - 1) = i).
                exact Ho.
              ** unfold memoryAfter_head.
                f_equal.
                apply membership_unique.
          -- decided Ho.
            rewrite <- (toMem_tail a x).
            unfold memoryAfter_tail.
            extensionality Hb.
            f_equal.
            apply membership_unique.
        * destruct (decide (b ∈ nAfter n (offset 1 a))) as [Htt|Hff].
          -- contradict Hf. rewrite nAfter_succ_spec.
            right. exact Htt.
          -- rewrite proj_update.
            extensionality Hb.
            destruct (decide (a = b)) as [Hab|Hab]; [ | reflexivity ].
            destruct Hab.
            contradict Hf.
            apply nAfter_head.
  Qed.

 End core_section.

End Core.


(** ** Repeat definition that were lost when then section ended. *)

Global Ltac simp_loadMany := rewrite_strat (outermost (hints loadMany)).
