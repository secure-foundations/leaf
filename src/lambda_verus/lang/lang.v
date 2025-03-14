From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings binders.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Open Scope Z_scope.

(** Expressions and vals. *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Declare Scope loc_scope.
Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Inductive base_lit : Set :=
| LitPoison | LitLoc (l : loc) | LitInt (n : Z).
Inductive bin_op : Set :=
| PlusOp | MinusOp | MultOp | LeOp | EqOp | OffsetOp.
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Notation "[ ]" := (@nil binder) : binder_scope.
Notation "a :: b" := (@cons binder a%binder b%binder)
  (at level 60, right associativity) : binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%binder (@cons binder x2%binder
        (..(@cons binder xn%binder (@nil binder))..))) : binder_scope.
Notation "[ x ]" := (@cons binder x%binder (@nil binder)) : binder_scope.

Inductive expr :=
| Var (x : string)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| NdInt
| App (e : expr) (el : list expr)
| Read (o : order) (e : expr)
| Write (o : order) (e1 e2: expr)
| CAS (e0 e1 e2 : expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| Case (e : expr) (el : list expr)
| Fork (e : expr).

Arguments App _%E _%E.
Arguments Case _%E _%E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lit _ | NdInt => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write _ e1 e2 | Free e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read _ e | Alloc e | Fork e => is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Global Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

Inductive val :=
| LitV (l : base_lit)
| RecV (f : binder) (xl : list binder) (e : expr) `{!Closed (f :b: xl +b+ []) e}.

Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | RecV f x e => Rec f x e
  | LitV l => Lit l
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (RecV f xl e) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.

(** The state: heaps of vals*lockstate. *)
Inductive lock_state :=
| WSt | RSt (n : nat).
Definition state := gmap loc (lock_state * val).

(** Evaluation contexts *)
Inductive ectx_item :=
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (e2 : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| ReadCtx (o : order)
| WriteLCtx (o : order) (e2 : expr)
| WriteRCtx (o : order) (v1 : val)
| CasLCtx (e1 e2: expr)
| CasMCtx (v0 : val) (e2 : expr)
| CasRCtx (v0 : val) (v1 : val)
| AllocCtx
| FreeLCtx (e2 : expr)
| FreeRCtx (v1 : val)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx e2 => App e e2
  | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
  | ReadCtx o => Read o e
  | WriteLCtx o e2 => Write o e e2
  | WriteRCtx o v1 => Write o (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | AllocCtx => Alloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | CaseCtx el => Case e el
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | NdInt => NdInt
  | App e el => App (subst x es e) (map (subst x es) el)
  | Read o e => Read o (subst x es e)
  | Write o e1 e2 => Write o (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst' x es <$> subst_l xl esl e
  | _, _ => None
  end.
Arguments subst_l _%binder _ _%E.

Definition subst_v (xl : list binder) (vsl : vec val (length xl))
                   (e : expr) : expr :=
  Vector.fold_right2 (λ b, subst' b ∘ of_val) e _ (list_to_vec xl) vsl.
Arguments subst_v _%binder _ _%E.

Lemma subst_v_eq (xl : list binder) (vsl : vec val (length xl)) e :
  Some $ subst_v xl vsl e = subst_l xl (of_val <$> vec_to_list vsl) e.
Proof.
  revert vsl. induction xl=>/= vsl; inv_vec vsl=>//=v vsl. by rewrite -IHxl.
Qed.

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : base_lit :=
  LitInt $ Z_of_bool b.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

Fixpoint init_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => <[l:=(RSt 0, LitV LitPoison)]>(init_mem (l +ₗ 1) n σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => delete l (free_mem (l +ₗ 1) n σ)
  end.

Inductive lit_eq (σ : state) : base_lit → base_lit → Prop :=
(* No refl case for poison *)
| IntRefl z : lit_eq σ (LitInt z) (LitInt z)
| LocRefl l : lit_eq σ (LitLoc l) (LitLoc l)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 :
    σ !! l1 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2)
| LocUnallocR l1 l2 :
    σ !! l2 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2).

Inductive lit_neq : base_lit → base_lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq (LitInt z1) (LitInt z2)
| LocNeq l1 l2 :
    l1 ≠ l2 → lit_neq (LitLoc l1) (LitLoc l2)
| LocNeqNullR l :
    lit_neq (LitLoc l) (LitInt 0)
| LocNeqNullL l :
    lit_neq (LitInt 0) (LitLoc l).

Inductive bin_op_eval (σ : state) : bin_op → base_lit → base_lit → base_lit → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval σ PlusOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval σ MinusOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpMult z1 z2 :
    bin_op_eval σ MultOp (LitInt z1) (LitInt z2) (LitInt (z1 * z2))
| BinOpLe z1 z2 :
    bin_op_eval σ LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
| BinOpEqTrue l1 l2 :
    lit_eq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z :
    bin_op_eval σ OffsetOp (LitLoc l) (LitInt z) (LitLoc $ l +ₗ z).

Notation stuck_term := (App (Lit (LitInt 0)) []).

Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
| BinOpS op l1 l2 l' σ :
    bin_op_eval σ op l1 l2 l' →
    head_step (BinOp op (Lit l1) (Lit l2)) σ [] (Lit l') σ []
| NdIntS z σ :
    head_step NdInt σ [] (Lit (LitInt z)) σ []
| BetaS f xl e e' el σ:
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    head_step (App (Rec f xl e) el) σ [] e' σ []
| ReadScS l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read ScOrd (Lit $ LitLoc l)) σ [] (of_val v) σ []
| ReadNa1S l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read Na1Ord (Lit $ LitLoc l)) σ
              []
              (Read Na2Ord (Lit $ LitLoc l)) (<[l:=(RSt $ S n, v)]>σ)
              []
| ReadNa2S l n v σ:
    σ !! l = Some (RSt $ S n, v) →
    head_step (Read Na2Ord (Lit $ LitLoc l)) σ
              []
              (of_val v) (<[l:=(RSt n, v)]>σ)
              []
| WriteScS l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write ScOrd (Lit $ LitLoc l) e) σ
              []
              (Lit LitPoison) (<[l:=(RSt 0, v)]>σ)
              []
| WriteNa1S l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write Na1Ord (Lit $ LitLoc l) e) σ
              []
              (Write Na2Ord (Lit $ LitLoc l) e) (<[l:=(WSt, v')]>σ)
              []
| WriteNa2S l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (WSt, v') →
    head_step (Write Na2Ord (Lit $ LitLoc l) e) σ
              []
              (Lit LitPoison) (<[l:=(RSt 0, v)]>σ)
              []
| CasFailS l n e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt n, LitV litl) →
    lit_neq lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ [] (Lit $ lit_of_bool false) σ  []
| CasSucS l e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt 0, LitV litl) →
    lit_eq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              []
              (Lit $ lit_of_bool true) (<[l:=(RSt 0, LitV lit2)]>σ)
              []
(* A succeeding CAS has to detect concurrent non-atomic read accesses, and
   trigger UB if there is one.  In lambdaRust, succeeding and failing CAS are
   not mutually exclusive, so it could happen that a CAS can both fail (and
   hence not be stuck) but also succeed (and hence be racing with a concurrent
   non-atomic read).  In that case, we have to explicitly reduce to a stuck
   state; due to the possibility of failing CAS, we cannot rely on the current
   state being stuck like we could in a language where failing and succeeding
   CAS are mutually exclusive.

   This means that CAS is atomic (it always reducs to an irreducible
   expression), but not strongly atomic (it does not always reduce to a value).

   If there is a concurrent non-atomic write, the CAS itself is stuck: All its
   reductions are blocked.  *)
| CasStuckS l n e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt n, LitV litl) → 0 < n →
    lit_eq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              []
              stuck_term σ
              []
| AllocS n l σ :
    0 < n →
    (∀ m, σ !! (l +ₗ m) = None) →
    head_step (Alloc $ Lit $ LitInt n) σ
              []
              (Lit $ LitLoc l) (init_mem l (Z.to_nat n) σ)
              []
| FreeS n l σ :
    0 < n →
    (∀ m, is_Some (σ !! (l +ₗ m)) ↔ 0 ≤ m < n) →
    head_step (Free (Lit $ LitInt n) (Lit $ LitLoc l)) σ
              []
              (Lit LitPoison) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    head_step (Case (Lit $ LitInt i) el) σ [] e σ []
| ForkS e σ:
    head_step (Fork e) σ [] (Lit LitPoison) σ [e].

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  head_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  head_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; decompose_Forall_hyps;
    simplify_option_eq; by eauto.
Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 →
  vl1 = vl2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by rewrite to_of_val in H1.
  - subst. by rewrite to_of_val in H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto. by apply (inj of_val).
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1 as [| | |v1 vl1 el1| | | | | | | | | |],
           Ki2 as [| | |v2 vl2 el2| | | | | | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
  destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto. congruence.
Qed.

Lemma shift_loc_assoc l n n' : l +ₗ n +ₗ n' = l +ₗ (n + n').
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0 l : l +ₗ 0 = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_assoc_nat l (n n' : nat) : l +ₗ n +ₗ n' = l +ₗ (n + n')%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Global Instance shift_loc_inj l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
Proof. done. Qed.

Lemma lookup_init_mem σ (l l' : loc) (n : nat) :
  l.1 = l'.1 → l.2 ≤ l'.2 < l.2 + n →
  init_mem l n σ !! l' = Some (RSt 0, LitV LitPoison).
Proof.
  intros ?. destruct l' as [? l']; simplify_eq/=.
  revert l. induction n as [|n IH]=> /= l Hl; [lia|].
  assert (l' = l.2 ∨ l.2 + 1 ≤ l') as [->|?] by lia.
  { by rewrite -surjective_pairing lookup_insert. }
  rewrite lookup_insert_ne; last by destruct l; intros ?; simplify_eq/=; lia.
  rewrite -(shift_loc_block l 1) IH /=; last lia. done.
Qed.

Lemma lookup_init_mem_ne σ (l l' : loc) (n : nat) :
  l.1 ≠ l'.1 ∨ l'.2 < l.2 ∨ l.2 + n ≤ l'.2 →
  init_mem l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> /= l Hl; auto.
  rewrite -(IH (l +ₗ 1)); last (simpl; intuition lia).
  apply lookup_insert_ne. intros ->; intuition lia.
Qed.

Definition fresh_block (σ : state) : block :=
  let loclst : list loc := elements (dom _ σ : gset loc) in
  let blockset : gset block := foldr (λ l, ({[l.1]} ∪.)) ∅ loclst in
  fresh blockset.

Lemma is_fresh_block σ i : σ !! (fresh_block σ,i) = None.
Proof.
  assert (∀ (l : loc) ls (X : gset block),
    l ∈ ls → l.1 ∈ foldr (λ l, ({[l.1]} ∪.)) X ls) as help.
  { induction 1; set_solver. }
  rewrite /fresh_block /shift_loc /= -(not_elem_of_dom (D := gset loc)) -elem_of_elements.
  move=> /(help _ _ ∅) /=. apply is_fresh.
Qed.

Lemma alloc_fresh n σ :
  let l := (fresh_block σ, 0) in
  let init := repeat (LitV $ LitInt 0) (Z.to_nat n) in
  0 < n →
  head_step (Alloc $ Lit $ LitInt n) σ [] (Lit $ LitLoc l) (init_mem l (Z.to_nat n) σ) [].
Proof.
  intros l init Hn. apply AllocS. auto.
  - intros i. apply (is_fresh_block _ i).
Qed.

Lemma lookup_free_mem_ne σ l l' n : l.1 ≠ l'.1 → free_mem l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> l ? //=.
  rewrite lookup_delete_ne; last congruence.
  apply IH. by rewrite shift_loc_block.
Qed.

Lemma delete_free_mem σ l l' n :
  delete l (free_mem l' n σ) = free_mem l' n (delete l σ).
Proof.
  revert l'. induction n as [|n IH]=> l' //=. by rewrite delete_commute IH.
Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof.
  revert e X Y. fix FIX 1; destruct e=>X Y/=; try naive_solver.
  - naive_solver set_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert e X. fix FIX 1; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
    repeat case_bool_decide; simplify_eq/=; f_equal;
    try by intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma subst_is_closed X x es e :
  is_closed X es → is_closed (x::X) e → is_closed X (subst x es e).
Proof.
  revert e X. fix FIX 1; destruct e=>X //=; repeat (case_bool_decide=>//=);
    try naive_solver; rewrite ?andb_True; intros.
  - set_solver.
  - eauto using is_closed_weaken with set_solver.
  - eapply is_closed_weaken; first done.
    destruct (decide (BNamed x = f)), (decide (BNamed x ∈ xl)); set_solver.
  - split; first naive_solver. induction el; naive_solver.
  - split; first naive_solver. induction el; naive_solver.
Qed.

Lemma subst'_is_closed X b es e :
  is_closed X es → is_closed (b:b:X) e → is_closed X (subst' b es e).
Proof. destruct b; first done. apply subst_is_closed. Qed.

(* Operations on literals *)
Lemma lit_eq_state σ1 σ2 l1 l2 :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  lit_eq σ1 l1 l2 → lit_eq σ2 l1 l2.
Proof. intros Heq. inversion 1; econstructor; eauto; eapply Heq; done. Qed.

Lemma bin_op_eval_state σ1 σ2 op l1 l2 l' :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  bin_op_eval σ1 op l1 l2 l' → bin_op_eval σ2 op l1 l2 l'.
Proof.
  intros Heq. inversion 1; econstructor; eauto using lit_eq_state.
Qed.

(* Misc *)
Lemma stuck_not_head_step σ e' κ σ' ef :
  ¬head_step stuck_term σ e' κ σ' ef.
Proof. inversion 1. Qed.

(** Equality and other typeclass stuff *)
Global Instance base_lit_dec_eq : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance bin_op_dec_eq : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance un_op_dec_eq : EqDecision order.
Proof. solve_decision. Defined.

Fixpoint expr_beq (e : expr) (e' : expr) : bool :=
  let fix expr_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
    | _, _ => false
    end
  in
  match e, e' with
  | Var x, Var x' => bool_decide (x = x')
  | Lit l, Lit l' => bool_decide (l = l')
  | Rec f xl e, Rec f' xl' e' =>
    bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
    bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | NdInt, NdInt => true
  | App e el, App e' el' | Case e el, Case e' el' =>
    expr_beq e e' && expr_list_beq el el'
  | Read o e, Read o' e' => bool_decide (o = o') && expr_beq e e'
  | Write o e1 e2, Write o' e1' e2' =>
    bool_decide (o = o') && expr_beq e1 e1' && expr_beq e2 e2'
  | CAS e0 e1 e2, CAS e0' e1' e2' =>
    expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
  | Alloc e, Alloc e' | Fork e, Fork e' => expr_beq e e'
  | Free e1 e2, Free e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | _, _ => false
  end.
Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix FIX 1.
    destruct e1 as [| | | | |? el1| | | | | |? el1|],
             e2 as [| | | | |? el2| | | | | |? el2|]; simpl; try done;
  rewrite ?andb_True ?bool_decide_spec ?FIX;
  try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
Qed.
Global Instance expr_dec_eq : EqDecision expr.
Proof.
 refine (λ e1 e2, cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Global Instance val_dec_eq : EqDecision val.
Proof.
 refine (λ v1 v2, cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.

Global Instance expr_inhabited : Inhabited expr := populate (Lit LitPoison).
Global Instance val_inhabited : Inhabited val := populate (LitV LitPoison).

Canonical Structure stateO := leibnizO state.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Language *)
Lemma lrust_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val,
    val_stuck, fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
Canonical Structure lrust_ectxi_lang := EctxiLanguage lrust_lang_mixin.
Canonical Structure lrust_ectx_lang := EctxLanguageOfEctxi lrust_ectxi_lang.
Canonical Structure lrust_lang := LanguageOfEctx lrust_ectx_lang.

(* Lemmas about the language. *)
Lemma stuck_irreducible K σ : irreducible (fill K stuck_term) σ.
Proof.
  apply: (irreducible_fill (K:=ectx_language.fill K)); first done.
  apply prim_head_irreducible.
  - inversion 1.
  - apply ectxi_language_sub_redexes_are_values.
    intros [] ??; simplify_eq/=; eauto; discriminate_list.
Qed.

(* Define some derived forms *)
Notation Lam xl e := (Rec BAnon xl e) (only parsing).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV xl e := (RecV BAnon xl e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitPoison) (Lit LitPoison)).
Coercion lit_of_bool : bool >-> base_lit.
Notation If e0 e1 e2 := (Case e0 (@cons expr e2 (@cons expr e1 (@nil expr))))
  (only parsing).
Notation Newlft := (Lit LitPoison) (only parsing).
Notation Endlft := (Seq Skip (Seq Skip Skip)) (only parsing).
Notation Share := (Seq Skip Skip) (only parsing).
