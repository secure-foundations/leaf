(** This file implements a type [binder] with elements [BAnon] for the
anonymous binder, and [BNamed] for named binders. This type is isomorphic to
[option string], but we use a special type so that we can define [BNamed] as
a coercion.

This library is used in various Iris developments, like heap-lang, LambdaRust,
Iron, Fairis. *)
From stdpp Require Export strings.
From stdpp Require Import sets countable finite fin_maps.
From stdpp Require Import options.

(* Pick up extra assumptions from section parameters. *)
Set Default Proof Using "Type*".

Declare Scope binder_scope.
Delimit Scope binder_scope with binder.

Inductive binder := BAnon | BNamed :> string → binder.
Bind Scope binder_scope with binder.
Notation "<>" := BAnon : binder_scope.

(** [binder_list] matches [option_list]. *)
Definition binder_list (b : binder) : list string :=
  match b with
  | BAnon => []
  | BNamed s => [s]
  end.

Global Instance binder_dec_eq : EqDecision binder.
Proof. solve_decision. Defined.
Global Instance binder_inhabited : Inhabited binder := populate BAnon.
Global Instance binder_countable : Countable binder.
Proof.
 refine (inj_countable'
   (λ b, match b with BAnon => None | BNamed s => Some s end)
   (λ b, match b with None => BAnon | Some s => BNamed s end) _); by intros [].
Qed.

(** The functions [cons_binder b ss] and [app_binder bs ss] are typically used
to collect the free variables of an expression. Here [ss] is the current list of
free variables, and [b], respectively [bs], are the binders that are being
added. *)
Definition cons_binder (b : binder) (ss : list string) : list string :=
  match b with BAnon => ss | BNamed s => s :: ss end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (bs : list binder) (ss : list string) : list string :=
  match bs with [] => ss | b :: bs => b :b: app_binder bs ss end.
Infix "+b+" := app_binder (at level 60, right associativity).

Global Instance set_unfold_cons_binder s b ss P :
  SetUnfoldElemOf s ss P → SetUnfoldElemOf s (b :b: ss) (BNamed s = b ∨ P).
Proof.
  constructor. rewrite <-(set_unfold (s ∈ ss) P).
  destruct b; simpl; rewrite ?elem_of_cons; naive_solver.
Qed.
Global Instance set_unfold_app_binder s bs ss P Q :
  SetUnfoldElemOf (BNamed s) bs P → SetUnfoldElemOf s ss Q →
  SetUnfoldElemOf s (bs +b+ ss) (P ∨ Q).
Proof.
  intros HinP HinQ.
  constructor. rewrite <-(set_unfold (s ∈ ss) Q), <-(set_unfold (BNamed s ∈ bs) P).
  clear HinP HinQ.
  induction bs; set_solver.
Qed.

Lemma app_binder_named ss1 ss2 : (BNamed <$> ss1) +b+ ss2 = ss1 ++ ss2.
Proof. induction ss1; by f_equal/=. Qed.

Lemma app_binder_snoc bs s ss : bs +b+ (s :: ss) = (bs ++ [BNamed s]) +b+ ss.
Proof. induction bs; by f_equal/=. Qed.

Global Instance cons_binder_Permutation b : Proper ((≡ₚ) ==> (≡ₚ)) (cons_binder b).
Proof. intros ss1 ss2 Hss. destruct b; csimpl; by rewrite Hss. Qed.

Global Instance app_binder_Permutation : Proper ((≡ₚ) ==> (≡ₚ) ==> (≡ₚ)) app_binder.
Proof.
  assert (∀ bs, Proper ((≡ₚ) ==> (≡ₚ)) (app_binder bs)).
  { intros bs. induction bs as [|[]]; intros ss1 ss2; simpl; by intros ->. }
  induction 1 as [|[]|[] []|]; intros ss1 ss2 Hss; simpl;
    first [by eauto using perm_trans|by rewrite 1?perm_swap, Hss].
Qed.

Definition binder_delete `{Delete string M} (b : binder) (m : M) : M :=
  match b with BAnon => m | BNamed s => delete s m end.
Definition binder_insert `{Insert string A M} (b : binder) (x : A) (m : M) : M :=
  match b with BAnon => m | BNamed s => <[s:=x]> m end.
Global Instance: Params (@binder_insert) 4 := {}.

Section binder_delete_insert.
  Context `{FinMap string M}.

  Global Instance binder_insert_proper `{Equiv A} b :
    Proper ((≡) ==> (≡) ==> (≡@{M A})) (binder_insert b).
  Proof. destruct b; solve_proper. Qed.

  Lemma binder_delete_empty {A} b : binder_delete b ∅ =@{M A} ∅.
  Proof. destruct b; simpl; eauto using delete_empty. Qed.

  Lemma lookup_binder_delete_None {A} (m : M A) b s :
    binder_delete b m !! s = None ↔ b = BNamed s ∨ m !! s = None.
  Proof. destruct b; simpl; by rewrite ?lookup_delete_None; naive_solver. Qed.
  Lemma binder_insert_fmap {A B} (f : A → B) (x : A) b (m : M A) :
    f <$> binder_insert b x m = binder_insert b (f x) (f <$> m).
  Proof. destruct b; simpl; by rewrite ?fmap_insert. Qed.

  Lemma binder_delete_insert {A} b s x (m : M A) :
    b ≠ BNamed s → binder_delete b (<[s:=x]> m) = <[s:=x]> (binder_delete b m).
  Proof. intros. destruct b; simpl; by rewrite ?delete_insert_ne by congruence. Qed.
  Lemma binder_delete_delete {A} b s (m : M A) :
    binder_delete b (delete s m) = delete s (binder_delete b m).
  Proof. destruct b; simpl; by rewrite 1?delete_commute. Qed.
End binder_delete_insert.
