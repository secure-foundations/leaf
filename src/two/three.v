From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From iris.base_logic.lib Require Export invariants.

From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export fancy_updates_from_vs.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export wsat.

From iris.bi Require Import derived_laws.

Context {Σ: gFunctors}.
Context `{!invGS Σ}.

Definition supports x y : iProp Σ := x -∗ (y ∗ (y -∗ x)).

Lemma lemma_compose (A B P Q C : iProp Σ)
    (a: ⊢ supports (A ∗ P) (A ∗ B))
    (b: ⊢ supports (B ∗ Q) (B ∗ C))
    : ⊢ supports (A ∗ P ∗ Q) (A ∗ C).
Proof.
  unfold supports in *.
  iIntros "[a [p q]]".
  iDestruct (a with "[a p]") as "[[a b] back]". { iFrame. }
  iDestruct (b with "[b q]") as "[[b c] back2]". { iFrame. }
  iFrame.
  iIntros "[a c]".
  iDestruct ("back2" with "[b c]") as "[b q]". { iFrame. }
  iDestruct ("back" with "[a b]") as "[a p]". { iFrame. }
  iFrame.
Qed.

Lemma lemma_compose2 (A B P Q C : iProp Σ)
    (a: ⊢ supports (A ∗ P) (A ∗ B))
    (b: ⊢ supports (B ∗ Q) (B ∗ C))
    : ⊢ supports (A ∗ P ∗ Q) (A ∗ P ∗ C).
Proof.
  unfold supports in *.
  iIntros "[a [p q]]".
  iDestruct (a with "[a p]") as "[[a b] back]". { iFrame. }
  iDestruct (b with "[b q]") as "[[b c] back2]". { iFrame. }
  iDestruct ("back" with "[a b]") as "[a p]". { iFrame. }
  iFrame.
  iIntros "[a [p c]]".
  
  iDestruct (a with "[a p]") as "[[a b] back]". { iFrame. }
  iDestruct ("back2" with "[b c]") as "[b q]". { iFrame. }
  iDestruct ("back" with "[a b]") as "[a p]". { iFrame. }
  iFrame.
Qed.

(*
Lemma lemma_compose3 (A B P Q C : iProp Σ)
    (a: ⊢ supports (A ∗ P ∗ Q) (A ∗ Q ∗ B))
    (b: ⊢ supports (B ∗ P ∗ Q) (B ∗ P ∗ C))
    : ⊢ supports (A ∗ P ∗ Q) (A ∗ P ∗ C).
Proof.
  unfold supports in *.
  iIntros "[a [p q]]".
  iDestruct (a with "[a p q]") as "[[a [p b]] back]". { iFrame. }
  iDestruct (b with "[b q]") as "[[b c] back2]". { iFrame. }
  iDestruct ("back" with "[a b]") as "[a p]". { iFrame. }
  iFrame.
  iIntros "[a [p c]]".
  
  iDestruct (a with "[a p]") as "[[a b] back]". { iFrame. }
  iDestruct ("back2" with "[b c]") as "[b q]". { iFrame. }
  iDestruct ("back" with "[a b]") as "[a p]". { iFrame. }
  iFrame.
Qed.
*)


Lemma lemma_compose_8 (A B P Q C : iProp Σ)
    (a: A ⊢ □ (supports P B))
    (b: B ⊢ □ (supports P C))
    : A ⊢ □ (supports P C).
Proof.
  unfold supports in *.
  iIntros "a".
  iDestruct (a with "a") as "#bt".
  iModIntro.
  iIntros "p".
  iDestruct ("bt" with "p") as "[b back]".
  iDestruct (b with "b") as "#ct".
  iDestruct ("back" with "b") as "p".
  iDestruct ("ct" with "p") as "ccp". iFrame.
Qed.

(*
Lemma lemma_compose_9 (A B P Q C : iProp Σ)
    (a: A ∗ P ⊢ □ (supports Q B))
    (b: B ∗ P ⊢ □ (supports Q C))
    : A ∗ P ⊢ □ (supports Q C).
Proof.
  unfold supports in *.
  iIntros "a".
  iDestruct (a with "a") as "#bt".
  iModIntro.
  iIntros "q".
  iDestruct ("bt" with "q") as "[b back]".
  iDestruct (b with "b") as "#ct".
  iDestruct ("back" with "b") as "q".
  iDestruct ("ct" with "q") as "ccq". iFrame.
Qed.
*)

Lemma exists_and {T} (t: T) (P : T -> iProp Σ) (Q: iProp Σ)
  : (∃ t , P t) ∧ Q ⊢ ∃ t , (P t ∧ Q).
Proof.
  iIntros "a".
  rewrite bi.and_exist_r.
  iFrame.
Qed.

Context `{i : !inG Σ A}.
Implicit Types a : A.
Context `{CmraDiscrete A}.

Local Lemma later_internal_eq_iRes_singleton_a γ a r :
  ▷ (r ≡ iRes_singleton γ a) ⊢@{iPropI Σ}
  ◇ ∃ b r', r ≡ iRes_singleton γ b ⋅ r' ∧ ▷ (a ≡ b).
Proof.
  assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)).
  { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). }
  rewrite (f_equivI (λ r : iResUR Σ, r (inG_id i) !! γ) r).
  rewrite {1}/iRes_singleton discrete_fun_lookup_singleton lookup_singleton.
  rewrite option_equivI. case Hb: (r (inG_id _) !! γ)=> [b|]; last first.
  { by rewrite /bi_except_0 -bi.or_intro_l. }
  rewrite -bi.except_0_intro.
  rewrite -(bi.exist_intro (cmra_transport (eq_sym inG_prf) (inG_fold b))).
  rewrite -(bi.exist_intro (discrete_fun_insert (inG_id _) (delete γ (r (inG_id i))) r)).
  apply bi.and_intro.
  - apply equiv_internal_eq. rewrite /iRes_singleton.
    rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
    intros i'. rewrite discrete_fun_lookup_op.
    destruct (decide (i' = inG_id i)) as [->|?].
    + rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
      intros γ'. rewrite lookup_op. destruct (decide (γ' = γ)) as [->|?].
      * by rewrite lookup_singleton lookup_delete Hb inG_unfold_fold.
      * by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
    + rewrite discrete_fun_lookup_insert_ne //.
      by rewrite discrete_fun_lookup_singleton_ne // left_id.
  - apply bi.later_mono. rewrite (f_equivI inG_fold) inG_fold_unfold.
    apply: (internal_eq_rewrite' _ _ (λ b, a ≡ cmra_transport (eq_sym inG_prf) b)%I);
      [solve_proper|apply internal_eq_sym|].
    rewrite cmra_transport_trans eq_trans_sym_inv_r /=. apply internal_eq_refl.
Qed.

Print inG_prf.
Definition project (x: iResUR Σ) (𝛾: gname) : option A :=
  match (x (inG_id i) !! 𝛾) with
  | Some t => Some (cmra_transport (eq_sym inG_prf) (inG_fold t))
  | None => None
  end.

Lemma valid_project (x: iResUR Σ) (𝛾: gname) (n: nat) :
    ✓{n} x -> ✓{n} (project x 𝛾).
Proof.
  intros.
  unfold project.
  destruct (x (inG_id i) !! 𝛾) eqn:p.
  - apply cmra_transport_validN.
    rewrite <- inG_unfold_validN.
    setoid_rewrite inG_unfold_fold.
    enough (✓{n} Some o); trivial.
    rewrite <- p.
    enough (✓{n} (x (inG_id i))). { trivial. }
    trivial.
  - unfold validN. unfold cmra_validN. unfold optionR. unfold option_validN_instance.
    trivial.
Qed.

Lemma some_op_equiv (a b c : A)
  : a ≡ b ⋅ c -> Some a ≡ Some b ⋅ Some c.
Proof. intros. setoid_rewrite H0. trivial. Qed.

Lemma project_op (x y: iResUR Σ) γ :
    project (x ⋅ y) γ ≡ project x γ ⋅ project y γ.
Proof.
  unfold project.
  rewrite lookup_op.
  destruct (x (inG_id i) !! γ) eqn:p1; destruct (y (inG_id i) !! γ) eqn:p2.
  - rewrite p1. rewrite p2.
      replace (Some o ⋅ Some o0) with (Some (o ⋅ o0)) by trivial.
      apply some_op_equiv.
      setoid_rewrite <- cmra_transport_op.
      f_equiv.
      unfold inG_fold.
      apply cmra_morphism_op.
      typeclasses eauto.
  - rewrite p1. rewrite p2. trivial.
      (*replace (Some o ⋅ None) with (Some o) by trivial. trivial.*)
  - rewrite p1. rewrite p2. trivial.
      (*replace (None ⋅ Some o) with (Some o) by trivial. trivial.*)
  - rewrite p1. rewrite p2. trivial.
Qed.

Lemma project_iRes_singleton (x: A) (𝛾: gname)
  : project (iRes_singleton 𝛾 x) 𝛾 ≡ Some x.
Proof.
  unfold project, iRes_singleton.
  setoid_rewrite discrete_fun_lookup_singleton.
  rewrite lookup_singleton.
  f_equiv.
  setoid_rewrite inG_fold_unfold.
  rewrite cmra_transport_trans eq_trans_sym_inv_r /=.
  trivial.
Qed.

Lemma some_op_equiv2 (a b : A) (c: option A) (n: nat)
  : Some a ≡{n}≡ Some b ⋅ c -> a ≡{n}≡ b ⋅? c.
Proof. intros. unfold "⋅?". destruct c.
  - inversion H0. trivial.
  - inversion H0. trivial.
Qed.

Lemma discrete_equiv (a b : A) (n: nat)
  : a ≡{n}≡ b -> a ≡ b.
Proof.
  intros.
  apply discrete. { typeclasses eauto. }
  apply dist_le with (n0 := n); trivial. lia.
Qed.

Lemma proper_project_equiv_n 𝛾 (n: nat) : Proper ((≡{n}≡) ==> (≡{n}≡)) (λ x , project x 𝛾).
Proof.
  unfold Proper, "==>". intros. unfold project.
  assert (x (inG_id i) !! 𝛾 ≡{n}≡ y (inG_id i) !! 𝛾) as M.
  {
      enough (x (inG_id i) ≡{n}≡ y (inG_id i)).
      { trivial. }
      trivial.
  }
  destruct (x (inG_id i) !! 𝛾);
  destruct (y (inG_id i) !! 𝛾).
  - assert (o ≡{n}≡ o0) as Q.
    + unfold "≡" in M. unfold ofe_equiv, optionO, option_equiv in M.
          inversion M. trivial.
    + setoid_rewrite Q. trivial.
  - inversion M.
  - inversion M.
  - trivial.
Qed.
      

Lemma None_Some_contra (x: A) (y: option A) (n: nat)
  (k: None ≡{n}≡ Some x ⋅ y) : False.
Proof.
  (*have k := discrete_equiv2 _ _ _ t.*)
  destruct y.
  - unfold "⋅" in k. unfold optionR in k. unfold cmra_op in k. unfold option_op_instance in k.
      unfold union_with in k. unfold option_union_with in k. inversion k.
  - unfold "⋅" in k. unfold optionR in k. unfold cmra_op in k. unfold option_op_instance in k.
      unfold union_with in k. unfold option_union_with in k. inversion k.
Qed.

Lemma and_own 𝛾 (x y: A)
  : (own 𝛾 x ∧ own 𝛾 y) ⊢ 
  ((⌜ ∃ z , ✓ z ∧ (∃ t , z ≡ x ⋅? t) ∧ (∃ t , z ≡ y ⋅? t) ⌝) : iProp Σ).
Proof.
  uPred.unseal.
  split.
  intros n x0 val aoo.
  unfold uPred_pure_def. unfold uPred_holds.
  rewrite own_eq in aoo.
  unfold own_def in aoo.
  unfold uPred_holds in aoo. unfold uPred_and_def in aoo.
  destruct aoo as [o1 o2].
  rewrite uPred_ownM_eq in o1.
  rewrite uPred_ownM_eq in o2.
  unfold uPred_holds in o1. unfold uPred_ownM_def in o1.
  unfold uPred_holds in o2. unfold uPred_ownM_def in o2.
  
  destruct (project x0 𝛾) eqn:p.
  - exists c. split.
    { rewrite (cmra_discrete_valid_iff n).
        enough (✓{n} Some c) by trivial. rewrite <- p. apply valid_project. trivial.
    }
    split.
    {
      unfold includedN in o1.
      destruct o1 as [t o1]. exists (project t 𝛾).
      unfold included.
      apply (discrete_equiv _ _ n).
      apply some_op_equiv2. rewrite <- p.
      setoid_rewrite <- (project_iRes_singleton x 𝛾).
      setoid_rewrite <- project_op.
      apply proper_project_equiv_n. trivial.
    }
    {
      unfold includedN in o2.
      destruct o2 as [t o2]. exists (project t 𝛾).
      unfold included.
      apply (discrete_equiv _ _ n).
      apply some_op_equiv2. rewrite <- p.
      setoid_rewrite <- (project_iRes_singleton y 𝛾).
      setoid_rewrite <- project_op.
      apply proper_project_equiv_n. trivial.
    }
  - unfold includedN in o1.
      destruct o1 as [t o1].
      assert (project x0 𝛾 ≡{n}≡ project (iRes_singleton 𝛾 x) 𝛾 ⋅ project t 𝛾).
      { setoid_rewrite <- project_op. apply proper_project_equiv_n. trivial. }
      setoid_rewrite project_iRes_singleton in H0.
      rewrite p in H0.
      have j := None_Some_contra _ _ _ H0.
      contradiction.
Qed.
  
Lemma and_own 𝛾 (x y z: M)
  ∀ r , 
  : (own 𝛾 x ∧ own 𝛾 y) ⊢ own 𝛾 z
  ((⌜ ∃ z , ✓ z ∧ x ≼ z ∧ y ≼ z ⌝) : iProp Σ).

Lemma lemma_extend_1 (A B P Q C : iProp Σ)
    (a : supports P A ⊢ supports P B)
    : supports (P ∗ Q) A ⊢ supports (P ∗ Q) B.
Proof.
  unfold supports in *.
  iIntros "x [p q]".

  
  
 
Lemma lemma_compose_4 (A B P Q C : iProp Σ)
    (a: (A ∗ P ∗ Q ⊢ A ∗ P ∗ Q ∗ (supports Q B)))
    (b: (B ∗ P ∗ Q ⊢ B ∗ P ∗ Q ∗ (supports Q C)))
    : (A ∗ P ∗ Q ⊢ A ∗ P ∗ Q ∗ (supports Q C)).
Proof.
  unfold supports in *.
  iIntros "ap".
  iDestruct (a with "ap") as "[a [p [q suppb]]]".
  iDestruct ("suppb" with "q") as "[b backb]".
  iModIntro. unfold supports in *.
  iIntros "q".
  
  
  
Lemma lemma_compose (A B P Q C : iProp Σ)
    (a: (A ∗ P ⊢ □ (supports Q B)))
    (b: (B ∗ P ⊢ □ (supports Q C)))
    : (A ∗ P ⊢ □ (supports Q C)).
Proof.
  unfold supports in *.
  iIntros "ap".
  iDestruct (a with "ap") as "#sb".
  iModIntro. unfold supports in *.
  iIntros "q".
    

Definition supports E x y : iProp Σ := □ (x ={E, ∅}=∗ y ∗ (y ={∅, E}=∗ x))%I.
Notation "P &&{ E }&&> Q" := (supports E P Q)
  (at level 99, E at level 50, Q at level 200).

Lemma supports_refl E P : ⊢ P &&{ E }&&> P.
Proof.
  unfold supports. iIntros. iModIntro. iIntros "x".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iIntros "[t z]". iMod ownE_empty as "l". iModIntro. iModIntro.
  iFrame. iIntros "a [b c]". iModIntro. iModIntro. iFrame.
Qed.

Lemma supports_monotonic E1 E2 P Q :
  (disjoint E1 E2) ->
  supports E1 P Q ⊢ supports (E1 ∪ E2) P Q.
Proof.
  intro.
  unfold supports. iIntros "#x". iModIntro. iIntros "p".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iDestruct ("x" with "p") as "t".
  iIntros "[s e12]".
  iDestruct (ownE_op with "e12") as "[e1 e2]"; trivial.
  iDestruct ("t" with "[s e1]") as "z". { iFrame. }
  iMod "z" as "z". iModIntro.
  iMod "z" as "z". iModIntro.
  iDestruct "z" as "[a [b [c d]]]".
  iFrame. iIntros "e f".
  iDestruct ("d" with "e f") as "d".
  iMod "d" as "d". iModIntro.
  iMod "d" as "d". iModIntro.
  iDestruct "d" as "[q [r s]]". iFrame.
  rewrite ownE_op; trivial. iFrame.
Qed.

Lemma supports_add_set E1 E2 P Q :
  (disjoint E1 E2) ->
  supports E1 P Q ⊢ □ (P ={E1 ∪ E2, E2}=∗ Q ∗ (Q ={E2, E1 ∪ E2}=∗ P)).
Proof.
  intro.
  unfold supports. iIntros "#x". iModIntro. iIntros "p".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iDestruct ("x" with "p") as "t".
  iIntros "[s e12]".
  iDestruct (ownE_op with "e12") as "[e1 e2]"; trivial.
  iDestruct ("t" with "[s e1]") as "z". { iFrame. }
  iMod "z" as "z". iModIntro.
  iMod "z" as "z". iModIntro.
  iDestruct "z" as "[a [b [c d]]]".
  iFrame. iIntros "e [f g]".
  iDestruct ("d" with "e [f b]") as "d". {iFrame.}
  iMod "d" as "d". iModIntro.
  iMod "d" as "d". iModIntro.
  iDestruct "d" as "[q [r s]]". iFrame.
  rewrite ownE_op; trivial. iFrame.
Qed.

Lemma supports_composition E1 E2 P Q R : (disjoint E1 E2) ->
    (P &&{E1}&&> Q) ∗ (Q &&{E2}&&> R) ⊢ P &&{E1 ∪ E2}&&> R.
Proof.
  intro.
  iIntros "[#x #y]".
  iDestruct (supports_add_set _ E2 _ _ with "x") as "#z"; trivial.
  unfold supports. iModIntro.
  iIntros "p".
  iMod ("z" with "p") as "[l s]".
  iMod ("y" with "l") as "[R T]".
  iModIntro. iFrame.
  iIntros "R".
  iMod ("T" with "R") as "Q".
  iMod ("s" with "Q").
  iModIntro. iFrame.
Qed.

Lemma supports_apply E1 E2 A B P Q : (disjoint E1 E2) ->
    (A &&{E1}&&> B) ∗ (B ∗ P ={E2}=∗ B ∗ Q)
                    ⊢ (A ∗ P ={E1 ∪ E2}=∗ A ∗ Q).
Proof.
  intro.
  iIntros "[#x y] [a p]".
  iDestruct (supports_add_set _ E2 _ _ with "x") as "#z"; trivial.
  iMod ("z" with "a") as "[b g]".
  iMod ("y" with "[b p]") as "[b q]". {iFrame.}
  iMod ("g" with "b").
  iModIntro. iFrame.
Qed.

Lemma lemma0 x (P : iProp Σ)
  : (P ⊢ uPred_ownM x) ->
      P ⊢ (
          (uPred_ownM x)
          ∗ 
          ((uPred_ownM x) -∗ P)
      ).
Proof.
  uPred.unseal.
  intro.
  split.
  intros.
  destruct H.
  unfold uPred_holds. unfold uPred_sep_def. intros.
  have h := uPred_in_entails n x0 H0 H1.
  unfold uPred_holds in h. unfold uPred_ownM_def in h.
  unfold includedN in h. destruct h as [z h].
  exists x. exists z.
  split.
  { trivial. }
  split.
  { unfold uPred_holds. unfold uPred_ownM_def. trivial. }
  { unfold uPred_holds. unfold uPred_wand_def. intros.
      unfold uPred_holds in H3.
      unfold uPred_ownM_def in H3.
      unfold includedN in H3. destruct H3 as [w j].
      setoid_rewrite j.
      apply uPred_mono with (n1 := n) (x1 := x0); trivial.
      assert (z ⋅ (x ⋅ w) ≡ (z ⋅ x) ⋅ w) as associ. { apply cmra_assoc. }
      setoid_rewrite associ.
      assert ((z ⋅ x) ≡ (x ⋅ z)) as commu. { apply cmra_comm. }
      setoid_rewrite commu.
      unfold includedN. exists w.
      apply dist_le with (n0 := n); trivial.
      setoid_rewrite h.
      trivial.
  } 
Qed.

Lemma lemma1 E (P Q R: iProp Σ) : (P ⊢ □ (Q ={E}=∗ R)) -> (⊢ □ (P ∗ Q ={E}=∗ P ∗ R)).
Proof.
  intro.
  iIntros.
  iModIntro. iIntros "[p q]".
  iDestruct (H with "p") as "#J".
  iMod ("J" with "q") as "k".
  iModIntro. iFrame.
Qed.

(*
Lemma lemma2 E (P Q R: iProp Σ) :
    (⊢ □ (P ∗ Q ={E}=∗ P ∗ R)) -> (P ⊢ □ (Q ={E}=∗ R)).
Proof.
  intro.
  iIntros "p".
  iModIntro.
  *)

Lemma lemma7 E (S P Q R: iProp Σ) :
    (⊢ □ (P ∗ Q ={E}=∗ P ∗ R))
      -> (S ⊢ P)
      -> (⊢ □ (S ∗ Q ={E}=∗ S ∗ R)).
Proof.
  intro.
  intro.
  iIntros.
  iModIntro.
  iIntros "[s q]".
  iDestruct (H0 with "s") as "p".
  iDestruct (H with "[p q]") as "x". {iFrame.}
  idestruct (h with "[p q]") as "t". {iframe.}

  
Lemma3 e (p q r: iprop σ) :
    (⊢ (p ∗ q ={e}=∗ p ∗ r)) -> (p ⊢ (q ={e}=∗ r)).
proof.
  intro.
  iintros "p q".
  idestruct (h with "[p q]") as "t". {iframe.}
  

Lemma lemma3 E (P1 P2 Q R: iProp Σ) :
    (P2 -∗ P1) ∗ □ (P1 ∗ Q ={E}=∗ P1 ∗ R) ⊢ □ (P2 ∗ Q ={E}=∗ P2 ∗ R).
Proof.
  intro.
  iIntros.
  iModIntro. iIntros "[p q]".
  iDestruct (H with "p") as "#J".
  iMod ("J" with "q") as "k".
  iModIntro. iFrame.
Qed.



Lemma lemma1 (P Q R: iProp Σ) : (P -∗ □ Q ==∗ R) ⊢ (□ P ∗ Q ==∗ P ∗ R).
Proof.
  iIntros "x y".
  Unset Printing Notations.

Lemma sep_and_my (P Q: iProp Σ) : (P ⊢ Q) -> P ⊢ (Q ∗ (Q -∗ P)).
Proof.
  unfold bi_entails.
  uPred.unseal.
  intros.
  split.
  destruct H.
  intros.
  unfold uPred_holds. unfold uPred_sep_def.
  unfold uPred_wand_def. cbv [uPred_holds].
  exists x. exists ε.
  

Lemma sep_and_my (P Q R: iProp Σ) : (P ∗ Q) ∧ (P ∗ R) ⊢ P ∗ (Q ∧ R).
Proof.
  unfold bi_entails.
  uPred.unseal.
  intros.
  split. intros.
  unfold uPred_holds. unfold uPred_sep_def.
  unfold uPred_holds. unfold uPred_and_def.
  unfold uPred_holds in H0. unfold uPred_and_def in H0. destruct H0.
  unfold uPred_holds in H0. unfold uPred_sep_def in H0.
  unfold uPred_holds in H1. unfold uPred_sep_def in H1.
  
  destruct H0 as [x1 [x2 [A [B C]]]].
  destruct H1 as [y1 [y2 [D [E F]]]].
  *)
  

Lemma ehy (a b c : iProp Σ) : ⊢ (a -∗ (b ∗ (b -∗ a))) -∗ (a -∗ (c ∗ (c -∗ a)))
    -∗ (a -∗ ((b ∧ c) ∗ ((b ∧ c) -∗ a))).
Proof.
  iIntros "x y a".

Lemma stuff a b P Q : (a -∗ b) ∗ (b ∗ P ==∗ b ∗ Q) ⊢ ((a ∗ P ==∗ a ∗ Q) : iProp Σ).
Proof.
  unfold bi_entails.
  Print bi_entails.
  uPred.unseal.
  split. intros.
  unfold uPred_holds. unfold uPred_wand_def.
  intros.
  unfold uPred_holds in H3. unfold uPred_sep_def in H3.
  unfold uPred_holds. unfold uPred_bupd_def. intros.
  unfold uPred_holds. unfold uPred_sep_def.
  
  unfold uPred_sep_def in H0.
  
  unfold uPred_holds in H0. unfold uPred_sep_def in H0.
  destruct H0 as [x1 [x2 [S [T U]]]].
  unfold uPred_wand_def in U.
  unfold uPred_holds in T. unfold uPred_wand_def in T.
  
  unfold uPred_holds. unfold uPred_sep_def.
  unfold uPred_holds. unfold uPred_bupd_def.
  unfold uPred_wand_def. unfold uPred_holds.
  unfold uPred_sep_def. unfold uPred_holds.
  
  unfold uPred_entails. , uPred_sep_def, uPred_wand_def.
  unfold bi_entails, bi_sep, bi_wand.
  intro.

Class Inv (A : Type) := inv : A → Prop.
Global Hint Mode Inv ! : typeclass_instances.
Global Instance: Params (@inv) 2 := {}.

Record ProtocolMixin P B
    `{Equiv P, PCore P, Op P, Valid P, Inv P, Unit P}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
:= {
    protocol_ra_mixin: RAMixin P;
    base_ra_mixin: RAMixin P; (* completely ignore core *)
 
    interp: P -> B;

    inv_implies_valid: ∀ (p: P) , inv p -> ✓ p;
    inv_proper: Proper ((≡) ==> impl) (@inv P _);
    interp_proper: Proper ((≡) ==> (≡)) (@inv P _);
}. 

Inductive InvedProtocol (P: Type) :=
  | Inved : P -> InvedProtocol P.
Global Arguments Inved {_} _.

Global Instance inved_protocol_equiv P `{Equiv P} : Equiv (InvedProtocol P) :=
    λ x y , match x with Inved a => match y with Inved b => a ≡ b end end.
    
Global Instance inved_protocol_pcore P `{PCore P} : PCore (InvedProtocol P) :=
    λ x , match x with Inved a => 
        match pcore a with
          | Some t => Some (Inved t)
          | None => None
        end end.

Global Instance inved_protocol_valid P `{Inv P} `{Op P} : Valid (InvedProtocol P) :=
   λ x , match x with Inved a => ∃ b , inv (a ⋅ b) end.
   
Global Instance inved_protocol_op P `{Inv P} `{Op P} : Op (InvedProtocol P) :=
   λ x y , match x with Inved a => match y with Inved b => Inved (a ⋅ b) end end.


Definition inved_protocol_ra_mixin {P B}
    `{Equiv P, PCore P, Op P, Inv P, Valid P, Unit P}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
    (pm: ProtocolMixin P B) : RAMixin (InvedProtocol P).
Proof. split.
 - 
