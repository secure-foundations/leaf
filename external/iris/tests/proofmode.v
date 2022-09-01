From iris.bi Require Import laterable.
From iris.proofmode Require Import tactics intro_patterns.
Set Default Proof Using "Type".

Unset Mangle Names.

Section tests.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Lemma test_eauto_emp_isplit_biwand P : emp ⊢ P ∗-∗ P.
Proof. eauto 6. Qed.

Lemma test_eauto_isplit_biwand P : ⊢ P ∗-∗ P.
Proof. eauto. Qed.

Fixpoint test_fixpoint (n : nat) {struct n} : True → emp ⊢@{PROP} ⌜ (n + 0)%nat = n ⌝.
Proof.
  case: n => [|n] /=; first (iIntros (_) "_ !%"; reflexivity).
  iIntros (_) "_".
  by iDestruct (test_fixpoint with "[//]") as %->.
Qed.

Check "demo_0".
Lemma demo_0 P Q : □ (P ∨ Q) -∗ (∀ x, ⌜x = 0⌝ ∨ ⌜x = 1⌝) → (Q ∨ P).
Proof.
  iIntros "H #H2". Show. iDestruct "H" as "###H".
  (* should remove the disjunction "H" *)
  iDestruct "H" as "[#?|#?]"; last by iLeft. Show.
  (* should keep the disjunction "H" because it is instantiated *)
  iDestruct ("H2" $! 10) as "[%|%]". done. done.
Qed.

Lemma demo_2 P1 P2 P3 P4 Q (P5 : nat → PROP) `{!Affine P4, !Absorbing P2} :
  P2 ∗ (P3 ∗ Q) ∗ True ∗ P1 ∗ P2 ∗ (P4 ∗ (∃ x:nat, P5 x ∨ P3)) ∗ emp -∗
    P1 -∗ (True ∗ True) -∗
  (((P2 ∧ False ∨ P2 ∧ ⌜0 = 0⌝) ∗ P3) ∗ Q ∗ P1 ∗ True) ∧
     (P2 ∨ False) ∧ (False → P5 0).
Proof.
  (* Intro-patterns do something :) *)
  iIntros "[H2 ([H3 HQ]&?&H1&H2'&foo&_)] ? [??]".
  (* To test destruct: can also be part of the intro-pattern *)
  iDestruct "foo" as "[_ meh]".
  repeat iSplit; [|by iLeft|iIntros "#[]"].
  iFrame "H2".
  (* split takes a list of hypotheses just for the LHS *)
  iSplitL "H3".
  - iFrame "H3". iRight. auto.
  - iSplitL "HQ". iAssumption. by iSplitL "H1".
Qed.

Lemma demo_3 P1 P2 P3 :
  P1 ∗ P2 ∗ P3 -∗ P1 ∗ ▷ (P2 ∗ ∃ x, (P3 ∧ ⌜x = 0⌝) ∨ P3).
Proof. iIntros "($ & $ & $)". iNext. by iExists 0. Qed.

Lemma test_pure_space_separated P1 :
  <affine> ⌜True⌝ ∗ P1 -∗ P1.
Proof.
  (* [% H] should be parsed as two separate patterns and not the pure name
  [H] *)
  iIntros "[% H] //".
Qed.

Definition foo (P : PROP) := (P -∗ P)%I.
Definition bar : PROP := (∀ P, foo P)%I.

Lemma test_unfold_constants : ⊢ bar.
Proof. iIntros (P) "HP //". Qed.

Check "test_iStopProof".
Lemma test_iStopProof Q : emp -∗ Q -∗ Q.
Proof. iIntros "#H1 H2". Show. iStopProof. Show. by rewrite bi.sep_elim_r. Qed.

Lemma test_iRewrite `{!BiInternalEq PROP} {A : ofe} (x y : A) P :
  □ (∀ z, P -∗ <affine> (z ≡ y)) -∗ (P -∗ P ∧ (x,x) ≡ (y,x)).
Proof.
  iIntros "#H1 H2".
  iRewrite (internal_eq_sym x x with "[# //]").
  iRewrite -("H1" $! _ with "[- //]").
  auto.
Qed.

Check "test_iDestruct_and_emp".
Lemma test_iDestruct_and_emp P Q `{!Persistent P, !Persistent Q} :
  P ∧ emp -∗ emp ∧ Q -∗ <affine> (P ∗ Q).
Proof. iIntros "[#? _] [_ #?]". Show. auto. Qed.

Lemma test_iIntros_persistent P Q `{!Persistent Q} : ⊢ (P → Q → P ∧ Q).
Proof. iIntros "H1 #H2". by iFrame "∗#". Qed.

Lemma test_iDestruct_intuitionistic_1 P Q `{!Persistent P}:
  Q ∗ □ (Q -∗ P) -∗ P ∗ Q.
Proof. iIntros "[HQ #HQP]". iDestruct ("HQP" with "HQ") as "#HP". by iFrame. Qed.

Lemma test_iDestruct_intuitionistic_2 P Q `{!Persistent P, !Affine P}:
  Q ∗ (Q -∗ P) -∗ P.
Proof. iIntros "[HQ HQP]". iDestruct ("HQP" with "HQ") as "#HP". done. Qed.

Lemma test_iDestruct_specialize_wand P Q :
  Q -∗ Q -∗ □ (Q -∗ P) -∗ P ∗ P.
Proof.
  iIntros "HQ1 HQ2 #HQP".
  (* [iDestruct] does not consume "HQP" because a wand is instantiated *)
  iDestruct ("HQP" with "HQ1") as "HP1".
  iDestruct ("HQP" with "HQ2") as "HP2".
  iFrame.
Qed.
Lemma test_iPoseProof_specialize_wand P Q :
  Q -∗ Q -∗ □ (Q -∗ P) -∗ P ∗ P.
Proof.
  iIntros "HQ1 HQ2 #HQP".
  (* [iPoseProof] does not consume "HQP" because a wand is instantiated *)
  iPoseProof ("HQP" with "HQ1") as "HP1".
  iPoseProof ("HQP" with "HQ2") as "HP2".
  iFrame.
Qed.

Lemma test_iDestruct_pose_forall (Φ : nat → PROP) :
  □ (∀ x, Φ x) -∗ Φ 0 ∗ Φ 1.
Proof.
  iIntros "#H".
  (* [iDestruct] does not consume "H" because quantifiers are instantiated *)
  iDestruct ("H" $! 0) as "$".
  iDestruct ("H" $! 1) as "$".
Qed.

Lemma test_iDestruct_or P Q : □ (P ∨ Q) -∗ Q ∨ P.
Proof.
  iIntros "#H".
  (* [iDestruct] consumes "H" because no quantifiers/wands are instantiated *)
  iDestruct "H" as "[H|H]".
  - by iRight.
  - by iLeft.
Qed.
Lemma test_iPoseProof_or P Q : □ (P ∨ Q) -∗ (Q ∨ P) ∗ (P ∨ Q).
Proof.
  iIntros "#H".
  (* [iPoseProof] does not consume "H" despite that no quantifiers/wands are
  instantiated. This makes it different from [iDestruct]. *)
  iPoseProof "H" as "[HP|HQ]".
  - iFrame "H". by iRight.
  - iFrame "H". by iLeft.
Qed.

Lemma test_iDestruct_intuitionistic_affine_bi `{!BiAffine PROP} P Q `{!Persistent P}:
  Q ∗ (Q -∗ P) -∗ P ∗ Q.
Proof. iIntros "[HQ HQP]". iDestruct ("HQP" with "HQ") as "#HP". by iFrame. Qed.

Check "test_iDestruct_spatial".
Lemma test_iDestruct_spatial Q : □ Q -∗ Q.
Proof. iIntros "#HQ". iDestruct "HQ" as "-#HQ". Show. done. Qed.

Check "test_iDestruct_spatial_affine".
Lemma test_iDestruct_spatial_affine Q `{!Affine Q} : □ Q -∗ Q.
Proof.
  iIntros "#-#HQ".
  (* Since [Q] is affine, it should not add an <affine> modality *)
  Show. done.
Qed.

Lemma test_iDestruct_spatial_noop Q : Q -∗ Q.
Proof. iIntros "-#HQ". done. Qed.

Lemma test_iDestruct_exists (Φ: nat → PROP) :
  (∃ y, Φ y) -∗ ∃ n, Φ n.
Proof. iIntros "H". iDestruct "H" as (y) "H". by iExists y. Qed.

Lemma test_iDestruct_exists_automatic (Φ: nat → PROP) :
  (∃ y, Φ y) -∗ ∃ n, Φ n.
Proof.
  iIntros "H".
  iDestruct "H" as (?) "H".
  (* the automatic name should by [y] *)
  by iExists y.
Qed.

Lemma test_iDestruct_exists_automatic_multiple (Φ: nat → PROP) :
  (∃ y n baz, Φ (y+n+baz)) -∗ ∃ n, Φ n.
Proof. iDestruct 1 as (???) "H". by iExists (y+n+baz). Qed.

Lemma test_iDestruct_exists_freshen (y:nat) (Φ: nat → PROP) :
  (∃ y, Φ y) -∗ ∃ n, Φ n.
Proof.
  iIntros "H".
  iDestruct "H" as (?) "H".
  (* the automatic name is the freshened form of [y] *)
  by iExists y0.
Qed.

Check "test_iDestruct_exists_not_exists".
Lemma test_iDestruct_exists_not_exists P :
  P -∗ P.
Proof. Fail iDestruct 1 as (?) "H". Abort.

Lemma test_iDestruct_exists_explicit_name (Φ: nat → PROP) :
  (∃ y, Φ y) -∗ ∃ n, Φ n.
Proof.
  (* give an explicit name that isn't the binder name *)
  iDestruct 1 as (foo) "?".
  by iExists foo.
Qed.

Lemma test_iDestruct_exists_pure (Φ: nat → Prop) :
  ⌜∃ y, Φ y⌝ ⊢@{PROP} ∃ n, ⌜Φ n⌝.
Proof.
  iDestruct 1 as (?) "H".
  by iExists y.
Qed.

Lemma test_iDestruct_exists_and_pure (H: True) P :
  ⌜False⌝ ∧ P -∗ False.
Proof.
  (* this automatic name uses [fresh H] as a sensible default (it's a hypothesis
  in [Prop] and the user cannot supply a name in their code) *)
  iDestruct 1 as (?) "H".
  contradict H0.
Qed.

Check "test_iDestruct_exists_intuitionistic".
Lemma test_iDestruct_exists_intuitionistic P (Φ: nat → PROP) :
  □ (∃ y, Φ y ∧ P) -∗ P.
Proof.
  iDestruct 1 as (?) "#H". Show.
  iDestruct "H" as "[_ $]".
Qed.

Lemma test_iDestruct_exists_freshen_local_name (Φ: nat → PROP) :
  let y := 0 in
  □ (∃ y, Φ y) -∗ ∃ n, Φ (y+n).
Proof.
  iIntros (y) "#H".
  iDestruct "H" as (?) "H".
  iExists y0; auto.
Qed.

(* regression test for #337 *)
Check "test_iDestruct_exists_anonymous".
Lemma test_iDestruct_exists_anonymous P Φ :
  (∃ _:nat, P) ∗ (∃ x:nat, Φ x) -∗ P ∗ ∃ x, Φ x.
Proof.
  iIntros "[HP HΦ]".
  (* this should not use [x] as the default name for the unnamed binder *)
  iDestruct "HP" as (?) "$". Show.
  iDestruct "HΦ" as (x) "HΦ".
  by iExists x.
Qed.

Definition an_exists P : PROP := (∃ (an_exists_name:nat), ▷^an_exists_name P)%I.

(* should use the name from within [an_exists] *)
Lemma test_iDestruct_exists_automatic_def P :
  an_exists P -∗ ∃ k, ▷^k P.
Proof. iDestruct 1 as (?) "H". by iExists an_exists_name. Qed.

(* use an Iris intro pattern [% H] rather than (?) to indicate iExistDestruct *)
Lemma test_exists_intro_pattern_anonymous P (Φ: nat → PROP) :
  P ∗ (∃ y:nat, Φ y) -∗ ∃ x, P ∗ Φ x.
Proof.
  iIntros "[HP1 [% HP2]]".
  iExists y.
  iFrame "HP1 HP2".
Qed.

Lemma test_iIntros_pure (ψ φ : Prop) P : ψ → ⊢ ⌜ φ ⌝ → P → ⌜ φ ∧ ψ ⌝ ∧ P.
Proof. iIntros (??) "H". auto. Qed.

Check "test_iIntros_forall_pure".
Lemma test_iIntros_forall_pure (Ψ: nat → PROP) :
  ⊢ ∀ x : nat, Ψ x → Ψ x.
Proof.
  iIntros "%".
  (* should be a trivial implication now *)
  Show. auto.
Qed.

Lemma test_iIntros_pure_not `{!BiPureForall PROP} : ⊢@{PROP} ⌜ ¬False ⌝.
Proof. by iIntros (?). Qed.

Lemma test_fast_iIntros `{!BiInternalEq PROP} P Q :
  ⊢ ∀ x y z : nat,
    ⌜x = plus 0 x⌝ → ⌜y = 0⌝ → ⌜z = 0⌝ → P → □ Q → foo (x ≡ x).
Proof.
  iIntros (a) "*".
  iIntros "#Hfoo **".
  iIntros "_ //".
Qed.

Lemma test_very_fast_iIntros P :
  ∀ x y : nat, ⊢ ⌜ x = y ⌝ → P -∗ P.
Proof. by iIntros. Qed.

Lemma test_iIntros_automatic_name (Φ: nat → PROP) :
  ∀ y, Φ y -∗ ∃ x, Φ x.
Proof. iIntros (?) "H". by iExists y. Qed.

Lemma test_iIntros_automatic_name_proofmode_intro (Φ: nat → PROP) :
  ∀ y, Φ y -∗ ∃ x, Φ x.
Proof. iIntros "% H". by iExists y. Qed.

(* even an object-level forall should get the right name *)
Lemma test_iIntros_object_forall P :
  P -∗ ∀ (y:unit), P.
Proof. iIntros "H". iIntros (?). destruct y. iAssumption. Qed.

Lemma test_iIntros_object_proofmode_intro (Φ: nat → PROP) :
  ⊢ ∀ y, Φ y -∗ ∃ x, Φ x.
Proof. iIntros "% H". by iExists y. Qed.

Check "test_iIntros_pure_names".
Lemma test_iIntros_pure_names (H:True) P :
  ∀ x y : nat, ⊢ ⌜ x = y ⌝ → P -∗ P.
Proof.
  iIntros (???).
  (* the pure hypothesis should get a sensible [H0] as its name *)
  Show. auto.
Qed.

Definition tc_opaque_test : PROP := tc_opaque (∀ x : nat, ⌜ x = x ⌝)%I.
Lemma test_iIntros_tc_opaque : ⊢ tc_opaque_test.
Proof. by iIntros (x). Qed.

(** Prior to 0b84351c this used to loop, now [iAssumption] instantiates [R] with
[False] and performs false elimination. *)
Lemma test_iAssumption_evar_ex_false : ∃ R, R ⊢ ∀ P, P.
Proof. eexists. iIntros "?" (P). iAssumption. Qed.

Lemma test_iApply_evar P Q R : (∀ Q, Q -∗ P) -∗ R -∗ P.
Proof. iIntros "H1 H2". iApply "H1". iExact "H2". Qed.

Lemma test_iAssumption_affine P Q R `{!Affine P, !Affine R} : P -∗ Q -∗ R -∗ Q.
Proof. iIntros "H1 H2 H3". iAssumption. Qed.

Lemma test_done_goal_evar Q : ∃ P, Q ⊢ P.
Proof. eexists. iIntros "H". Fail done. iAssumption. Qed.

Lemma test_iDestruct_spatial_and P Q1 Q2 : P ∗ (Q1 ∧ Q2) -∗ P ∗ Q1.
Proof. iIntros "[H [? _]]". by iFrame. Qed.

Lemma test_iAssert_persistent P Q : P -∗ Q -∗ True.
Proof.
  iIntros "HP HQ".
  iAssert True%I as "#_". { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as "#_". { Fail iClear "HQ". by iClear "HP". }
  iAssert True%I as %_. { by iClear "HP HQ". }
  iAssert True%I with "[HP]" as %_. { Fail iClear "HQ". by iClear "HP". }
  done.
Qed.

Lemma test_iAssert_persistently P : □ P -∗ True.
Proof.
  iIntros "HP". iAssert (□ P)%I with "[# //]" as "#H". done.
Qed.

Lemma test_iSpecialize_auto_frame P Q R :
  (P -∗ True -∗ True -∗ Q -∗ R) -∗ P -∗ Q -∗ R.
Proof. iIntros "H ? HQ". by iApply ("H" with "[$]"). Qed.

Lemma test_iSpecialize_pure (φ : Prop) Q R :
  φ → (⌜φ⌝ -∗ Q) → ⊢ Q.
Proof. iIntros (HP HPQ). iDestruct (HPQ $! HP) as "?". done. Qed.

Lemma test_iSpecialize_pure_done (φ: Prop) Q :
  φ → (⌜φ⌝ -∗ Q) ⊢ Q.
Proof. iIntros (HP) "HQ". iApply ("HQ" with "[% //]"). Qed.

Check "test_iSpecialize_pure_error".
Lemma test_iSpecialize_not_pure_error P Q :
  (P -∗ Q) ⊢ Q.
Proof. iIntros "HQ". Fail iSpecialize ("HQ" with "[%]"). Abort.

Check "test_iSpecialize_pure_error".
Lemma test_iSpecialize_pure_done_error (φ: Prop) Q :
  (⌜φ⌝ -∗ Q) ⊢ Q.
Proof. iIntros "HQ". Fail iSpecialize ("HQ" with "[% //]"). Abort.

Check "test_iSpecialize_done_error".
Lemma test_iSpecialize_done_error P Q :
  (P -∗ Q) ⊢ Q.
Proof. iIntros "HQ". Fail iSpecialize ("HQ" with "[//]"). Abort.

Lemma test_iSpecialize_Coq_entailment P Q R :
  (⊢ P) → (P -∗ Q) → (⊢ Q).
Proof. iIntros (HP HPQ). iDestruct (HPQ $! HP) as "?". done. Qed.

Lemma test_iSpecialize_intuitionistic P Q R :
  □ P -∗ □ (P -∗ P -∗ P -∗ P -∗ □ P -∗ P -∗ Q) -∗ R -∗ R ∗ □ (P ∗ Q).
Proof.
  iIntros "#HP #H HR".
  (* Test that [H] remains in the intuitionistic context *)
  iSpecialize ("H" with "HP").
  iSpecialize ("H" with "[HP]"); first done.
  iSpecialize ("H" with "[]"); first done.
  iSpecialize ("H" with "[-HR]"); first done.
  iSpecialize ("H" with "[#]"); first done.
  iFrame "HR".
  iSpecialize ("H" with "[-]"); first done.
  by iFrame "#".
Qed.

Lemma test_iSpecialize_intuitionistic_2 P Q R :
  □ P -∗ □ (P -∗ P -∗ P -∗ P -∗ □ P -∗ P -∗ Q) -∗ R -∗ R ∗ □ (P ∗ Q).
Proof.
  iIntros "#HP #H HR".
  (* Test that [H] remains in the intuitionistic context *)
  iSpecialize ("H" with "HP") as #.
  iSpecialize ("H" with "[HP]") as #; first done.
  iSpecialize ("H" with "[]") as #; first done.
  iSpecialize ("H" with "[-HR]") as #; first done.
  iSpecialize ("H" with "[#]") as #; first done.
  iFrame "HR".
  iSpecialize ("H" with "[-]") as #; first done.
  by iFrame "#".
Qed.

Lemma test_iSpecialize_intuitionistic_3 P Q R :
  P -∗ □ (P -∗ Q) -∗ □ (P -∗ <pers> Q) -∗ □ (Q -∗ R) -∗ P ∗ □ (Q ∗ R).
Proof.
  iIntros "HP #H1 #H2 #H3".
  (* Should fail, [Q] is not persistent *)
  Fail iSpecialize ("H1" with "HP") as #.
  (* Should succeed, [<pers> Q] is persistent *)
  iSpecialize ("H2" with "HP") as #.
  (* Should succeed, despite [R] not being persistent, no spatial premises are
  needed to prove [Q] *)
  iSpecialize ("H3" with "H2") as #.
  by iFrame "#".
Qed.

Check "test_iAssert_intuitionistic".
Lemma test_iAssert_intuitionistic `{!BiBUpd PROP} P :
  □ P -∗ □ |==> P.
Proof.
  iIntros "#HP".
  (* Test that [HPupd1] ends up in the intuitionistic context *)
  iAssert (|==> P)%I with "[]" as "#HPupd1"; first done.
  (* This should not work, [|==> P] is not persistent. *)
  Fail iAssert (|==> P)%I with "[#]" as "#HPupd2"; first done.
  done.
Qed.

Lemma test_iSpecialize_evar P : (∀ R, R -∗ R) -∗ P -∗ P.
Proof. iIntros "H HP". iApply ("H" with "[HP]"). done. Qed.

Lemma test_iPure_intro_emp R `{!Affine R} :
  R -∗ emp.
Proof. iIntros "HR". by iPureIntro. Qed.

Lemma test_iEmp_intro P Q R `{!Affine P, !Persistent Q, !Affine R} :
  P -∗ Q → R -∗ emp.
Proof. iIntros "HP #HQ HR". iEmpIntro. Qed.

Lemma test_iPure_intro (φ : nat → Prop) P Q R `{!Affine P, !Persistent Q, !Affine R} :
  φ 0 → P -∗ Q → R -∗ ∃ x : nat, <affine> ⌜ φ x ⌝ ∧ ⌜ φ x ⌝.
Proof. iIntros (?) "HP #HQ HR". iPureIntro; eauto. Qed.
Lemma test_iPure_intro_2 (φ : nat → Prop) P Q R `{!Persistent Q} :
  φ 0 → P -∗ Q → R -∗ ∃ x : nat, <affine> ⌜ φ x ⌝ ∗ ⌜ φ x ⌝.
Proof. iIntros (?) "HP #HQ HR". iPureIntro; eauto. Qed.

(* Ensure that [% ...] works as a pattern when the left-hand side of and/sep is
pure. *)
Lemma test_pure_and_sep_destruct_affine `{!BiAffine PROP} (φ : Prop) P :
  ⌜φ⌝ ∧ (⌜φ⌝ ∗ P) -∗ P.
Proof.
  iIntros "[% [% $]]".
Qed.
Lemma test_pure_and_sep_destruct_1 (φ : Prop) P :
  ⌜φ⌝ ∧ (<affine> ⌜φ⌝ ∗ P) -∗ P.
Proof.
  iIntros "[% [% $]]".
Qed.
Lemma test_pure_and_sep_destruct_2 (φ : Prop) P :
  ⌜φ⌝ ∧ (⌜φ⌝ ∗ <absorb> P) -∗ <absorb> P.
Proof.
  iIntros "[% [% $]]".
Qed.
(* Ensure that [% %] also works when the conjunction is *inside* ⌜...⌝ *)
Lemma test_pure_inner_and_destruct :
  ⌜False ∧ True⌝ ⊢@{PROP} False.
Proof.
  iIntros "[% %]". done.
Qed.

(* Ensure that [% %] works as a pattern for an existential with a pure body. *)
Lemma test_exist_pure_destruct_1 :
  (∃ x, ⌜ x = 0 ⌝) ⊢@{PROP} True.
Proof.
  iIntros "[% %]". done.
Qed.
(* Also test nested existentials where the type of the 2nd depends on the first
(which could cause trouble if we do things in the wrong order) *)
Lemma test_exist_pure_destruct_2 :
  (∃ x (_:x=0), True) ⊢@{PROP} True.
Proof.
  iIntros "(% & % & $)".
Qed.

Lemma test_fresh P Q:
  (P ∗ Q) -∗ (P ∗ Q).
Proof.
  iIntros "H".
  let H1 := iFresh in
  let H2 := iFresh in
  let pat :=constr:(IList [cons (IIdent H1) (cons (IIdent H2) nil)]) in
  iDestruct "H" as pat.
  iFrame.
Qed.

(* Test for issue #288 *)
Lemma test_iExists_unused : ⊢ ∃ P : PROP, ∃ x : nat, P.
Proof.
  iExists _.
  iExists 10.
  iAssert emp%I as "H"; first done.
  iExact "H".
Qed.

(* Check coercions *)
Lemma test_iExist_coercion (P : Z → PROP) : (∀ x, P x) -∗ ∃ x, P x.
Proof. iIntros "HP". iExists (0:nat). iApply ("HP" $! (0:nat)). Qed.

Lemma test_iExist_tc `{Set_ A C} P : ⊢ ∃ x1 x2 : gset positive, P -∗ P.
Proof. iExists {[ 1%positive ]}, ∅. auto. Qed.

Lemma test_iSpecialize_tc P : (∀ x y z : gset positive, P) -∗ P.
Proof.
  iIntros "H".
  (* FIXME: this [unshelve] and [apply _] should not be needed. *)
  unshelve iSpecialize ("H" $! ∅ {[ 1%positive ]} ∅); try apply _. done.
Qed.

Lemma test_iFrame_pure `{!BiInternalEq PROP} {A : ofe} (φ : Prop) (y z : A) :
  φ → <affine> ⌜y ≡ z⌝ -∗ (⌜ φ ⌝ ∧ ⌜ φ ⌝ ∧ y ≡ z : PROP).
Proof. iIntros (Hv) "#Hxy". iFrame (Hv) "Hxy". Qed.

Lemma test_iFrame_disjunction_1 P1 P2 Q1 Q2 :
  BiAffine PROP →
  □ P1 -∗ Q2 -∗ P2 -∗ (P1 ∗ P2 ∗ False ∨ P2) ∗ (Q1 ∨ Q2).
Proof. intros ?. iIntros "#HP1 HQ2 HP2". iFrame "HP1 HQ2 HP2". Qed.
Lemma test_iFrame_disjunction_2 P : P -∗ (True ∨ True) ∗ P.
Proof. iIntros "HP". iFrame "HP". auto. Qed.

Lemma test_iFrame_conjunction_1 P Q :
  P -∗ Q -∗ (P ∗ Q) ∧ (P ∗ Q).
Proof. iIntros "HP HQ". iFrame "HP HQ". Qed.
Lemma test_iFrame_conjunction_2 P Q :
  P -∗ Q -∗ (P ∧ P) ∗ (Q ∧ Q).
Proof. iIntros "HP HQ". iFrame "HP HQ". Qed.

Lemma test_iFrame_later `{!BiAffine PROP} P Q : P -∗ Q -∗ ▷ P ∗ Q.
Proof. iIntros "H1 H2". by iFrame "H1". Qed.

Lemma test_iFrame_affinely_1 P Q `{!Affine P} :
  P -∗ <affine> Q -∗ <affine> (P ∗ Q).
Proof. iIntros "HP HQ". iFrame "HQ". by iModIntro. Qed.
Lemma test_iFrame_affinely_2 P Q `{!Affine P, !Affine Q} :
  P -∗ Q -∗ <affine> (P ∗ Q).
Proof. iIntros "HP HQ". iFrame "HQ". by iModIntro. Qed.

Lemma test_iAssert_modality P : ◇ False -∗ ▷ P.
Proof.
  iIntros "HF".
  iAssert (<affine> False)%I with "[> -]" as %[].
  by iMod "HF".
Qed.

Lemma test_iMod_affinely_timeless P `{!Timeless P} :
  <affine> ▷ P -∗ ◇ <affine> P.
Proof. iIntros "H". iMod "H". done. Qed.

Lemma test_iAssumption_False P : False -∗ P.
Proof. iIntros "H". done. Qed.

Lemma test_iAssumption_coq_1 P Q : (⊢ Q) → <affine> P -∗ Q.
Proof. iIntros (HQ) "_". iAssumption. Qed.

Lemma test_iAssumption_coq_2 P Q : (⊢ □ Q) → <affine> P -∗ ▷ Q.
Proof. iIntros (HQ) "_". iAssumption. Qed.

(* Check instantiation and dependent types *)
Lemma test_iSpecialize_dependent_type (P : ∀ n, vec nat n → PROP) :
  (∀ n v, P n v) -∗ ∃ n v, P n v.
Proof.
  iIntros "H". iExists _, [#10].
  iSpecialize ("H" $! _ [#10]). done.
Qed.

(* Check that typeclasses are not resolved too early *)
Lemma test_TC_resolution `{!BiAffine PROP} (Φ : nat → PROP) l x :
  x ∈ l → ([∗ list] y ∈ l, Φ y) -∗ Φ x.
Proof.
  iIntros (Hp) "HT".
  iDestruct (big_sepL_elem_of _ _ _ Hp with "HT") as "Hp".
  done.
Qed.

Lemma test_eauto_iFrame P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R ∨ False.
Proof. eauto 10 with iFrame. Qed.

Lemma test_iCombine_persistent P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R ∨ False.
Proof. iIntros "HP HQ #HR". iCombine "HR HQ HP HR" as "H". auto. Qed.

Lemma test_iCombine_frame P Q R `{!Persistent R} :
  P -∗ Q -∗ R → R ∗ Q ∗ P ∗ R.
Proof. iIntros "HP HQ #HR". iCombine "HQ HP HR" as "$". by iFrame. Qed.

Lemma test_iNext_evar P : P -∗ True.
Proof.
  iIntros "HP". iAssert (▷ _ -∗ ▷ P)%I as "?"; last done.
  iIntros "?". iNext. iAssumption.
Qed.

Lemma test_iNext_sep1 P Q (R1 := (P ∗ Q)%I) :
  (▷ P ∗ ▷ Q) ∗ R1 -∗ ▷ ((P ∗ Q) ∗ R1).
Proof.
  iIntros "H". iNext.
  rewrite {1 2}(lock R1). (* check whether R1 has not been unfolded *) done.
Qed.

Lemma test_iNext_sep2 P Q : ▷ P ∗ ▷ Q -∗ ▷ (P ∗ Q).
Proof.
  iIntros "H". iNext. iExact "H". (* Check that the laters are all gone. *)
Qed.

Lemma test_iNext_quantifier {A} (Φ : A → A → PROP) :
  (∀ y, ∃ x, ▷ Φ x y) -∗ ▷ (∀ y, ∃ x, Φ x y).
Proof. iIntros "H". iNext. done. Qed.

Lemma text_iNext_Next `{!BiInternalEq PROP} {A B : ofe} (f : A -n> A) x y :
  Next x ≡ Next y -∗ (Next (f x) ≡ Next (f y) : PROP).
Proof. iIntros "H". iNext. by iRewrite "H". Qed.

Lemma test_iFrame_persistent (P Q : PROP) :
  □ P -∗ Q -∗ <pers> (P ∗ P) ∗ (P ∗ Q ∨ Q).
Proof. iIntros "#HP". iFrame "HP". iIntros "$". Qed.

Lemma test_iSplit_persistently P Q : □ P -∗ <pers> (P ∗ P).
Proof. iIntros "#?". by iSplit. Qed.

Lemma test_iSpecialize_persistent P Q : □ P -∗ (<pers> P → Q) -∗ Q.
Proof. iIntros "#HP HPQ". by iSpecialize ("HPQ" with "HP"). Qed.

Lemma test_iDestruct_persistent P (Φ : nat → PROP) `{!∀ x, Persistent (Φ x)}:
  □ (P -∗ ∃ x, Φ x) -∗
  P -∗ ∃ x, Φ x ∗ P.
Proof.
  iIntros "#H HP". iDestruct ("H" with "HP") as (x) "#H2". eauto with iFrame.
Qed.

Lemma test_iLöb `{!BiLöb PROP} P : ⊢ ∃ n, ▷^n P.
Proof.
  iLöb as "IH". iDestruct "IH" as (n) "IH".
  by iExists (S n).
Qed.

Lemma test_iInduction_wf (x : nat) P Q :
  □ P -∗ Q -∗ ⌜ (x + 0 = x)%nat ⌝.
Proof.
  iIntros "#HP HQ".
  iInduction (lt_wf x) as [[|x] _] "IH"; simpl; first done.
  rewrite (inj_iff S). by iApply ("IH" with "[%]"); first lia.
Qed.

Lemma test_iInduction_using (m : gmap nat nat) (Φ : nat → nat → PROP) y :
  ([∗ map] x ↦ i ∈ m, Φ y x) -∗ ([∗ map] x ↦ i ∈ m, emp ∗ Φ y x).
Proof.
  iIntros "Hm". iInduction m as [|i x m] "IH" using map_ind forall(y).
  - by rewrite !big_sepM_empty.
  - rewrite !big_sepM_insert //. iDestruct "Hm" as "[$ ?]".
    by iApply "IH".
Qed.

Lemma test_iIntros_start_proof :
  ⊢@{PROP} True.
Proof.
  (* Make sure iIntros actually makes progress and enters the proofmode. *)
  progress iIntros. done.
Qed.

Lemma test_True_intros : (True : PROP) -∗ True.
Proof.
  iIntros "?". done.
Qed.

Lemma test_iPoseProof_let P Q :
  (let R := True%I in R ∗ P ⊢ Q) →
  P ⊢ Q.
Proof.
  iIntros (help) "HP".
  iPoseProof (help with "[$HP]") as "?". done.
Qed.

Lemma test_iIntros_let P :
  ∀ Q, let R := emp%I in P -∗ R -∗ Q -∗ P ∗ Q.
Proof. iIntros (Q R) "$ _ $". Qed.

Lemma test_iNext_iRewrite `{!BiInternalEq PROP} P Q :
  <affine> ▷ (Q ≡ P) -∗ <affine> ▷ Q -∗ <affine> ▷ P.
Proof.
  iIntros "#HPQ HQ !>". iNext. by iRewrite "HPQ" in "HQ".
Qed.

Lemma test_iIntros_modalities `(!Absorbing P) :
  ⊢ <pers> (▷ ∀  x : nat, ⌜ x = 0 ⌝ → ⌜ x = 0 ⌝ -∗ False -∗ P -∗ P).
Proof.
  iIntros (x ??).
  iIntros "* **". (* Test that fast intros do not work under modalities *)
  iIntros ([]).
Qed.

Lemma test_iIntros_rewrite P (x1 x2 x3 x4 : nat) :
  x1 = x2 → (⌜ x2 = x3 ⌝ ∗ ⌜ x3 ≡ x4 ⌝ ∗ P) -∗ ⌜ x1 = x4 ⌝ ∗ P.
Proof. iIntros (?) "(-> & -> & $)"; auto. Qed.

Lemma test_iNext_affine `{!BiInternalEq PROP} P Q :
  <affine> ▷ (Q ≡ P) -∗ <affine> ▷ Q -∗ <affine> ▷ P.
Proof. iIntros "#HPQ HQ !>". iNext. by iRewrite "HPQ" in "HQ". Qed.

Lemma test_iAlways P Q R :
  □ P -∗ <pers> Q → R -∗ <pers> <affine> <affine> P ∗ □ Q.
Proof. iIntros "#HP #HQ HR". iSplitL. iModIntro. done. iModIntro. done. Qed.

(* A bunch of test cases from #127 to establish that tactics behave the same on
`⌜ φ ⌝ → P` and `∀ _ : φ, P` *)
Lemma test_forall_nondep_1 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". by iApply "Hφ". Qed.
Lemma test_forall_nondep_2 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" with "[% //]"). done. Qed.
Lemma test_forall_nondep_3 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". unshelve iSpecialize ("Hφ" $! _). done. done. Qed.
Lemma test_forall_nondep_4 (φ : Prop) :
  φ → (∀ _ : φ, False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" $! Hφ); done. Qed.

Lemma test_pure_impl_1 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". by iApply "Hφ". Qed.
Lemma test_pure_impl_2 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" with "[% //]"). done. Qed.
Lemma test_pure_impl_3 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". unshelve iSpecialize ("Hφ" $! _). done. done. Qed.
Lemma test_pure_impl_4 (φ : Prop) :
  φ → (⌜φ⌝ → False : PROP) -∗ False.
Proof. iIntros (Hφ) "Hφ". iSpecialize ("Hφ" $! Hφ). done. Qed.

Lemma test_forall_nondep_impl2 (φ : Prop) P :
  φ → P -∗ (∀ _ : φ, P -∗ False : PROP) -∗ False.
Proof.
  iIntros (Hφ) "HP Hφ".
  Fail iSpecialize ("Hφ" with "HP").
  iSpecialize ("Hφ" with "[% //] HP"). done.
Qed.

Lemma test_pure_impl2 (φ : Prop) P :
  φ → P -∗ (⌜φ⌝ → P -∗ False : PROP) -∗ False.
Proof.
  iIntros (Hφ) "HP Hφ".
  Fail iSpecialize ("Hφ" with "HP").
  iSpecialize ("Hφ" with "[% //] HP"). done.
Qed.

Lemma demo_laterN_forall {A} (Φ Ψ: A → PROP) n: (∀ x, ▷^n Φ x) -∗ ▷^n (∀ x, Φ x).
Proof.
  iIntros "H" (w). iApply ("H" $! w).
Qed.

Lemma test_iNext_laterN_later P n : ▷ ▷^n P -∗ ▷^n ▷ P.
Proof. iIntros "H". iNext. by iNext. Qed.
Lemma test_iNext_later_laterN P n : ▷^n ▷ P -∗ ▷ ▷^n P.
Proof. iIntros "H". iNext. by iNext. Qed.
Lemma test_iNext_plus_1 P n1 n2 : ▷ ▷^n1 ▷^n2 P -∗ ▷^n1 ▷^n2 ▷ P.
Proof. iIntros "H". iNext. iNext. by iNext. Qed.
Lemma test_iNext_plus_2 P n m : ▷^n ▷^m P -∗ ▷^(n+m) P.
Proof. iIntros "H". iNext. done. Qed.
Check "test_iNext_plus_3".
Lemma test_iNext_plus_3 P Q n m k :
  ▷^m ▷^(2 + S n + k) P -∗ ▷^m ▷ ▷^(2 + S n) Q -∗ ▷^k ▷ ▷^(S (S n + S m)) (P ∗ Q).
Proof. iIntros "H1 H2". iNext. iNext. iNext. iFrame. Show. iModIntro. done. Qed.

Lemma test_iNext_unfold P Q n m (R := (▷^n P)%I) :
  R ⊢ ▷^m True.
Proof.
  iIntros "HR". iNext.
  match goal with |-  context [ R ] => idtac | |- _ => fail end.
  done.
Qed.

Lemma test_iNext_fail P Q a b c d e f g h i j:
  ▷^(a + b) ▷^(c + d + e) P -∗ ▷^(f + g + h + i + j) True.
Proof. iIntros "H". iNext. done. Qed.

Lemma test_specialize_affine_pure (φ : Prop) P :
  φ → (<affine> ⌜φ⌝ -∗ P) ⊢ P.
Proof.
  iIntros (Hφ) "H". by iSpecialize ("H" with "[% //]").
Qed.

Lemma test_assert_affine_pure (φ : Prop) P :
  φ → P ⊢ P ∗ <affine> ⌜φ⌝.
Proof. iIntros (Hφ). iAssert (<affine> ⌜φ⌝)%I with "[%]" as "$"; auto. Qed.
Lemma test_assert_pure (φ : Prop) P :
  φ → P ⊢ P ∗ ⌜φ⌝.
Proof. iIntros (Hφ). iAssert ⌜φ⌝%I with "[%]" as "$"; auto with iFrame. Qed.

Lemma test_specialize_very_nested (φ : Prop) P P2 Q R1 R2 :
  φ →
  P -∗ P2 -∗
  (<affine> ⌜ φ ⌝ -∗ P2 -∗ Q) -∗
  (P -∗ Q -∗ R1) -∗
  (R1 -∗ True -∗ R2) -∗
  R2.
Proof.
  iIntros (?) "HP HP2 HQ H1 H2".
  by iApply ("H2" with "(H1 HP (HQ [% //] [-])) [//]").
Qed.

Lemma test_specialize_very_very_nested P1 P2 P3 P4 P5 :
  □ P1 -∗
  □ (P1 -∗ P2) -∗
  (P2 -∗ P2 -∗ P3) -∗
  (P3 -∗ P4) -∗
  (P4 -∗ P5) -∗
  P5.
Proof.
  iIntros "#H #H1 H2 H3 H4".
  by iSpecialize ("H4" with "(H3 (H2 (H1 H) (H1 H)))").
Qed.

Check "test_specialize_nested_intuitionistic".
Lemma test_specialize_nested_intuitionistic (φ : Prop) P P2 Q R1 R2 :
  φ →
  □ P -∗ □ (P -∗ Q) -∗ (Q -∗ Q -∗ R2) -∗ R2.
Proof.
  iIntros (?) "#HP #HQ HR".
  iSpecialize ("HR" with "(HQ HP) (HQ HP)").
  Show.
  done.
Qed.

Lemma test_specialize_intuitionistic P Q :
  □ P -∗ □ (P -∗ Q) -∗ □ Q.
Proof. iIntros "#HP #HQ". iSpecialize ("HQ" with "HP"). done. Qed.

Lemma test_iEval x y : ⌜ (y + x)%nat = 1 ⌝ -∗ ⌜ S (x + y) = 2%nat ⌝ : PROP.
Proof.
  iIntros (H).
  iEval (rewrite (Nat.add_comm x y) // H).
  done.
Qed.

Lemma test_iEval_precedence : True ⊢ True : PROP.
Proof.
  iIntros.
  (* Ensure that in [iEval (a); b], b is not parsed as part of the argument of [iEval]. *)
  iEval (rewrite /=); iPureIntro; exact I.
Qed.

Check "test_iSimpl_in".
Lemma test_iSimpl_in x y : ⌜ (3 + x)%nat = y ⌝ -∗ ⌜ S (S (S x)) = y ⌝ : PROP.
Proof. iIntros "H". iSimpl in "H". Show. done. Qed.

Lemma test_iSimpl_in_2 x y z :
  ⌜ (3 + x)%nat = y ⌝ -∗ ⌜ (1 + y)%nat = z ⌝ -∗
  ⌜ S (S (S x)) = y ⌝ : PROP.
Proof. iIntros "H1 H2". iSimpl in "H1 H2". Show. done. Qed.

Lemma test_iSimpl_in3 x y z :
  ⌜ (3 + x)%nat = y ⌝ -∗ ⌜ (1 + y)%nat = z ⌝ -∗
  ⌜ S (S (S x)) = y ⌝ : PROP.
Proof. iIntros "#H1 H2". iSimpl in "#". Show. done. Qed.

Check "test_iSimpl_in4".
Lemma test_iSimpl_in4 x y : ⌜ (3 + x)%nat = y ⌝ -∗ ⌜ S (S (S x)) = y ⌝ : PROP.
Proof. iIntros "H". Fail iSimpl in "%". by iSimpl in "H". Qed.

Lemma test_iPureIntro_absorbing (φ : Prop) :
  φ → ⊢@{PROP} <absorb> ⌜φ⌝.
Proof. intros ?. iPureIntro. done. Qed.

Check "test_iFrame_later_1".
Lemma test_iFrame_later_1 P Q : P ∗ ▷ Q -∗ ▷ (P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Show. auto. Qed.

Check "test_iFrame_later_2".
Lemma test_iFrame_later_2 P Q : ▷ P ∗ ▷ Q -∗ ▷ (▷ P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Show. auto. Qed.

Lemma test_with_ident P Q R : P -∗ Q -∗ (P -∗ Q -∗ R) -∗ R.
Proof.
  iIntros "? HQ H".
  iMatchHyp (fun H _ =>
    iApply ("H" with [spec_patterns.SIdent H []; spec_patterns.SIdent "HQ" []])).
Qed.

Lemma iFrame_with_evar_r P Q :
  ∃ R, (P -∗ Q -∗ P ∗ R) ∧ R = Q.
Proof.
  eexists. split. iIntros "HP HQ". iFrame. iApply "HQ". done.
Qed.
Lemma iFrame_with_evar_l P Q :
  ∃ R, (P -∗ Q -∗ R ∗ P) ∧ R = Q.
Proof.
  eexists. split. iIntros "HP HQ". Fail iFrame "HQ".
  iSplitR "HP"; iAssumption. done.
Qed.
Lemma iFrame_with_evar_persistent P Q :
  ∃ R, (P -∗ □ Q -∗ P ∗ R ∗ Q) ∧ R = emp%I.
Proof.
  eexists. split. iIntros "HP #HQ". iFrame "HQ HP". iEmpIntro. done.
Qed.

Lemma test_iAccu P Q R S :
  ∃ PP, (□P -∗ Q -∗ R -∗ S -∗ PP) ∧ PP = (Q ∗ R ∗ S)%I.
Proof.
  eexists. split. iIntros "#? ? ? ?". iAccu. done.
Qed.

Lemma test_iAssumption_evar P : ∃ R, (R ⊢ P) ∧ R = P.
Proof.
  eexists. split.
  - iIntros "H". iAssumption.
  (* Now verify that the evar was chosen as desired (i.e., it should not pick False). *)
  - reflexivity.
Qed.

Lemma test_iAssumption_False_no_loop : ∃ R, R ⊢ ∀ P, P.
Proof. eexists. iIntros "?" (P). done. Qed.

Lemma test_apply_affine_impl `{!BiPlainly PROP} (P : PROP) :
  P -∗ (∀ Q : PROP, ■ (Q -∗ <pers> Q) → ■ (P -∗ Q) → Q).
Proof. iIntros "HP" (Q) "_ #HPQ". by iApply "HPQ". Qed.

Lemma test_apply_affine_wand `{!BiPlainly PROP} (P : PROP) :
  P -∗ (∀ Q : PROP, <affine> ■ (Q -∗ <pers> Q) -∗ <affine> ■ (P -∗ Q) -∗ Q).
Proof. iIntros "HP" (Q) "_ #HPQ". by iApply "HPQ". Qed.

Lemma test_and_sep (P Q R : PROP) : P ∧ (Q ∗ □ R) ⊢ (P ∧ Q) ∗ □ R.
Proof.
  iIntros "H". repeat iSplit.
  - iDestruct "H" as "[$ _]".
  - iDestruct "H" as "[_ [$ _]]".
  - iDestruct "H" as "[_ [_ #$]]".
Qed.

Lemma test_and_sep_2 (P Q R : PROP) `{!Persistent R, !Affine R} :
  P ∧ (Q ∗ R) ⊢ (P ∧ Q) ∗ R.
Proof.
  iIntros "H". repeat iSplit.
  - iDestruct "H" as "[$ _]".
  - iDestruct "H" as "[_ [$ _]]".
  - iDestruct "H" as "[_ [_ #$]]".
Qed.

Check "test_and_sep_affine_bi".
Lemma test_and_sep_affine_bi `{!BiAffine PROP} P Q : □ P ∧ Q ⊢ □ P ∗ Q.
Proof.
  iIntros "[??]". iSplit; last done. Show. done.
Qed.

Check "test_big_sepL_simpl".
Lemma test_big_sepL_simpl x (l : list nat) P :
   P -∗
  ([∗ list] k↦y ∈ l, <affine> ⌜ y = y ⌝) -∗
  ([∗ list] y ∈ x :: l, <affine> ⌜ y = y ⌝) -∗
  P.
Proof. iIntros "HP ??". Show. simpl. Show. done. Qed.

Check "test_big_sepL2_simpl".
Lemma test_big_sepL2_simpl x1 x2 (l1 l2 : list nat) P :
  P -∗
  ([∗ list] k↦y1;y2 ∈ []; l2, <affine> ⌜ y1 = y2 ⌝) -∗
  ([∗ list] y1;y2 ∈ x1 :: l1; (x2 :: l2) ++ l2, <affine> ⌜ y1 = y2 ⌝) -∗
  P ∨ ([∗ list] y1;y2 ∈ x1 :: l1; x2 :: l2, True).
Proof. iIntros "HP ??". Show. simpl. Show. by iLeft. Qed.

Check "test_big_sepL2_iDestruct".
Lemma test_big_sepL2_iDestruct (Φ : nat → nat → PROP) x1 x2 (l1 l2 : list nat) :
  ([∗ list] y1;y2 ∈ x1 :: l1; x2 :: l2, Φ y1 y2) -∗
  <absorb> Φ x1 x2.
Proof. iIntros "[??]". Show. iFrame. Qed.

Lemma test_big_sepL2_iFrame (Φ : nat → nat → PROP) (l1 l2 : list nat) P :
  Φ 0 10 -∗ ([∗ list] y1;y2 ∈ l1;l2, Φ y1 y2) -∗
  ([∗ list] y1;y2 ∈ (0 :: l1);(10 :: l2), Φ y1 y2).
Proof. iIntros "$ ?". iFrame. Qed.

Lemma test_lemma_1 (b : bool) :
  emp ⊢@{PROP} □?b True.
Proof. destruct b; simpl; eauto. Qed.
Check "test_reducing_after_iDestruct".
Lemma test_reducing_after_iDestruct : emp ⊢@{PROP} True.
Proof.
  iIntros "H". iDestruct (test_lemma_1 true with "H") as "H". Show. done.
Qed.

Lemma test_lemma_2 (b : bool) :
  □?b emp ⊢@{PROP} emp.
Proof. destruct b; simpl; eauto. Qed.
Check "test_reducing_after_iApply".
Lemma test_reducing_after_iApply : emp ⊢@{PROP} emp.
Proof.
  iIntros "#H". iApply (test_lemma_2 true). Show. auto.
Qed.

Lemma test_lemma_3 (b : bool) :
  □?b emp ⊢@{PROP} ⌜b = b⌝.
Proof. destruct b; simpl; eauto. Qed.
Check "test_reducing_after_iApply_late_evar".
Lemma test_reducing_after_iApply_late_evar : emp ⊢@{PROP} ⌜true = true⌝.
Proof.
  iIntros "#H". iApply (test_lemma_3). Show. auto.
Qed.

Section wandM.
  Import proofmode.base.
  Check "test_wandM".
  Lemma test_wandM mP Q R :
    (mP -∗? Q) -∗ (Q -∗ R) -∗ (mP -∗? R).
  Proof.
    iIntros "HPQ HQR HP". Show.
    iApply "HQR". iApply "HPQ". Show.
    done.
  Qed.
End wandM.

Definition modal_if_def b (P : PROP) :=
  (□?b P)%I.
Lemma modal_if_lemma1 b P :
  False -∗ □?b P.
Proof. iIntros "?". by iExFalso. Qed.
Lemma test_iApply_prettification1 (P : PROP) :
  False -∗ modal_if_def true P.
Proof.
  (* Make sure the goal is not prettified before [iApply] unifies. *)
  iIntros "?". rewrite /modal_if_def. iApply modal_if_lemma1. iAssumption.
Qed.
Lemma modal_if_lemma2 P :
  False -∗ □?false P.
Proof. iIntros "?". by iExFalso. Qed.
Lemma test_iApply_prettification2 (P  : PROP) :
  False -∗ ∃ b, □?b P.
Proof.
  (* Make sure the conclusion of the lemma is not prettified too early. *)
  iIntros "?". iExists _. iApply modal_if_lemma2. done.
Qed.

Lemma test_iDestruct_clear P Q R :
  P -∗ (Q ∗ R) -∗ True.
Proof.
  iIntros "HP HQR". iDestruct "HQR" as "{HP} [HQ HR]". done.
Qed.

Lemma test_iSpecialize_bupd `{BiBUpd PROP} A (a : A) (P : A -> PROP) :
  (|==> ∀ x, P x) ⊢ |==> P a.
Proof.
  iIntros "H". iSpecialize ("H" $! a). done.
Qed.

Lemma test_iSpecialize_fupd `{BiFUpd PROP} A (a : A) (P : A -> PROP) E1 E2 :
  (|={E1, E2}=> ∀ x, P x) ⊢ |={E1, E2}=> P a.
Proof.
  iIntros "H". iSpecialize ("H" $! a). done.
Qed.

Lemma test_iDestruct_and_bupd `{BiBUpd PROP} (P Q : PROP) :
  (|==> P ∧ Q) ⊢ |==> P.
Proof.
  iIntros "[P _]". done.
Qed.

Lemma test_iDestruct_and_fupd `{BiFUpd PROP} (P Q : PROP) E1 E2 :
  (|={E1, E2}=> P ∧ Q) ⊢ |={E1, E2}=> P.
Proof.
  iIntros "[P _]". done.
Qed.

Lemma test_iModIntro_make_laterable `{BiAffine PROP} (P Q : PROP) :
  Laterable Q →
  P -∗ Q -∗ make_laterable (▷ P ∗ Q).
Proof.
  iIntros (?) "HP HQ". iModIntro. Show. by iFrame.
Qed.

End tests.

Section parsing_tests.
Context {PROP : bi}.
Implicit Types P : PROP.

(** Test notations for (bi)entailment and internal equality. These tests are
especially extensive because of past problems such as
https://gitlab.mpi-sws.org/iris/iris/-/issues/302. *)
Lemma test_bi_emp_valid : ⊢@{PROP} True.
Proof. naive_solver. Qed.

Lemma test_bi_emp_valid_parens : (⊢@{PROP} True) ∧ ((⊢@{PROP} True)).
Proof. naive_solver. Qed.

Lemma test_bi_emp_valid_parens_space_open : ( ⊢@{PROP} True).
Proof. naive_solver. Qed.

Lemma test_bi_emp_valid_parens_space_close : (⊢@{PROP} True ).
Proof. naive_solver. Qed.

Lemma test_entails_annot_sections P :
  (P ⊢@{PROP} P) ∧ (⊢@{PROP}) P P ∧ (P ⊢.) P ∧ (.⊢ P) P ∧
  (P ⊣⊢@{PROP} P) ∧ (⊣⊢@{PROP}) P P ∧ (P ⊣⊢.) P ∧ (.⊣⊢ P) P.
Proof. naive_solver. Qed.

Lemma test_entails_annot_sections_parens P :
  ((P ⊢@{PROP} P)) ∧ ((⊢@{PROP})) P P ∧ ((P ⊢.)) P ∧ ((.⊢ P)) P ∧
  ((P ⊣⊢@{PROP} P)) ∧ ((⊣⊢@{PROP})) P P ∧ ((P ⊣⊢.)) P ∧ ((.⊣⊢ P)) P.
Proof. naive_solver. Qed.

Lemma test_entails_annot_sections_space_open P :
  ( P ⊢@{PROP} P) ∧ ( P ⊢.) P ∧
  ( P ⊣⊢@{PROP} P) ∧ ( P ⊣⊢.) P.
Proof. naive_solver. Qed.

Lemma test_entails_annot_sections_space_close P :
  (P ⊢@{PROP} P ) ∧ (⊢@{PROP} ) P P ∧ (.⊢ P ) P ∧
  (P ⊣⊢@{PROP} P ) ∧ (⊣⊢@{PROP} ) P P ∧ (.⊣⊢ P ) P.
Proof. naive_solver. Qed.

Lemma test_bi_internal_eq_annot_sections `{!BiInternalEq PROP} P :
  ⊢@{PROP}
    P ≡@{PROP} P ∧ (≡@{PROP}) P P ∧ (P ≡.) P ∧ (.≡ P) P ∧
    ((P ≡@{PROP} P)) ∧ ((≡@{PROP})) P P ∧ ((P ≡.)) P ∧ ((.≡ P)) P ∧
    ( P ≡@{PROP} P) ∧ ( P ≡.) P ∧
    (P ≡@{PROP} P ) ∧ (≡@{PROP} ) P P ∧ (.≡ P ) P.
Proof. naive_solver. Qed.
End parsing_tests.

Section printing_tests.
Context {PROP : bi} `{!BiFUpd PROP}.
Implicit Types P Q R : PROP.

Check "elim_mod_accessor".
Lemma elim_mod_accessor {X : Type} E1 E2 α (β : X → PROP) γ :
  accessor (fupd E1 E2) (fupd E2 E1) α β γ -∗ |={E1}=> True.
Proof. iIntros ">Hacc". Show. Abort.

(* Test line breaking of long assumptions. *)
Section linebreaks.
Check "print_long_line_1".
Lemma print_long_line_1 (P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P : PROP) :
  P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P ∗
  P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P
  -∗ True.
Proof.
  iIntros "HP". Show. Undo. iIntros "?". Show.
Abort.

(* This is specifically crafted such that not having the printing box in
   the proofmode notation breaks the output. *)
Local Notation "'TESTNOTATION' '{{' P '|' Q '}' '}'" := (P ∧ Q)%I
  (format "'TESTNOTATION'  '{{'  P  '|'  '/' Q  '}' '}'") : bi_scope.
Check "print_long_line_2".
Lemma print_long_line_2 (P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P : PROP) :
  TESTNOTATION {{ P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P | P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P_P }}
  -∗ True.
Proof.
  iIntros "HP". Show. Undo. iIntros "?". Show.
Abort.

Check "long_impl".
Lemma long_impl (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  ⊢ PPPPPPPPPPPPPPPPP → (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ).
Proof.
  iStartProof. Show.
Abort.
Check "long_impl_nested".
Lemma long_impl_nested (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  ⊢ PPPPPPPPPPPPPPPPP → (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ) → (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ).
Proof.
  iStartProof. Show.
Abort.
Check "long_wand".
Lemma long_wand (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  ⊢ PPPPPPPPPPPPPPPPP -∗ (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ).
Proof.
  iStartProof. Show.
Abort.
Check "long_wand_nested".
Lemma long_wand_nested (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  ⊢ PPPPPPPPPPPPPPPPP -∗ (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ) -∗ (QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ).
Proof.
  iStartProof. Show.
Abort.
Check "long_fupd".
Lemma long_fupd E (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  PPPPPPPPPPPPPPPPP ={E}=∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ.
Proof.
  iStartProof. Show.
Abort.
Check "long_fupd_nested".
Lemma long_fupd_nested E1 E2 (PPPPPPPPPPPPPPPPP QQQQQQQQQQQQQQQQQQ : PROP) :
  PPPPPPPPPPPPPPPPP ={E1,E2}=∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ
  ={E1,E2}=∗ QQQQQQQQQQQQQQQQQQ ∗ QQQQQQQQQQQQQQQQQQ.
Proof.
  iStartProof. Show.
Abort.
End linebreaks.

End printing_tests.

(** Test error messages *)
Section error_tests.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Check "iStopProof_not_proofmode".
Lemma iStopProof_not_proofmode : 10 = 10.
Proof. Fail iStopProof. Abort.

Check "iAlways_spatial_non_empty".
Lemma iAlways_spatial_non_empty P :
  P -∗ □ emp.
Proof. iIntros "HP". Fail iModIntro. Abort.

Check "iDestruct_bad_name".
Lemma iDestruct_bad_name P :
  P -∗ P.
Proof. iIntros "HP". Fail iDestruct "HQ" as "HP". Abort.

Check "iIntros_dup_name".
Lemma iIntros_dup_name P Q :
  P -∗ Q -∗ ∀ x y : (), P.
Proof.
  iIntros "HP". Fail iIntros "HP".
  iIntros "HQ" (x). Fail iIntros (x).
Abort.

Check "iIntros_pure_not_forall".
Lemma iIntros_pure_not_forall P Q :
  P -∗ Q.
Proof.
  Fail iIntros (?).
Abort.

Check "iSplitL_one_of_many".
Lemma iSplitL_one_of_many P :
  P -∗ P -∗ P ∗ P.
Proof.
  iIntros "HP1 HP2". Fail iSplitL "HP1 HPx". Fail iSplitL "HPx HP1".
Abort.

Check "iSplitR_one_of_many".
Lemma iSplitR_one_of_many P :
  P -∗ P -∗ P ∗ P.
Proof.
  iIntros "HP1 HP2". Fail iSplitR "HP1 HPx". Fail iSplitR "HPx HP1".
Abort.

Check "iSplitL_non_splittable".
Lemma iSplitL_non_splittable P :
  ⊢ P.
Proof.
  Fail iSplitL "".
Abort.

Check "iSplitR_non_splittable".
Lemma iSplitR_non_splittable P :
  ⊢ P.
Proof.
  Fail iSplitR "".
Abort.

Check "iCombine_fail".
Lemma iCombine_fail P:
  P -∗ P -∗ P ∗ P.
Proof.
  iIntros "HP1 HP2". Fail iCombine "HP1 HP3" as "HP".
Abort.

Check "iSpecialize_bad_name1_fail".
Lemma iSpecialize_bad_name1_fail P Q:
  (P -∗ Q) -∗ P -∗ Q.
Proof.
  iIntros "HW HP". Fail iSpecialize ("H" with "HP").
Abort.

Check "iSpecialize_bad_name2_fail".
Lemma iSpecialize_bad_name2_fail P Q:
  (P -∗ Q) -∗ P -∗ Q.
Proof.
  iIntros "HW HP". Fail iSpecialize ("HW" with "H").
Abort.

Check "iExact_fail".
Lemma iExact_fail P Q :
  <affine> P -∗ Q -∗ <affine> P.
Proof.
  iIntros "HP". Fail iExact "HQ". iIntros "HQ". Fail iExact "HQ". Fail iExact "HP".
Abort.

Check "iClear_fail".
Lemma iClear_fail P : P -∗ P.
Proof. Fail iClear "HP". iIntros "HP". Fail iClear "HP". Abort.

Check "iSpecializeArgs_fail".
Lemma iSpecializeArgs_fail P :
  (∀ x : nat, P) -∗ P.
Proof. iIntros "HP". Fail iSpecialize ("HP" $! true). Abort.

Check "iStartProof_fail".
Lemma iStartProof_fail : 0 = 0.
Proof. Fail iStartProof. Abort.

Check "iPoseProof_fail".
Lemma iPoseProof_fail P : P -∗ P.
Proof.
  Fail iPoseProof (eq_refl 0) as "H".
  iIntros "H". Fail iPoseProof bi.and_intro as "H".
Abort.

Check "iPoseProof_not_found_fail".
Lemma iPoseProof_not_found_fail P : P -∗ P.
Proof.
  iIntros "H". Fail iPoseProof "Hx" as "H1".
Abort.

Check "iPoseProof_not_found_fail2".
Lemma iPoseProof_not_found_fail2 P Q (H: P -∗ Q) : P -∗ Q.
Proof.
  iIntros "HP". Fail iPoseProof (H with "[HQ]") as "H".
Abort.

Check "iPoseProofCoreHyp_not_found_fail".
Lemma iPoseProofCoreHyp_not_found_fail P : P -∗ P -∗ P.
Proof.
  iIntros "H". Fail iPoseProofCoreHyp "Hx" as "H1".
Abort.

Check "iPoseProofCoreHyp_not_fresh_fail".
Lemma iPoseProofCoreHyp_not_fresh_fail P : P -∗ P -∗ P.
Proof.
  iIntros "H0 H1". Fail iPoseProofCoreHyp "H0" as "H1".
Abort.

Check "iRevert_fail".
Lemma iRevert_fail P : P -∗ P.
Proof. Fail iRevert "H". Abort.

Check "iDestruct_fail".
Lemma iDestruct_fail P : P -∗ <absorb> P.
Proof.
  iIntros "HP".
  Fail iDestruct "HP" as "[{HP}]".
  (* IDone is unsupported (see issue #380) *)
  Fail iDestruct "HP" as "// H".
  (* fails due to not having "one proper intro pattern" (see issue #380) *)
  Fail iDestruct "HP" as "HP //".
  (* both of these work *)
  iDestruct "HP" as "HP /=".
  iDestruct "HP" as "/= HP".
  Fail iDestruct "HP" as "[HP HQ HR]".
  Fail iDestruct "HP" as "[HP|HQ|HR]".
  Fail iDestruct "HP" as "[HP]".
  Fail iDestruct "HP" as "[HP HQ|HR]".
Abort.

Check "iOrDestruct_fail".
Lemma iOrDestruct_fail P : (P ∨ P) -∗ P -∗ P.
Proof.
  iIntros "H H'". Fail iOrDestruct "H" as "H'" "H2". Fail iOrDestruct "H" as "H1" "H'".
Abort.

Check "iApply_fail".
Lemma iApply_fail P Q : P -∗ Q.
Proof. iIntros "HP". Fail iApply "HP". Abort.

Check "iApply_fail_not_affine_1".
Lemma iApply_fail_not_affine_1 P Q : P -∗ Q -∗ Q.
Proof. iIntros "HP HQ". Fail iApply "HQ". Abort.

Check "iIntros_fail_nonempty_spatial".
Lemma iIntro_fail_nonempty_spatial P Q : P -∗ P → Q.
Proof. Fail iIntros "? HP". Abort.

Check "iIntros_fail_not_fresh".
Lemma iIntro_fail_not_fresh P Q : P -∗ P -∗ Q.
Proof. Fail iIntros "HP HP". Abort.

Check "iIntros_fail_nothing_to_introduce".
Lemma iIntro_fail_nothing_to_introduce P Q : P -∗ Q.
Proof. Fail iIntros "HP HQ". Abort.

Check "iApply_fail_not_affine_2".
Lemma iApply_fail_not_affine_2 P Q R : P -∗ R -∗ (R -∗ Q) -∗ Q.
Proof. iIntros "HP HR HQ". Fail iApply ("HQ" with "HR"). Abort.

Check "iAssumption_fail_not_affine_1".
Lemma iAssumption_fail_not_affine_1 P Q : P -∗ Q -∗ Q.
Proof. iIntros "HP HQ". Fail iAssumption. Abort.

Check "iAssumption_fail_not_affine_2".
Lemma iAssumption_fail_not_affine_2 P Q : (⊢ Q) → P -∗ Q.
Proof. iIntros (HQ) "HP". Fail iAssumption. Abort.

Check "iRevert_wrong_var".
Lemma iRevert_wrong_var (k : nat) (Φ : nat → PROP) : ⊢ Φ (S k).
Proof.
  Fail iRevert (k1).
  Fail iLöb as "IH" forall (k1).
Abort.

Check "iRevert_dup_var".
Lemma iRevert_dup_var (k : nat) (Φ : nat → PROP) : ⊢ Φ (S k).
Proof. Fail iRevert (k k). Abort.

Check "iRevert_dep_var_coq".
Lemma iRevert_dep_var_coq (k : nat) (Φ : nat → PROP) : k = 0 → ⊢ Φ (S k).
Proof. intros Hk. Fail iRevert (k). Abort.

Check "iRevert_dep_var".
Lemma iRevert_dep_var (k : nat) (Φ : nat → PROP) : Φ k -∗ Φ (S k).
Proof. iIntros "Hk". Fail iRevert (k). Abort.

Check "iLöb_no_BiLöb".
Lemma iLöb_no_BiLöb P : ⊢ P.
Proof. Fail iLöb as "IH". Abort.

Check "iMod_mask_mismatch".
Lemma iMod_mask_mismatch `{!BiFUpd PROP} E1 E2 (P : PROP) :
  (|={E2}=> P) ⊢ |={E1}=> P.
Proof.
  Fail iIntros ">HP".
  iIntros "HP". Fail iMod "HP".
Abort.

Check "iModIntro_mask_mismatch".
Lemma iMod_mask_mismatch `{!BiFUpd PROP} E1 E2 (P : PROP) :
  ⊢ |={E1,E2}=> P.
Proof.
  Fail iModIntro.
  Fail iIntros "!>".
Abort.

Check "iRevert_wrong_sel_pat".
Lemma iRevert_wrong_sel_pat (n m : nat) (P Q : nat → PROP) :
  ⌜ n = m ⌝ -∗ P n -∗ P m.
Proof.
  Fail iRevert n.
Abort.

Check "iInduction_wrong_sel_pat".
Lemma iInduction_wrong_sel_pat (n m : nat) (P Q : nat → PROP) :
  ⌜ n = m ⌝ -∗ P n -∗ P m.
Proof.
  Fail iInduction n as [|n] "IH" forall m.
Abort.

End error_tests.

Section pure_name_tests.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Check "test_pure_name".
Lemma test_pure_name P (φ1 φ2 : Prop) (Himpl : φ1 → φ2) :
  P ∗ ⌜φ1⌝ -∗ P ∗ ⌜φ2⌝.
Proof.
  iIntros "[HP %HP2]".
  Show.
  iFrame.
  iPureIntro.
  exact (Himpl HP2).
Qed.

Lemma test_iIntros_forall_pure_named (Ψ: nat → PROP) :
  (∀ x : nat, Ψ x) ⊢ ∀ x : nat, Ψ x.
Proof. iIntros "HP". iIntros "%y". iApply ("HP" $! y). Qed.

Check "test_not_fresh".
Lemma test_not_fresh P (φ : Prop) (H : φ) :
  P ∗ ⌜ φ ⌝ -∗ P ∗ ⌜ φ ⌝.
Proof.
  Fail iIntros "[H %H]".
Abort.

Lemma test_exists_intro_pattern P (Φ: nat → PROP) :
  P ∗ (∃ y:nat, Φ y) -∗ ∃ x, P ∗ Φ x.
Proof.
  iIntros "[HP1 [%yy HP2]]".
  iExists yy.
  iFrame "HP1 HP2".
Qed.

End pure_name_tests.

Section tactic_tests.
Context {PROP : bi}.
Implicit Types P Q R : PROP.
Implicit Types φ : nat → PROP.
Implicit Types Ψ : nat → nat → PROP.

Check "test_iRename_select1".
Lemma test_iRename_select1 P Q :
  □ (P -∗ Q) -∗ □ P -∗ □ Q.
Proof.
  iIntros "#? #?".
  iRename select P into "H1".
  (* The following fails since there are no matching hypotheses. *)
  Fail iRename select (_ ∗ _)%I into "?".
  iRename select (_ -∗ _)%I into "H2".
  iDestruct ("H2" with "H1") as "$".
Qed.

Lemma test_iRename_select2 P Q :
  (P -∗ Q) -∗ P -∗ Q.
Proof.
  iIntros "??".
  iRename select P into "H1".
  iRename select (_ -∗ _)%I into "H2".
  by iApply "H2".
Qed.

Lemma test_iDestruct_select1 P Q :
  (P ∗ Q) -∗ Q ∗ P.
Proof.
  iIntros "?".
  iDestruct select (_ ∗ _)%I as "[$ $]".
Qed.

Check "test_iDestruct_select2".
Lemma test_iDestruct_select2 φ P :
  (∃ x, P ∗ φ x) -∗ ∃ x, φ x ∗ P.
Proof.
  iIntros "?".
  (* The following fails since [Φ n] is not pure. *)
  Fail iDestruct select (∃ _, _)%I as (n) "[H1 %]".
  iDestruct select (∃ _, _)%I as (n) "[H1 H2]".
  iExists n. iFrame.
Qed.

Lemma test_iDestruct_select3 Ψ P :
  (∃ x y, P ∗ Ψ x y) -∗ ∃ x y, Ψ x y ∗ P.
Proof.
  iIntros "?".
  iDestruct select (∃ _, _)%I as (n m) "[H1 H2]".
  iExists n, m. iFrame.
Qed.

Lemma test_iDestruct_select4 φ :
  □ (∃ x, φ x) -∗ □ (∃ x, φ x).
Proof.
  iIntros "#?".
  iDestruct select (∃ _, _)%I as (n) "H".
  by iExists n.
Qed.

Lemma test_iDestruct_select5 (φ : nat → Prop) P :
  P -∗ ⌜∃ n, φ n⌝ -∗ ∃ n, P ∗ ⌜φ n⌝ ∗ ⌜φ n⌝.
Proof.
  iIntros "??".
  iDestruct select ⌜_⌝%I as %[n H].
  iExists n. iFrame. by iSplit.
Qed.

Check "test_iDestruct_select_no_backtracking".
Lemma test_iDestruct_select_no_backtracking P Q :
  □ P -∗ Q -∗ Q.
Proof.
  iIntros "??".
  (* The following must fail since the pattern will match [Q], which cannot be
     introduced in the intuitionistic context. This demonstrates that tactics
     based on [iSelect] only act on the last hypothesis of the intuitionistic
     or spatial context that matches the pattern, and they do not backtrack if
     the requested action fails on the hypothesis. *)
  Fail iDestruct select _ as "#X".
  done.
Qed.

Lemma test_iDestruct_select_several_match P Q R :
  □ P -∗ □ Q -∗ □ R -∗ □ R.
Proof.
  iIntros "???".
  (* This demonstrates that the last matching hypothesis is used for all the
     tactics based on [iSelect]. *)
  iDestruct select (□ _)%I as "$".
Qed.

Lemma test_iRevert_select_iClear_select P Q R :
  □ P -∗ □ Q -∗ □ R -∗ □ R.
Proof.
  iIntros "???".
  iClear select (□ P)%I.
  iRevert select _.
  iClear select _.
  iIntros "$".
Qed.

Lemma test_iFrame_select P Q R :
  P -∗ (Q ∗ R) -∗ P ∗ Q ∗ R.
Proof.
  iIntros "??".
  iFrame select (_ ∗ _)%I.
  iFrame select _.
Qed.

End tactic_tests.
