From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Unset Mangle Names.

Section basic_tests.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.

  Lemma test_iIntros_tforall {TT : tele} (Φ : TT → PROP) :
    ⊢ ∀.. x, Φ x -∗ Φ x.
  Proof. iIntros (x) "H". done. Qed.
  Lemma test_iPoseProof_tforall {TT : tele} P (Φ : TT → PROP) :
    (∀.. x, P ⊢ Φ x) → P -∗ ∀.. x, Φ x.
  Proof.
    iIntros (H1) "H2"; iIntros (x).
    iPoseProof (H1) as "H1". by iApply "H1".
  Qed.
  Lemma test_iApply_tforall {TT : tele} P (Φ : TT → PROP) :
    (∀.. x, P -∗ Φ x) -∗ P -∗ ∀.. x, Φ x.
  Proof. iIntros "H1 H2" (x). by iApply "H1". Qed.
  Lemma test_iAssumption_tforall {TT : tele} (Φ : TT → PROP) :
    (∀.. x, Φ x) -∗ ∀.. x, Φ x.
  Proof. iIntros "H" (x). iAssumption. Qed.
  Lemma test_exist_texist_auto_name {TT : tele} (Φ : TT → PROP) :
    (∃.. y, Φ y) -∗ ∃.. x, Φ x.
  Proof. iDestruct 1 as (?) "H". by iExists y. Qed.
  Lemma test_pure_texist {TT : tele} (φ : TT → Prop) :
    (∃.. x, ⌜ φ x ⌝) -∗ ∃.. x, ⌜ φ x ⌝ : PROP.
  Proof. iIntros (H) "!%". done. Qed.
  Lemma test_pure_tforall `{!BiPureForall PROP} {TT : tele} (φ : TT → Prop) :
    (∀.. x, ⌜ φ x ⌝) -∗ ∀.. x, ⌜ φ x ⌝ : PROP.
  Proof. iIntros (H) "!%". done. Qed.
  Lemma test_pure_tforall_persistent {TT : tele} (Φ : TT → PROP) :
    (∀.. x, <pers> (Φ x)) -∗ <pers> ∀.. x, Φ x.
  Proof. iIntros "#H !>" (x). done. Qed.
  Lemma test_pure_texists_intuitionistic {TT : tele} (Φ : TT → PROP) :
    (∃.. x, □ (Φ x)) -∗ □ ∃.. x, Φ x.
  Proof. iDestruct 1 as (x) "#H". iExists (x). done. Qed.
  Lemma test_iMod_tforall {TT : tele} P (Φ : TT → PROP) :
    ◇ P -∗ (∀.. x, Φ x) -∗ ∀.. x, ◇ (P ∗ Φ x).
  Proof. iIntros ">H1 H2" (x) "!> {$H1}". done. Qed.
  Lemma test_timeless_tforall {TT : tele} (φ : TT → Prop) :
    ▷ (∀.. x, ⌜ φ x ⌝) -∗ ◇ ∀.. x, ⌜ φ x ⌝ : PROP.
  Proof. iIntros ">H1 !>". done. Qed.
  Lemma test_timeless_texist {TT : tele} (φ : TT → Prop) :
    ▷ (∃.. x, ⌜ φ x ⌝) -∗ ◇ ∃.. x, ⌜ φ x ⌝ : PROP.
  Proof. iIntros ">H1 !>". done. Qed.
  Lemma test_add_model_texist `{!BiBUpd PROP} {TT : tele} P Q (Φ : TT → PROP) :
    (|==> P) -∗ (P -∗ Q) -∗ ∀.. x, |==> Q ∗ (Φ x -∗ Φ x).
  Proof. iIntros "H1 H2". iDestruct ("H2" with "[> $H1]") as "$". auto. Qed.
  Lemma test_iFrame_tforall {TT : tele} P (Φ : TT → PROP) :
    P -∗ ∀.. x, P ∗ (Φ x -∗ Φ x).
  Proof. iIntros "$". auto. Qed.
  Lemma test_iFrame_texist {TT : tele} P (Φ : TT → PROP) :
    P -∗ (∃.. x, Φ x) -∗ ∃.. x, P ∗ Φ x.
  Proof. iIntros "$". auto. Qed.
End basic_tests.

Section accessor.
(* Just playing around a bit with a telescope version
   of accessors with just one binder list. *)
Definition accessor `{!BiFUpd PROP} {X : tele} (E1 E2 : coPset)
           (α β γ : X → PROP) : PROP :=
  (|={E1,E2}=> ∃.. x, α x ∗ (β x -∗ |={E2,E1}=> (γ x)))%I.

Notation "'ACC' @ E1 , E2 {{ ∃ x1 .. xn , α | β | γ } }" :=
  (accessor (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            E1 E2
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..)
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => β%I) ..)
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => γ%I) ..))
  (at level 20, α, β, γ at level 200, x1 binder, xn binder, only parsing).

(* Working with abstract telescopes. *)
Section tests.
Context `{!BiFUpd PROP} {X : tele}.
Implicit Types α β γ : X → PROP.

Lemma acc_mono E1 E2 α β γ1 γ2 :
  (∀.. x, γ1 x -∗ γ2 x) -∗
  accessor E1 E2 α β γ1 -∗ accessor E1 E2 α β γ2.
Proof.
  iIntros "Hγ12 >Hacc". iDestruct "Hacc" as (x') "[Hα Hclose]". Show.
  iModIntro. iExists x'. iFrame. iIntros "Hβ".
  iMod ("Hclose" with "Hβ") as "Hγ". iApply "Hγ12". auto.
Qed.

Lemma acc_mono_disj E1 E2 α β γ1 γ2 :
  accessor E1 E2 α β γ1 -∗ accessor E1 E2 α β (λ.. x, γ1 x ∨ γ2 x).
Proof.
  Show.
  iApply acc_mono. iIntros (x) "Hγ1". Show.
  rewrite ->tele_app_bind. Show.
  iLeft. done.
Qed.
End tests.

Section printing_tests.
Context `{!BiFUpd PROP}.

(* Working with concrete telescopes: Testing the reduction into normal quantifiers. *)
Lemma acc_elim_test_1 E1 E2 :
  ACC @ E1, E2 {{ ∃ a b : nat, <affine> ⌜a = b⌝ | True | <affine> ⌜a ≠ b⌝ }}
    ⊢@{PROP} |={E1}=> False.
Proof.
  iIntros ">H". Show.
  iDestruct "H" as (a b) "[% Hclose]". iMod ("Hclose" with "[//]") as "%".
  done.
Qed.
End printing_tests.
End accessor.

(* Robbert's tests *)
Section telescopes_and_tactics.

Definition test1 {PROP : bi} {X : tele} (α : X → PROP) : PROP :=
  (∃.. x, α x)%I.

Notation "'TEST1' {{ ∃ x1 .. xn , α } }" :=
  (test1 (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..))
  (at level 20, α at level 200, x1 binder, xn binder, only parsing).

Definition test2 {PROP : bi} {X : tele} (α : X → PROP) : PROP :=
  (▷ ∃.. x, α x)%I.

Notation "'TEST2' {{ ∃ x1 .. xn , α } }" :=
  (test2 (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..))
  (at level 20, α at level 200, x1 binder, xn binder, only parsing).

Definition test3 {PROP : bi} {X : tele} (α : X → PROP) : PROP :=
  (◇ ∃.. x, α x)%I.

Notation "'TEST3' {{ ∃ x1 .. xn , α } }" :=
  (test3 (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..))
  (at level 20, α at level 200, x1 binder, xn binder, only parsing).

Check "test1_test".
Lemma test1_test {PROP : bi}  :
  TEST1 {{ ∃ a b : nat, <affine> ⌜a = b⌝ }} ⊢@{PROP} ▷ False.
Proof.
  iIntros "H". iDestruct "H" as (x) "H". Show.
Restart.
  iIntros "H". unfold test1. iDestruct "H" as (x) "H". Show.
Abort.

Check "test2_test".
Lemma test2_test {PROP : bi}  :
  TEST2 {{ ∃ a b : nat, <affine> ⌜a = b⌝ }} ⊢@{PROP} ▷ False.
Proof.
  iIntros "H". iModIntro. Show.
  iDestruct "H" as (x) "H". Show.
Restart.
  iIntros "H". iDestruct "H" as (x) "H". Show.
Abort.

Check "test3_test".
Lemma test3_test {PROP : bi}  :
  TEST3 {{ ∃ a b : nat, <affine> ⌜a = b⌝ }} ⊢@{PROP} ▷ False.
Proof.
  iIntros "H". iMod "H".
  iDestruct "H" as (x) "H".
  Show.
Restart.
  iIntros "H". iDestruct "H" as (x) "H". Show.
Abort.

End telescopes_and_tactics.
