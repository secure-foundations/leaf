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

Import uPred.

Section ownership_stuff.
    Record nPred : Type := UPred {
      nPred_holds : nat → Prop;

      nPred_mono n1 n2 :
        nPred_holds n1 → n2 ≤ n1 → nPred_holds n2
    }.
    
    Program Definition uPred_of_nPred {M : ucmra} np : uPred M :=
        {| uPred_holds n x := nPred_holds np n |}.
    Next Obligation. 
        intros. apply nPred_mono with (n1 := n1); trivial.
    Qed.
    
    Definition update_ex_n {A: cmra} x R P := ∀ (n : nat) (mz : option A),
        nPred_holds R n /\ ✓{n} (x ⋅? mz) →
        ∃ y : A, (nPred_holds (P y) n) ∧ ✓{n} (y ⋅? mz).
    
    Lemma bupd_ownM_updatePN {M: ucmra} x (R : nPred) (P : M → nPred) :
      update_ex_n x R P →
        uPred_of_nPred R ∗ uPred_ownM x ⊢ |==> ∃ y, (uPred_of_nPred (P y))  ∧ uPred_ownM y.
    Proof.
      unseal=> Hup; split=> n x2 val_x2 [x3 [x4 [Hx [Hy [x5 Hz]] k]]] yf k_le_n val_x2_yf. 
      destruct (Hup k (Some (x5 ⋅ yf))) as (y&?&?); simpl in *.
      { 
        split.
        {
          assert (nPred_holds R n) by auto.
          apply nPred_mono with (n1 := n); trivial.
        }
        { rewrite /= assoc -(dist_le _ _ _ _ Hz); auto.
          assert (✓{k} (x3 ⋅ x4 ⋅ yf)).
          { rewrite -(dist_le _ _ _ _ Hx); auto. }
          apply cmra_validN_op_r with (x0 := x3).
          rewrite /= assoc. trivial.
        }
      } 
      exists (y ⋅ x5); split; first by rewrite -assoc.
      exists y.
      unfold uPred_and_def. unfold uPred_holds.
      unfold uPred_of_nPred.
      unfold uPred_ownM_def.
      split; trivial.
      unfold includedN. exists x5. trivial.
    Qed.
  
    Lemma cmra_total_updatePN `{CmraTotal A} (x: A) (R : nPred) (P : A → nPred) :
      update_ex_n x R P ↔
        ∀ n z, nPred_holds R n ∧ ✓{n} (x ⋅ z)
        → ∃ y, nPred_holds (P y) n ∧ ✓{n} (y ⋅ z).
    Proof.
      split=> Hup; [intros n z; apply (Hup n (Some z))|].
      intros n [z|] ?; simpl; [by apply Hup|].
      destruct (Hup n (core x)) as (y&?&?); first by rewrite cmra_core_r.
      eauto using cmra_validN_op_l.
    Qed.
    
  Lemma discrete_fun_insert_updatePN `{EqDecision A} {B : A → ucmra}
      (x: A) (R : nPred) (P : B x → nPred) (Q : discrete_fun B → nPred) (g: discrete_fun B) y1 :
    update_ex_n y1 R P →
    (∀ y2 n, nPred_holds (P y2) n → nPred_holds (Q (discrete_fun_insert x y2 g)) n) →
    update_ex_n (discrete_fun_insert x y1 g) R Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updatePN.
    intros n gf [r Hg]. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
    { move: (Hg x). by rewrite discrete_fun_lookup_op discrete_fun_lookup_insert. }
    exists (discrete_fun_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite discrete_fun_lookup_op ?discrete_fun_lookup_insert //; [].
    move: (Hg x'). by rewrite discrete_fun_lookup_op !discrete_fun_lookup_insert_ne.
  Qed.
    
    Lemma discrete_fun_singleton_updatePN `{EqDecision A} {B : A → ucmra} (x: A)
        (R: nPred) (P : B x → nPred) (Q : discrete_fun B → nPred) y1 :
      update_ex_n y1 R P →
      (∀ y2 n , nPred_holds (P y2) n → nPred_holds (Q (discrete_fun_singleton x y2)) n) →
      update_ex_n (discrete_fun_singleton x y1) R Q. 
    Proof. rewrite /discrete_fun_singleton; eauto using discrete_fun_insert_updatePN. Qed. 
    
     Lemma option_updatePN {A: cmra} (R: nPred) (P : A → nPred) (Q : option A → nPred) x : 
        update_ex_n x R P →
        (∀ y n, nPred_holds (P y) n → nPred_holds (Q (Some y)) n) →
        update_ex_n (Some x) R Q.
      Proof.
        intros Hx Hy; apply cmra_total_updatePN=> n [y|] ?.
        { destruct (Hx n (Some y)) as (y'&?&?); auto. exists (Some y'); auto. }
        destruct (Hx n None) as (y'&?&?); rewrite ?cmra_core_r; auto.
        by exists (Some y'); auto.
      Qed.
       
    Program Definition nPred_False : nPred :=
        {| nPred_holds n := False |}.
    Next Obligation. 
        intros. trivial.
    Qed.
      
      Lemma option_updatePN' {A: cmra} (R: nPred) (P : A → nPred) x : 
        update_ex_n x R P → update_ex_n (Some x) R (from_option P nPred_False).
      Proof. eauto using option_updatePN. Qed. 
    
    Lemma insert_updatePN `{Countable K} {A: cmra}
        (R: nPred) (P : A → nPred) (Q : gmap K A → nPred) m i x :
      update_ex_n x R P →
      (∀ y n, nPred_holds (P y) n → nPred_holds (Q (<[i:=y]>m)) n) →
      update_ex_n (<[i:=x]>m) R Q.
    Proof.
      intros Hx%option_updatePN' HP; apply cmra_total_updatePN=> n mf [r Hm].
      destruct (Hx n (Some (mf !! i))) as ([y|]&?&?); try done.
      { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
      exists (<[i:=y]> m); split; first by auto.
      intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
      destruct (decide (i = j)); simplify_map_eq/=; auto.
    Qed.
    
    Lemma singleton_updatePN `{Countable K} {A: cmra} (R: nPred) (P : A → nPred) (Q : gmap K A → nPred) i x : 
      update_ex_n x R P → (∀ y n, nPred_holds (P y) n → nPred_holds (Q {[ i := y ]}) n) → update_ex_n ({[ i := x ]}) R Q.
    Proof. apply insert_updatePN. Qed.
    
    Program Definition nPred_eq_singleton `{Countable K} {A: cmra} (P : A -> nPred) (i: K) (m: gmap K A) : nPred :=
        {| nPred_holds n := ∃ y , m = {[ i := y ]} ∧ nPred_holds (P y) n |}.
    Next Obligation. 
        intros. simpl. simpl in H0. destruct H0. exists x.  intuition.
        apply nPred_mono with (n1 := n1); trivial.
    Qed.
    
    Lemma singleton_updatePN' `{Countable K} {A: cmra} (R: nPred) (P : A → nPred) (i: K) x : 
      update_ex_n x R P →
      update_ex_n ({[ i := x ]}) R (nPred_eq_singleton P i).
    Proof. intro. apply singleton_updatePN with (P0 := P); trivial.
        intros.
        unfold nPred_eq_singleton. unfold nPred_holds.
        exists y. intuition.
    Qed.
    
      Lemma iso_cmra_updatePN {A B : cmra} (f : A → B) (g : B → A)
          (R: nPred) (P : B → nPred) (Q : A → nPred) y
      (gf : ∀ x, g (f x) ≡ x)
      (g_op : ∀ y1 y2, g (y1 ⋅ y2) ≡ g y1 ⋅ g y2) 
      (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y) :
        update_ex_n y R P → 
        (∀ y' n, nPred_holds (P y') n → nPred_holds (Q (g y')) n) →
        update_ex_n (g y) R Q.
      Proof.
        intros Hup Hx n mz [r Hmz].
        destruct (Hup n (f <$> mz)) as (y'&HPy'&Hy'%g_validN).
        { split; trivial.
          apply g_validN. destruct mz as [z|]; simpl in *; [|done].
          by rewrite g_op gf. }
        exists (g y'); split; [by eauto|].
        destruct mz as [z|]; simpl in *; [|done].
        revert Hy'. by rewrite g_op gf. 
      Qed.
       
    Program Definition nPred_eq_iso {A B: cmra} (P : B -> nPred) (g: B → A) (x: A) : nPred :=
        {| nPred_holds n := ∃ y , x = g y ∧ nPred_holds (P y) n |}.
    Next Obligation. 
        intros. simpl. simpl in H. destruct H. exists x0. intuition.
        apply nPred_mono with (n1 := n1); trivial.
    Qed.

      Lemma iso_cmra_updatePN' {A B : cmra} (f : A → B) (g : B → A) (R: nPred) (P : B → nPred) y
          (gf : ∀ x, g (f x) ≡ x)
          (g_op : ∀ y1 y2, g (y1 ⋅ y2) ≡ g y1 ⋅ g y2) 
          (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y) :
        update_ex_n y R P → 
        update_ex_n (g y) R (nPred_eq_iso P g).
      Proof.
        intro.
        apply (iso_cmra_updatePN f g R P _ y); trivial.
        unfold nPred_holds, nPred_eq_iso. intros. exists y'. intuition.
      Qed.
      
      (*
      Lemma cmra_updatePN_id {A: cmra} (P : A → nPred) x : (∀ n , nPred_holds (P x) n) → update_ex_n x P.
      Proof. intros ? n mz ?; eauto. Qed. 
      *)
      
      (*
      Lemma cmra_updateP_compose (P Q : A → nPred) x :
        update_ex_n x P → (∀ y, P y → y ~~>: Q) → x ~~>: Q. 
      Proof. intros Hx Hy n mz ?. destruct (Hx n mz) as (y&?&?); naive_solver. Qed. 
      *)
      
        Lemma cmra_updateP_weaken {A: cmra} (R: nPred) (P Q : A → nPred) x :
          update_ex_n x R P → (∀ y n, nPred_holds (P y) n → nPred_holds (Q y) n) → update_ex_n x R Q.
        Proof.
            intros.
            unfold update_ex_n in *.
            intuition.
            have j := H n mz (conj H2 H3).
            destruct j.
            exists x0. intuition.
        Qed.
            
      
       Lemma cmra_transport_updatePN {A B : cmra} (H : A = B) (R: nPred) (P : A → nPred) (Q : B → nPred) x : 
          update_ex_n x R P → (∀ y n, nPred_holds (P y) n → nPred_holds (Q ((cmra_transport H) y)) n) → update_ex_n ((cmra_transport H) x) R Q.
        Proof. destruct H; eauto using cmra_updateP_weaken. Qed.
        
        Program Definition nPred_eq_transport {A B: cmra} (H : A = B) (P : A -> nPred) (y: B) : nPred :=
        {| nPred_holds n := ∃ y' , y = cmra_transport H y' ∧ nPred_holds (P y') n |}.
        Next Obligation. 
            intros. simpl. simpl in H0. destruct H0. exists x. intuition.
            apply nPred_mono with (n1 := n1); trivial.
        Qed.
        
        Lemma cmra_transport_updatePN' {A B : cmra} (H : A = B) (R: nPred) (P : A → nPred) x : 
          update_ex_n x R P →
          update_ex_n (cmra_transport H x) R (nPred_eq_transport H P).
        Proof.
            intro. apply (cmra_transport_updatePN H R P _ x); trivial.
            intros. unfold nPred_holds, nPred_eq_transport.
            exists y. split; trivial.
        Qed.
    
    Context `{i : !inG Σ A}.
    
    
    (*
(** ** Frame preserving updates *)
Lemma own_updateP P γ (a: A) : a ~~>: P → own γ a ==∗ ∃ a', ⌜P a'⌝ ∗ own γ a'.
Proof.
  intros Hupd. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m,
    ⌜ ∃ a', m = iRes_singleton γ a' ∧ P a' ⌝ ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updateP, (discrete_fun_singleton_updateP _ (λ m, ∃ x,
      m = {[ γ := x ]} ∧ ∃ x',
      x = inG_unfold x' ∧ ∃ a',
      x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver].
    apply singleton_updateP', (iso_cmra_updateP' inG_fold).
    { apply inG_unfold_fold. }
    { apply (cmra_morphism_op _). }
    { apply inG_unfold_validN. }
    by apply cmra_transport_updateP'.
  - apply exist_elim=> m; apply pure_elim_l=> -[a' [-> HP]].
    rewrite -(exist_intro a'). rewrite -persistent_and_sep.
    by apply and_intro; [apply pure_intro|].
Qed.
*)

Print cmra_transport_updateP'.
Print iso_cmra_updateP'.
Print singleton_updateP'.
Print discrete_fun_singleton.
Print discrete_fun_singleton_updateP.

Program Definition updated_nPred P (γ: gname) m : nPred :=
    {| nPred_holds n :=
        ∃ (a': A) , m = iRes_singleton γ a' ∧ nPred_holds (P a') n
    |} .
Next Obligation.  
    intros. simpl. simpl in H. destruct H. destruct H. subst.
    exists x. intuition. apply nPred_mono with (n1 := n1); trivial.
Qed.

Lemma own_updatePN R P γ (a: A) (uen: update_ex_n a R P)
  : uPred_of_nPred R ∗ own γ a ==∗ ∃ (a': A), (uPred_of_nPred (P a')) ∗ own γ a'.
Proof. 
  rewrite !own_eq.
  rewrite -(bupd_mono (∃ m,
    uPred_of_nPred (updated_nPred P γ  m) ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updatePN.
        Print iResUR.
        Print gmapUR.
  
    (*apply (discrete_fun_singleton_updatePN _
        (nPred_eq_singleton _ _)).*)
    
    Print iResUR.
    unfold iRes_singleton.
    
    apply (discrete_fun_singleton_updatePN (inG_id i) R
      (nPred_eq_singleton (
          nPred_eq_iso (
              nPred_eq_transport inG_prf P
          ) inG_unfold 
      ) γ )).
      {
         apply singleton_updatePN', (iso_cmra_updatePN' inG_fold).
         { apply inG_unfold_fold. }
         { apply (cmra_morphism_op _). }
         { apply inG_unfold_validN. }
         apply cmra_transport_updatePN'.
         trivial.
      }
      {
        intros.
        unfold updated_nPred, nPred_holds.
        unfold nPred_eq_singleton, nPred_eq_iso, nPred_eq_transport, nPred_holds in H.
        destruct H. destruct H.
        destruct H0. destruct H0.
        destruct H1. destruct H1.
        subst.
        unfold iRes_singleton.
        exists x1.
        intuition.
      }
  - apply exist_elim=> m.
    split. intro. unfold update_ex_n in uen. intros.
    generalize H0. clear H0.
    uPred.unseal.
    unfold uPred_holds, uPred_exist_def.
    unfold uPred_holds, uPred_sep_def.
    unfold uPred_holds, uPred_of_nPred.
    unfold uPred_holds, uPred_and_def.
    unfold nPred_holds, updated_nPred.
    unfold uPred_holds.
    unfold own_def.
    
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    exists x0.
    exists ε.
    exists x.
    split.
    { rewrite left_id. reflexivity. }
    split.
    {
      trivial.
    }
    subst m. rewrite uPred_ownM_eq. trivial.
Qed.

End ownership_stuff.
