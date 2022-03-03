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

Require Import free_monoid.

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
    
    Definition update_ex_n {A: cmra} x P := ∀ (n : nat) (mz : option A), ✓{n} (x ⋅? mz) → ∃ y : A, (nPred_holds (P y) n) ∧ ✓{n} (y ⋅? mz).
    
    Lemma bupd_ownM_updatePN {M: ucmra} x (Φ : M → nPred) :
      update_ex_n x Φ → uPred_ownM x ⊢ |==> ∃ y, (uPred_of_nPred (Φ y))  ∧ uPred_ownM y.
    Proof.
      unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??. 
      destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *.
      { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. }
      exists (y ⋅ x3); split; first by rewrite -assoc.
      exists y.
      unfold uPred_and_def. unfold uPred_holds.
      unfold uPred_of_nPred.
      unfold uPred_ownM_def.
      split; trivial.
      unfold includedN. exists x3. trivial.
    Qed.
  
    Lemma cmra_total_updatePN `{CmraTotal A} (x: A) (P : A → nPred) :
      update_ex_n x P ↔ ∀ n z, ✓{n} (x ⋅ z) → ∃ y, nPred_holds (P y) n ∧ ✓{n} (y ⋅ z).
    Proof.
      split=> Hup; [intros n z; apply (Hup n (Some z))|].
      intros n [z|] ?; simpl; [by apply Hup|].
      destruct (Hup n (core x)) as (y&?&?); first by rewrite cmra_core_r.
      eauto using cmra_validN_op_l.
    Qed.
    
  Lemma discrete_fun_insert_updatePN `{EqDecision A} {B : A → ucmra} (x: A) (P : B x → nPred) (Q : discrete_fun B → nPred) (g: discrete_fun B) y1 :
    update_ex_n y1 P →
    (∀ y2 n, nPred_holds (P y2) n → nPred_holds (Q (discrete_fun_insert x y2 g)) n) →
    update_ex_n (discrete_fun_insert x y1 g) Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updatePN.
    intros n gf Hg. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
    { move: (Hg x). by rewrite discrete_fun_lookup_op discrete_fun_lookup_insert. }
    exists (discrete_fun_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite discrete_fun_lookup_op ?discrete_fun_lookup_insert //; [].
    move: (Hg x'). by rewrite discrete_fun_lookup_op !discrete_fun_lookup_insert_ne.
  Qed.
    
    Lemma discrete_fun_singleton_updatePN `{EqDecision A} {B : A → ucmra} (x: A) (P : B x → nPred) (Q : discrete_fun B → nPred) y1 :
      update_ex_n y1 P →
      (∀ y2 n , nPred_holds (P y2) n → nPred_holds (Q (discrete_fun_singleton x y2)) n) →
      update_ex_n (discrete_fun_singleton x y1) Q. 
    Proof. rewrite /discrete_fun_singleton; eauto using discrete_fun_insert_updatePN. Qed. 
    
     Lemma option_updatePN {A: cmra} (P : A → nPred) (Q : option A → nPred) x : 
        update_ex_n x P →
        (∀ y n, nPred_holds (P y) n → nPred_holds (Q (Some y)) n) →
        update_ex_n (Some x) Q.
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
      
      Lemma option_updatePN' {A: cmra} (P : A → nPred) x : 
        update_ex_n x P → update_ex_n (Some x) (from_option P nPred_False).
      Proof. eauto using option_updatePN. Qed. 
    
    Lemma insert_updatePN `{Countable K} {A: cmra} (P : A → nPred) (Q : gmap K A → nPred) m i x :
      update_ex_n x P →
      (∀ y n, nPred_holds (P y) n → nPred_holds (Q (<[i:=y]>m)) n) →
      update_ex_n (<[i:=x]>m) Q.
    Proof.
      intros Hx%option_updatePN' HP; apply cmra_total_updatePN=> n mf Hm.
      destruct (Hx n (Some (mf !! i))) as ([y|]&?&?); try done.
      { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
      exists (<[i:=y]> m); split; first by auto.
      intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
      destruct (decide (i = j)); simplify_map_eq/=; auto.
    Qed.
    
    Lemma singleton_updatePN `{Countable K} {A: cmra} (P : A → nPred) (Q : gmap K A → nPred) i x : 
      update_ex_n x P → (∀ y n, nPred_holds (P y) n → nPred_holds (Q {[ i := y ]}) n) → update_ex_n ({[ i := x ]}) Q.
    Proof. apply insert_updatePN. Qed.
    
    Program Definition nPred_eq_singleton `{Countable K} {A: cmra} (P : A -> nPred) (i: K) (m: gmap K A) : nPred :=
        {| nPred_holds n := ∃ y , m = {[ i := y ]} ∧ nPred_holds (P y) n |}.
    Next Obligation. 
        intros. simpl. simpl in H0. destruct H0. exists x.  intuition.
        apply nPred_mono with (n1 := n1); trivial.
    Qed.
    
    Lemma singleton_updatePN' `{Countable K} {A: cmra} (P : A → nPred) (i: K) x : 
      update_ex_n x P →
      update_ex_n ({[ i := x ]}) (nPred_eq_singleton P i).
    Proof. intro. apply singleton_updatePN with (P0 := P); trivial.
        intros.
        unfold nPred_eq_singleton. unfold nPred_holds.
        exists y. intuition.
    Qed.
    
      Lemma iso_cmra_updatePN {A B : cmra} (f : A → B) (g : B → A)
          (P : B → nPred) (Q : A → nPred) y
      (gf : ∀ x, g (f x) ≡ x)
      (g_op : ∀ y1 y2, g (y1 ⋅ y2) ≡ g y1 ⋅ g y2) 
      (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y) :
        update_ex_n y P → 
        (∀ y' n, nPred_holds (P y') n → nPred_holds (Q (g y')) n) →
        update_ex_n (g y) Q.
      Proof.
        intros Hup Hx n mz Hmz.
        destruct (Hup n (f <$> mz)) as (y'&HPy'&Hy'%g_validN).
        { apply g_validN. destruct mz as [z|]; simpl in *; [|done].
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

      Lemma iso_cmra_updatePN' {A B : cmra} (f : A → B) (g : B → A) (P : B → nPred) y
          (gf : ∀ x, g (f x) ≡ x)
          (g_op : ∀ y1 y2, g (y1 ⋅ y2) ≡ g y1 ⋅ g y2) 
          (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y) :
        update_ex_n y P → 
        update_ex_n (g y) (nPred_eq_iso P g).
      Proof.
        intro.
        apply (iso_cmra_updatePN f g P _ y); trivial.
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
      
        Lemma cmra_updateP_weaken {A: cmra} (P Q : A → nPred) x :
          update_ex_n x P → (∀ y n, nPred_holds (P y) n → nPred_holds (Q y) n) → update_ex_n x Q.
        Proof.
            intros.
            unfold update_ex_n in *.
            intuition.
            have j := H n mz H1.
            destruct j.
            exists x0. intuition.
        Qed.
            
      
       Lemma cmra_transport_updatePN {A B : cmra} (H : A = B) (P : A → nPred) (Q : B → nPred) x : 
          update_ex_n x P → (∀ y n, nPred_holds (P y) n → nPred_holds (Q ((cmra_transport H) y)) n) → update_ex_n ((cmra_transport H) x) Q.
        Proof. destruct H; eauto using cmra_updateP_weaken. Qed.
        
        Program Definition nPred_eq_transport {A B: cmra} (H : A = B) (P : A -> nPred) (y: B) : nPred :=
        {| nPred_holds n := ∃ y' , y = cmra_transport H y' ∧ nPred_holds (P y') n |}.
        Next Obligation. 
            intros. simpl. simpl in H0. destruct H0. exists x. intuition.
            apply nPred_mono with (n1 := n1); trivial.
        Qed.
        
        Lemma cmra_transport_updatePN' {A B : cmra} (H : A = B) (P : A → nPred) x : 
          update_ex_n x P →
          update_ex_n (cmra_transport H x) (nPred_eq_transport H P).
        Proof.
            intro. apply (cmra_transport_updatePN H P _ x); trivial.
            intros. unfold nPred_holds, nPred_eq_transport.
            exists y. split; trivial.
        Qed.
    
    Context `{i : !inG Σ A}.
    
    
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
    
    Lemma own_updatePN P γ (a: A) (uen: update_ex_n a P)
      : own γ a ==∗ ∃ (a': A), (uPred_of_nPred (P a')) ∗ own γ a'.
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
        
        apply (discrete_fun_singleton_updatePN (inG_id i)
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
          }.
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
          }.
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

Context {F : Type -> ucmra}.

Context (user_ext_valid: ∀ T (eq: Equiv T) , F T -> Prop).
Context (user_ext_interp: ∀ T (eq: Equiv T) , F T -> free T).

Print "▶".
Print laterO.

Class myG Σ := MyG { my_tokG :> inG Σ (authUR (F (laterO (iPropO Σ)))) }.

(*
Definition myΣ : gFunctors := #[GFunctor (authUR (F (laterO (iPropO Σ))))].

Global Instance subG_myΣ {Σ} : subG myΣ Σ → myG Σ.
Proof. solve_inG. Qed.
*)

Context `{!myG Σ}.

Definition ext_valid_n : nat -> F (laterO (iPropO Σ)) -> Prop :=
    λ n , user_ext_valid (laterO (iPropO Σ)) (≡{n}≡).

Program Definition ext_valid {M} (x: F (laterO (iPropO Σ))) : uPred M := {|
  uPred_holds n y := ext_valid_n n x ; (* ignore y *)
|}.
Next Obligation. Admitted.

Print uPredO.
Print iPropO.
Print laterO.
Print iPropO.

Print Next.

Definition iprop_of_free : free (laterO (iPropO Σ)) -> iProp Σ. Admitted.

Definition ext_interp : F (laterO (iPropO Σ)) -> iProp Σ :=
    λ f , (iprop_of_free (user_ext_interp (laterO (iPropO Σ)) (≡) f)).

(*
Definition ext_interp : F (laterO (iPropO Σ)) -> iProp Σ :=
    λ f , (▷ later_car (user_ext_interp (laterO (iPropO Σ)) (≡) f)) % I.
    *)


(*
Definition ext_valid_n : nat -> F (iProp Σ) -> Prop :=
    λ n f , user_ext_valid (iProp Σ) (≡) (user_fmap (λ p , ▷^n p) f).
*)

Program Definition eq_nPred `{A: ofe} (x y : A) : nPred :=
    {| nPred_holds n := x ≡{n}≡ y |}.
Next Obligation.  
  intros. apply dist_le with (n := n1); trivial.
Qed.

Program Definition helper_nPred  (x x' z : F (laterO (iPropO Σ))) (t: auth (F (laterO (iPropO Σ)))) : nPred :=
    {| nPred_holds n := ∃ p ,
        t ≡{n}≡ ● (x' ⋅ p) ⋅ ◯ x' /\ x ⋅ p ≡{n}≡ z |}.
Next Obligation.
  intros. simpl. simpl in H.
  destruct H. exists x0.
  intuition.
  - apply dist_le with (n := n1); trivial.
  - apply dist_le with (n := n1); trivial.
Qed.

Lemma is_frag_if_val n (z x : F (laterO (iPropO Σ))) c
    : ✓{n} (● z ⋅ ◯ x ⋅ c) -> ∃ y , c = ◯ y. Admitted.
    
Lemma get_remainder_to_auth2 n (z x : F (laterO (iPropO Σ)))
    : ✓{n} (● z ⋅ ◯ x) → ∃ x1 , z ≡{n}≡ x ⋅ x1. Admitted.
    
Lemma get_remainder_to_auth3 n (z x x0 : F (laterO (iPropO Σ)))
    : ✓{n} (● z ⋅ ◯ x ⋅ ◯ x0) → ∃ x1 , z ≡{n}≡ x ⋅ x0 ⋅ x1. Admitted.

Lemma valid_auth3_frag2 n (x x0 x1 : F (laterO (iPropO Σ)))
    (isv: ✓{n} (x ⋅ x0 ⋅ x1))
    : ✓{n} (● (x ⋅ x0 ⋅ x1) ⋅ ◯ x ⋅ ◯ x0). Admitted.
    
Lemma valid_auth2_frag1 n (x x0 : F (laterO (iPropO Σ)))
    (isv: ✓{n} (x ⋅ x0))
    : ✓{n} (● (x ⋅ x0) ⋅ ◯ x). Admitted.
    
Lemma valid_of_valid_auth_dot_stuff n (x : F (laterO (iPropO Σ))) stuff1
    : ✓{n} (● x ⋅ stuff1) -> ✓{n}(x). Admitted.
    
Lemma valid_of_valid_auth_dot_stuff2 n (x : F (laterO (iPropO Σ))) stuff1 stuff2
    : ✓{n} (● x ⋅ stuff1 ⋅ stuff2) -> ✓{n}(x). Admitted.

Lemma update_ex_n_auth_frag (x x' z : F (laterO (iPropO Σ)))
  (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y))
  : update_ex_n (● z ⋅ ◯ x) (helper_nPred x x' z).
Proof.
  unfold update_ex_n.
  intros.
  destruct mz.
  - unfold "⋅?" in *.
      have j := is_frag_if_val _ _ _ _ H. destruct j. subst c.
      have r := get_remainder_to_auth3 _ _ _ _ H. destruct r.
      setoid_rewrite H0 in H.
      exists (● (x' ⋅ x0 ⋅ x1) ⋅ ◯ x').
      unfold nPred_holds, helper_nPred.
      split.
      {
        exists (x0 ⋅ x1). split; trivial.
        - rewrite (assoc op). trivial.
        - rewrite (assoc op). trivial.
      }
      { 
        apply valid_auth3_frag2.
        rewrite <- (assoc op).
        apply cond.
        rewrite (assoc op).
        apply (valid_of_valid_auth_dot_stuff2 _ _ _ _ H).
      }
  - unfold "⋅?" in *.
      have r := get_remainder_to_auth2 _ _ _ H. destruct r.
      setoid_rewrite H0 in H. rename x0 into x1.
      exists (● (x' ⋅ x1) ⋅ ◯ x').
      unfold nPred_holds, helper_nPred.
      split.
      {
        exists x1. split; trivial.
      }
      { 
        apply valid_auth2_frag1.
        apply cond.
        apply (valid_of_valid_auth_dot_stuff _ _ _ H).
      }
Qed.

Definition nondet_auth_update_helper (𝛾: gname) (x x' z : F (laterO (iPropO Σ)))
  (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y)) :
    own 𝛾 (● z ⋅ ◯ x) ==∗
    ∃ t , uPred_of_nPred (helper_nPred x x' z t) ∗ own 𝛾 t.
Proof.
  apply own_updatePN.
  apply update_ex_n_auth_frag. trivial.
Qed.

Definition helper_nPred_entail (x x' z : F (laterO (iPropO Σ))) (t: auth (F (laterO (iPropO Σ))))
    : (uPred_of_nPred (helper_nPred x x' z t) : iProp Σ)
      ⊢ (∃ p , t ≡ ● (x' ⋅ p) ⋅ ◯ x' ∗ x ⋅ p ≡ z) % I.
Proof.
  split. intros.
  unfold uPred_holds, uPred_of_nPred in H0.
  unfold nPred_holds, helper_nPred in H0.
  uPred.unseal.
  unfold uPred_holds, uPred_exist_def.
  destruct H0. destruct H0.
  exists x1.
  unfold uPred_holds, uPred_sep_def.
  exists ε, x0.
  split.
  { rewrite left_id. reflexivity. }
  split.
  { 
    unfold uPred_holds, uPred_internal_eq_def. trivial.
  }
  { 
    unfold uPred_holds, uPred_internal_eq_def. trivial.
  }
Qed.


Definition nondet_auth_update (𝛾: gname) (x x' z : F (laterO (iPropO Σ)))
  (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y)) :
    own 𝛾 (● z ⋅ ◯ x) ==∗
    ∃ p , own 𝛾 (● (x' ⋅ p) ⋅ ◯ x') ∗ (z ≡ x ⋅ p).
Proof.
  iIntros "O".
  iMod (nondet_auth_update_helper 𝛾 x x' with "O") as (t) "[un O]".
    { trivial. }
  iDestruct (helper_nPred_entail with "un") as (p) "[t_eq z_eq]".
  iModIntro.
  iExists p.
  iFrame.
  iRewrite "z_eq".
  iRewrite "t_eq" in "O".
  iFrame.
  done.
Qed.

Definition bank (𝛾: gname) : iProp Σ :=
    ∃ (x: F (laterO (iPropO Σ))) ,
        own 𝛾 (● x)
          ∗ ext_valid x
          ∗ ext_interp x.
          
Definition ext (𝛾: gname) (x: F (laterO (iPropO Σ))) : iProp Σ := own 𝛾 (◯ x).

Instance ext_valid_proper (n: nat) :
    Proper ((≡{n}≡) ==> iff) (ext_valid_n n). Admitted.

  
Instance non_expansive_ext_valid (M: ucmra) : NonExpansive (@ext_valid M).
Proof.
  intros n P1 P2 HP.
  split.
  intros n' x le v.
  unfold ext_valid, uPred_holds.
  have HP' := dist_le _ _ _ _ HP le.
  apply ext_valid_proper. trivial.
Qed.

Definition valid_exchange `{eq: Equiv T} (x x' : F T) (p q : free T) :=
    ∀ y , user_ext_valid T eq (x ⋅ y) → user_ext_valid T eq (x' ⋅ y)
            /\ (user_ext_interp T eq (x ⋅ y)) ⋅ p ≡ (user_ext_interp T eq (x' ⋅ y)) ⋅ q.

Lemma update_cond_from_valid_exchange
    (x x' : F (laterO (iPropO Σ))) (p q : free (laterO (iPropO Σ)))
    (ve: valid_exchange x x' p q)
    : ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y).
Proof.
  intros. unfold valid_exchange in ve.
  have ve' := ve y.
  unfold validN in H.
  unfold cmra_validN in H.
  
Lemma simple_update_helper (𝛾: gname) (x x' z : F (laterO (iPropO Σ)))
      (p q : free (laterO (iPropO Σ)))
  (ve: valid_exchange (laterO (iPropO Σ)) (≡) x x' p q
  (* (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y)) : *)
  (*
  (cond: ∀ y n , ext_valid_n _ n (x ⋅ y) → ext_valid_n _ n (x' ⋅ y)
      uPred_is_valid (x' ⋅ y)
      *)
   : ext_valid z
      ∗ iprop_of_free p
      ∗ ext_interp z
      ∗ own 𝛾 (● z)
      ∗ own 𝛾 (◯ x)
    ==∗
     ∃ z' , ext_valid z'
      ∗ iprop_of_free q
      ∗ ext_interp z'
      ∗ own 𝛾 (● z')
      ∗ own 𝛾 (◯ x').
Proof. 
    iIntros "[valid_z [P [protP af]]]".
    rewrite <- own_op.
    iMod (nondet_auth_update 𝛾 x x' z with "af") as (p) "[af equ]".
    iRewrite "equ" in "valid_z".
    Print internal_eq_rewrite.
      
      
Lemma simple_update (𝛾: gname) (x y: F (laterO (iPropO Σ))) (P Q: iProp Σ)
    : bank 𝛾 ∗ ext 𝛾 x ∗ P ==∗ bank 𝛾 ∗ ext 𝛾 y ∗ Q.
Proof. 
  iIntros "[R [E P]]".
  unfold bank, ext.
  iDestruct "R" as (z S) "[O V]".
  iDestruct (own_valid_2 with "O E") as "K".
  
  
  Unset Printing Notations.
  Set Printing Implicit.
  
  iDestruct (own_valid_2 with "O E") as "valid".
  Print uPred_cmra_valid.
  Print iProp.
  Print iResUR.
  Unset Printing Notations.
  iDestruct (cmra_valid_op_l with "valid") as "valid".
  Print ValidN.
  iApply cmra_valid_op_l
  Print uPred_cmra_valid_def.
  Print uPred_cmra_valid_aux.
  unfold uPred_cmra_valid_aux.
  Set Printing Implicit.
  Print auth_both_valid.
  Print own_valid.
  Print cmra.
  Print CmraMixin.
  Print ucmra.
  unfold .
  
  Print uPred_cmra_valid.
  Print auth_both_valid.



(*
Context {A : ofe}.

Context {P: Type}.
Context `{Dist P}.
Context `{Equiv P}.

Context `{Op P}.
Context `{Valid P}.
Context `{ValidN P}.
Context (p_unit: P).

Instance p_pcore
      : PCore P := λ x , Some p_unit.
      
Definition protocol_cmra_mixin : CmraMixin P.
Proof. split.
 *) 
