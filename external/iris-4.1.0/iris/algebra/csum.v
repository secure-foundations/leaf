From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Import options.

Local Arguments pcore _ _ !_ /.
Local Arguments cmra_pcore _ !_ /.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments cmra_validN _ _ !_ /.
Local Arguments cmra_valid _  !_ /.

Inductive csum (A B : Type) :=
  | Cinl : A → csum A B
  | Cinr : B → csum A B
  | CsumBot : csum A B.
Global Arguments Cinl {_ _} _.
Global Arguments Cinr {_ _} _.
Global Arguments CsumBot {_ _}.

Global Instance: Params (@Cinl) 2 := {}.
Global Instance: Params (@Cinr) 2 := {}.
Global Instance: Params (@CsumBot) 2 := {}.

Global Instance maybe_Cinl {A B} : Maybe (@Cinl A B) := λ x,
  match x with Cinl a => Some a | _ => None end.
Global Instance maybe_Cinr {A B} : Maybe (@Cinr A B) := λ x,
  match x with Cinr b => Some b | _ => None end.

Section ofe.
Context {A B : ofe}.
Implicit Types a : A.
Implicit Types b : B.

(* Cofe *)
Inductive csum_equiv : Equiv (csum A B) :=
  | Cinl_equiv a a' : a ≡ a' → Cinl a ≡ Cinl a'
  | Cinr_equiv b b' : b ≡ b' → Cinr b ≡ Cinr b'
  | CsumBot_equiv : CsumBot ≡ CsumBot.
Local Existing Instance csum_equiv.
Inductive csum_dist : Dist (csum A B) :=
  | Cinl_dist n a a' : a ≡{n}≡ a' → Cinl a ≡{n}≡ Cinl a'
  | Cinr_dist n b b' : b ≡{n}≡ b' → Cinr b ≡{n}≡ Cinr b'
  | CsumBot_dist n : CsumBot ≡{n}≡ CsumBot.
Local Existing Instance csum_dist.

Global Instance Cinl_ne : NonExpansive (@Cinl A B).
Proof. by constructor. Qed.
Global Instance Cinl_proper : Proper ((≡) ==> (≡)) (@Cinl A B).
Proof. by constructor. Qed.
Global Instance Cinl_inj : Inj (≡) (≡) (@Cinl A B).
Proof. by inversion_clear 1. Qed.
Global Instance Cinl_inj_dist n : Inj (dist n) (dist n) (@Cinl A B).
Proof. by inversion_clear 1. Qed.
Global Instance Cinr_ne : NonExpansive (@Cinr A B).
Proof. by constructor. Qed.
Global Instance Cinr_proper : Proper ((≡) ==> (≡)) (@Cinr A B).
Proof. by constructor. Qed.
Global Instance Cinr_inj : Inj (≡) (≡) (@Cinr A B).
Proof. by inversion_clear 1. Qed.
Global Instance Cinr_inj_dist n : Inj (dist n) (dist n) (@Cinr A B).
Proof. by inversion_clear 1. Qed.

Definition csum_ofe_mixin : OfeMixin (csum A B).
Proof.
  split.
  - intros mx my; split.
    + by destruct 1; constructor; try apply equiv_dist.
    + intros Hxy; oinversion (Hxy 0); subst; constructor; try done;
      apply equiv_dist=> n; by oinversion (Hxy n).
  - intros n; split.
    + by intros [|a|]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; eauto using dist_le with si_solver.
Qed.
Canonical Structure csumO : ofe := Ofe (csum A B) csum_ofe_mixin.

Program Definition csum_chain_l (c : chain csumO) (a : A) : chain A :=
  {| chain_car n := match c n return _ with Cinl a' => a' | _ => a end |}.
Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
Program Definition csum_chain_r (c : chain csumO) (b : B) : chain B :=
  {| chain_car n := match c n return _ with Cinr b' => b' | _ => b end |}.
Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
Definition csum_compl `{!Cofe A, !Cofe B} : Compl csumO := λ c,
  match c 0 with
  | Cinl a => Cinl (compl (csum_chain_l c a))
  | Cinr b => Cinr (compl (csum_chain_r c b))
  | CsumBot => CsumBot
  end.
Global Program Instance csum_cofe `{!Cofe A, !Cofe B} : Cofe csumO :=
  {| compl := csum_compl |}.
Next Obligation.
  intros ?? n c; rewrite /compl /csum_compl.
  oinversion (chain_cauchy c 0 n); first auto with lia; constructor.
  + rewrite (conv_compl n (csum_chain_l c _)) /=. destruct (c n); naive_solver.
  + rewrite (conv_compl n (csum_chain_r c _)) /=. destruct (c n); naive_solver.
Qed.

Global Instance csum_ofe_discrete :
  OfeDiscrete A → OfeDiscrete B → OfeDiscrete csumO.
Proof. by inversion_clear 3; constructor; apply (discrete _). Qed.
Global Instance csum_leibniz :
  LeibnizEquiv A → LeibnizEquiv B → LeibnizEquiv csumO.
Proof. by destruct 3; f_equal; apply leibniz_equiv. Qed.

Global Instance Cinl_discrete a : Discrete a → Discrete (Cinl a).
Proof. by inversion_clear 2; constructor; apply (discrete _). Qed.
Global Instance Cinr_discrete b : Discrete b → Discrete (Cinr b).
Proof. by inversion_clear 2; constructor; apply (discrete _). Qed.

End ofe.

Global Arguments csumO : clear implicits.

(* Functor on COFEs *)
Definition csum_map {A A' B B'} (fA : A → A') (fB : B → B')
                    (x : csum A B) : csum A' B' :=
  match x with
  | Cinl a => Cinl (fA a)
  | Cinr b => Cinr (fB b)
  | CsumBot => CsumBot
  end.
Global Instance: Params (@csum_map) 4 := {}.

Lemma csum_map_id {A B} (x : csum A B) : csum_map id id x = x.
Proof. by destruct x. Qed.
Lemma csum_map_compose {A A' A'' B B' B''} (f : A → A') (f' : A' → A'')
                       (g : B → B') (g' : B' → B'') (x : csum A B) :
  csum_map (f' ∘ f) (g' ∘ g) x = csum_map f' g' (csum_map f g x).
Proof. by destruct x. Qed.
Lemma csum_map_ext {A A' B B' : ofe} (f f' : A → A') (g g' : B → B') x :
  (∀ x, f x ≡ f' x) → (∀ x, g x ≡ g' x) → csum_map f g x ≡ csum_map f' g' x.
Proof. by destruct x; constructor. Qed.
Global Instance csum_map_cmra_ne {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n)
         (@csum_map A A' B B').
Proof. intros f f' Hf g g' Hg []; destruct 1; constructor; by apply Hf || apply Hg. Qed.
Definition csumO_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  csumO A B -n> csumO A' B' :=
  OfeMor (csum_map f g).
Global Instance csumO_map_ne A A' B B' :
  NonExpansive2 (@csumO_map A A' B B').
Proof. by intros n f f' Hf g g' Hg []; constructor. Qed.

Section cmra.
Context {A B : cmra}.
Implicit Types a : A.
Implicit Types b : B.

(* CMRA *)
Local Instance csum_valid_instance : Valid (csum A B) := λ x,
  match x with
  | Cinl a => ✓ a
  | Cinr b => ✓ b
  | CsumBot => False
  end.
Local Instance csum_validN_instance : ValidN (csum A B) := λ n x,
  match x with
  | Cinl a => ✓{n} a
  | Cinr b => ✓{n} b
  | CsumBot => False
  end.
Local Instance csum_pcore_instance : PCore (csum A B) := λ x,
  match x with
  | Cinl a => Cinl <$> pcore a
  | Cinr b => Cinr <$> pcore b
  | CsumBot => Some CsumBot
  end.
Local Instance csum_op_instance : Op (csum A B) := λ x y,
  match x, y with
  | Cinl a, Cinl a' => Cinl (a ⋅ a')
  | Cinr b, Cinr b' => Cinr (b ⋅ b')
  | _, _ => CsumBot
  end.

Lemma Cinl_op a a' : Cinl (a ⋅ a') = Cinl a ⋅ Cinl a'.
Proof. done. Qed.
Lemma Cinr_op b b' : Cinr (b ⋅ b') = Cinr b ⋅ Cinr b'.
Proof. done. Qed.

Lemma Cinl_valid a : ✓ (Cinl a) ↔ ✓ a.
Proof. done. Qed.
Lemma Cinr_valid b : ✓ (Cinr b) ↔ ✓ b.
Proof. done. Qed.

Lemma csum_included x y :
  x ≼ y ↔ y = CsumBot ∨ (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ a ≼ a')
                      ∨ (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ b ≼ b').
Proof.
  split.
  - unfold included. intros [[a'|b'|] Hy]; destruct x as [a|b|];
      inversion_clear Hy; eauto 10.
  - intros [->|[(a&a'&->&->&c&?)|(b&b'&->&->&c&?)]].
    + destruct x; exists CsumBot; constructor.
    + exists (Cinl c); by constructor.
    + exists (Cinr c); by constructor.
Qed.
Lemma Cinl_included a a' : Cinl a ≼ Cinl a' ↔ a ≼ a'.
Proof. rewrite csum_included. naive_solver. Qed.
Lemma Cinr_included b b' : Cinr b ≼ Cinr b' ↔ b ≼ b'.
Proof. rewrite csum_included. naive_solver. Qed.
Lemma CsumBot_included x : x ≼ CsumBot.
Proof. exists CsumBot. by destruct x. Qed.
(** We register a hint for [CsumBot_included] below. *)

Lemma csum_includedN n x y :
  x ≼{n} y ↔ y = CsumBot ∨ (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ a ≼{n} a')
                         ∨ (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ b ≼{n} b').
Proof.
  split.
  - unfold includedN. intros [[a'|b'|] Hy]; destruct x as [a|b|];
      inversion_clear Hy; eauto 10.
  - intros [->|[(a&a'&->&->&c&?)|(b&b'&->&->&c&?)]].
    + destruct x; exists CsumBot; constructor.
    + exists (Cinl c); by constructor.
    + exists (Cinr c); by constructor.
Qed.

Lemma csum_cmra_mixin : CmraMixin (csum A B).
Proof.
  split.
  - intros [] n; destruct 1; constructor; by ofe_subst.
  - intros ???? [n a a' Ha|n b b' Hb|n] [=]; subst; eauto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      destruct (cmra_pcore_ne n a a' ca) as (ca'&->&?); auto.
      exists (Cinl ca'); by repeat constructor.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      destruct (cmra_pcore_ne n b b' cb) as (cb'&->&?); auto.
      exists (Cinr cb'); by repeat constructor.
  - intros ? [a|b|] [a'|b'|] H; inversion_clear H; ofe_subst; done.
  - intros [a|b|]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [a|b|]; simpl; auto using cmra_validN_S.
  - intros [a1|b1|] [a2|b2|] [a3|b3|]; constructor; by rewrite ?assoc.
  - intros [a1|b1|] [a2|b2|]; constructor; by rewrite 1?comm.
  - intros [a|b|] ? [=]; subst; auto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      constructor; eauto using cmra_pcore_l.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      constructor; eauto using cmra_pcore_l.
  - intros [a|b|] ? [=]; subst; auto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      oinversion (cmra_pcore_idemp a ca); repeat constructor; auto.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      oinversion (cmra_pcore_idemp b cb); repeat constructor; auto.
  - intros x y ? [->|[(a&a'&->&->&?)|(b&b'&->&->&?)]]%csum_included [=].
    + exists CsumBot. rewrite csum_included; eauto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      destruct (cmra_pcore_mono a a' ca) as (ca'&->&?); auto.
      exists (Cinl ca'). rewrite csum_included; eauto 10.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      destruct (cmra_pcore_mono b b' cb) as (cb'&->&?); auto.
      exists (Cinr cb'). rewrite csum_included; eauto 10.
  - intros n [a1|b1|] [a2|b2|]; simpl; eauto using cmra_validN_op_l; done.
  - intros n [a|b|] y1 y2 Hx Hx'.
    + destruct y1 as [a1|b1|], y2 as [a2|b2|]; try by exfalso; inversion Hx'.
      destruct (cmra_extend n a a1 a2) as (z1&z2&?&?&?); [done|apply (inj Cinl), Hx'|].
      exists (Cinl z1), (Cinl z2). by repeat constructor.
    + destruct y1 as [a1|b1|], y2 as [a2|b2|]; try by exfalso; inversion Hx'.
      destruct (cmra_extend n b b1 b2) as (z1&z2&?&?&?); [done|apply (inj Cinr), Hx'|].
      exists (Cinr z1), (Cinr z2). by repeat constructor.
    + by exists CsumBot, CsumBot; destruct y1, y2; inversion_clear Hx'.
Qed.
Canonical Structure csumR := Cmra (csum A B) csum_cmra_mixin.

Global Instance csum_cmra_discrete :
  CmraDiscrete A → CmraDiscrete B → CmraDiscrete csumR.
Proof.
  split; first apply _.
  by move=>[a|b|] HH /=; try apply cmra_discrete_valid.
Qed.

Global Instance Cinl_core_id a : CoreId a → CoreId (Cinl a).
Proof. rewrite /CoreId /=. inversion_clear 1; by repeat constructor. Qed.
Global Instance Cinr_core_id b : CoreId b → CoreId (Cinr b).
Proof. rewrite /CoreId /=. inversion_clear 1; by repeat constructor. Qed.

Global Instance Cinl_exclusive a : Exclusive a → Exclusive (Cinl a).
Proof. by move=> H[]? =>[/H||]. Qed.
Global Instance Cinr_exclusive b : Exclusive b → Exclusive (Cinr b).
Proof. by move=> H[]? =>[|/H|]. Qed.

Global Instance Cinl_cancelable a : Cancelable a → Cancelable (Cinl a).
Proof.
  move=> ?? [y|y|] [z|z|] ? EQ //; inversion_clear EQ.
  constructor. by eapply (cancelableN a).
Qed.
Global Instance Cinr_cancelable b : Cancelable b → Cancelable (Cinr b).
Proof.
  move=> ?? [y|y|] [z|z|] ? EQ //; inversion_clear EQ.
  constructor. by eapply (cancelableN b).
Qed.

Global Instance Cinl_id_free a : IdFree a → IdFree (Cinl a).
Proof. intros ? [] ? EQ; inversion_clear EQ. by eapply id_free0_r. Qed.
Global Instance Cinr_id_free b : IdFree b → IdFree (Cinr b).
Proof. intros ? [] ? EQ; inversion_clear EQ. by eapply id_free0_r. Qed.

(** Interaction with [option] *)
Lemma Some_csum_includedN x y n :
  Some x ≼{n} Some y ↔
    y = CsumBot ∨
    (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ Some a ≼{n} Some a') ∨
    (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ Some b ≼{n} Some b').
Proof.
  repeat setoid_rewrite Some_includedN. rewrite csum_includedN. split.
  - intros [Hxy|?]; [inversion Hxy|]; naive_solver.
  - naive_solver by f_equiv.
Qed.
Lemma Some_csum_included x y :
  Some x ≼ Some y ↔
    y = CsumBot ∨
    (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ Some a ≼ Some a') ∨
    (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ Some b ≼ Some b').
Proof.
  repeat setoid_rewrite Some_included. rewrite csum_included. split.
  - intros [Hxy|?]; [inversion Hxy|]; naive_solver.
  - naive_solver by f_equiv.
Qed.

(** Updates *)
Lemma csum_update_l (a1 a2 : A) : a1 ~~> a2 → Cinl a1 ~~> Cinl a2.
Proof.
  intros Ha n [[a|b|]|] ?; simpl in *; auto.
  - by apply (Ha n (Some a)).
  - by apply (Ha n None).
Qed.
Lemma csum_update_r (b1 b2 : B) : b1 ~~> b2 → Cinr b1 ~~> Cinr b2.
Proof.
  intros Hb n [[a|b|]|] ?; simpl in *; auto.
  - by apply (Hb n (Some b)).
  - by apply (Hb n None).
Qed.
Lemma csum_updateP_l (P : A → Prop) (Q : csum A B → Prop) a :
  a ~~>: P → (∀ a', P a' → Q (Cinl a')) → Cinl a ~~>: Q.
Proof.
  intros Hx HP n mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm.
  - destruct (Hx n (Some a')) as (c&?&?); naive_solver.
  - destruct (Hx n None) as (c&?&?); naive_solver eauto using cmra_validN_op_l.
Qed.
Lemma csum_updateP_r (P : B → Prop) (Q : csum A B → Prop) b :
  b ~~>: P → (∀ b', P b' → Q (Cinr b')) → Cinr b  ~~>: Q.
Proof.
  intros Hx HP n mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm.
  - destruct (Hx n (Some b')) as (c&?&?); naive_solver.
  - destruct (Hx n None) as (c&?&?); naive_solver eauto using cmra_validN_op_l.
Qed.
Lemma csum_updateP'_l (P : A → Prop) a :
  a ~~>: P → Cinl a ~~>: λ m', ∃ a', m' = Cinl a' ∧ P a'.
Proof. eauto using csum_updateP_l. Qed.
Lemma csum_updateP'_r (P : B → Prop) b :
  b ~~>: P → Cinr b ~~>: λ m', ∃ b', m' = Cinr b' ∧ P b'.
Proof. eauto using csum_updateP_r. Qed.

Lemma csum_local_update_l (a1 a2 a1' a2' : A) :
  (a1,a2) ~l~> (a1',a2') → (Cinl a1,Cinl a2) ~l~> (Cinl a1',Cinl a2').
Proof.
  intros Hup n mf ? Ha1; simpl in *.
  destruct (Hup n (mf ≫= maybe Cinl)); auto.
  { by destruct mf as [[]|]; inversion_clear Ha1. }
  split; first done. by destruct mf as [[]|]; inversion_clear Ha1; constructor.
Qed.
Lemma csum_local_update_r (b1 b2 b1' b2' : B) :
  (b1,b2) ~l~> (b1',b2') → (Cinr b1,Cinr b2) ~l~> (Cinr b1',Cinr b2').
Proof.
  intros Hup n mf ? Ha1; simpl in *.
  destruct (Hup n (mf ≫= maybe Cinr)); auto.
  { by destruct mf as [[]|]; inversion_clear Ha1. }
  split; first done. by destruct mf as [[]|]; inversion_clear Ha1; constructor.
Qed.
End cmra.

(* We use a [Hint Extern] with [apply:], instead of [Hint Immediate], to invoke
  the new unification algorithm. The old unification algorithm sometimes gets
  confused by going from [ucmra]'s to [cmra]'s and back. *)
Global Hint Extern 0 (_ ≼ CsumBot) => apply: CsumBot_included : core.
Global Arguments csumR : clear implicits.

(* Functor *)
Global Instance csum_map_cmra_morphism {A A' B B' : cmra} (f : A → A') (g : B → B') :
  CmraMorphism f → CmraMorphism g → CmraMorphism (csum_map f g).
Proof.
  split; try apply _.
  - intros n [a|b|]; simpl; auto using cmra_morphism_validN.
  - move=> [a|b|]=>//=; rewrite -cmra_morphism_pcore; by destruct pcore.
  - intros [xa|ya|] [xb|yb|]=>//=; by rewrite cmra_morphism_op.
Qed.

Program Definition csumRF (Fa Fb : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := csumR (rFunctor_car Fa A B) (rFunctor_car Fb A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := csumO_map (rFunctor_map Fa fg) (rFunctor_map Fb fg)
|}.
Next Obligation.
  by intros Fa Fb A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumO_map_ne; try apply rFunctor_map_ne.
Qed.
Next Obligation.
  intros Fa Fb A ? B ? x. rewrite /= -{2}(csum_map_id x).
  apply csum_map_ext=>y; apply rFunctor_map_id.
Qed.
Next Obligation.
  intros Fa Fb A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -csum_map_compose.
  apply csum_map_ext=>y; apply rFunctor_map_compose.
Qed.

Global Instance csumRF_contractive Fa Fb :
  rFunctorContractive Fa → rFunctorContractive Fb →
  rFunctorContractive (csumRF Fa Fb).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  by apply csumO_map_ne; try apply rFunctor_map_contractive.
Qed.
