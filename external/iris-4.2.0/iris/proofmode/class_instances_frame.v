From iris.bi Require Import telescopes.
From iris.proofmode Require Import classes classes_make.
From iris.prelude Require Import options.
Import bi.

(** This file defines the instances that make up the framing machinery. *)

Section class_instances_frame.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(** When framing [R] against itself, we leave [True] if possible (via
[frame_here_absorbing] or [frame_affinely_here_absorbing]) since it is a weaker
goal. Otherwise we leave [emp] via [frame_here].
Only if all those options fail, we start decomposing [R], via instances like
[frame_exist]. To ensure that, all other instances must have cost > 1. *)
Global Instance frame_here_absorbing p R :
  QuickAbsorbing R → Frame p R R True | 0.
Proof.
  rewrite /QuickAbsorbing /Frame. intros.
  by rewrite intuitionistically_if_elim sep_elim_l.
Qed.
Global Instance frame_here p R : Frame p R R emp | 1.
Proof. intros. by rewrite /Frame intuitionistically_if_elim sep_elim_l. Qed.
Global Instance frame_affinely_here_absorbing p R :
  QuickAbsorbing R → Frame p (<affine> R) R True | 0.
Proof.
  rewrite /QuickAbsorbing /Frame. intros.
  rewrite intuitionistically_if_elim affinely_elim. apply sep_elim_l, _.
Qed.
Global Instance frame_affinely_here p R : Frame p (<affine> R) R emp | 1.
Proof.
  intros. rewrite /Frame intuitionistically_if_elim affinely_elim.
  apply sep_elim_l, _.
Qed.

Global Instance frame_here_pure_persistent a φ Q :
  FromPure a Q φ → Frame true ⌜φ⌝ Q emp | 2.
Proof.
  rewrite /FromPure /Frame /= => <-. rewrite right_id.
  by rewrite -affinely_affinely_if intuitionistically_affinely.
Qed.
Global Instance frame_here_pure a φ Q :
  FromPure a Q φ →
  TCOr (TCEq a false) (BiAffine PROP) →
  Frame false ⌜φ⌝ Q emp | 2. (* Same cost as default. *)
Proof.
  rewrite /FromPure /Frame => <- [->|?] /=.
  - by rewrite right_id.
  - by rewrite right_id -affinely_affinely_if affine_affinely.
Qed.

Global Instance frame_embed `{!BiEmbed PROP PROP'} p P Q (Q' : PROP') R :
  Frame p R P Q → MakeEmbed Q Q' →
  Frame p ⎡R⎤ ⎡P⎤ Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeEmbed => <- <-.
  rewrite embed_sep embed_intuitionistically_if_2 => //.
Qed.
Global Instance frame_pure_embed `{!BiEmbed PROP PROP'} p P Q (Q' : PROP') φ :
  Frame p ⌜φ⌝ P Q → MakeEmbed Q Q' →
  Frame p ⌜φ⌝ ⎡P⎤ Q' | 2. (* Same cost as default. *)
Proof. rewrite /Frame /MakeEmbed -embed_pure. apply (frame_embed p P Q). Qed.

Global Instance frame_sep_persistent_l progress R P1 P2 Q1 Q2 Q' :
  Frame true R P1 Q1 →
  MaybeFrame true R P2 Q2 progress →
  MakeSep Q1 Q2 Q' →
  Frame true R (P1 ∗ P2) Q' | 9.
Proof.
  rewrite /Frame /MaybeFrame' /MakeSep /= => <- [<-] <-.
  rewrite {1}(intuitionistically_sep_dup R).
  by rewrite !assoc -(assoc _ _ _ Q1) -(comm _ Q1) assoc -(comm _ Q1).
Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame false R P1 Q → MakeSep Q P2 Q' → Frame false R (P1 ∗ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r p R P1 P2 Q Q' :
  Frame p R P2 Q → MakeSep P1 Q Q' → Frame p R (P1 ∗ P2) Q' | 10.
Proof.
  rewrite /Frame /MakeSep => <- <-. by rewrite assoc -(comm _ P1) assoc.
Qed.

Global Instance frame_big_sepL_cons {A} p (Φ : nat → A → PROP) R Q l x l' :
  IsCons l x l' →
  Frame p R (Φ 0 x ∗ [∗ list] k ↦ y ∈ l', Φ (S k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q | 2. (* Same cost as default. *)
Proof. rewrite /IsCons=>->. by rewrite /Frame big_sepL_cons. Qed.
Global Instance frame_big_sepL_app {A} p (Φ : nat → A → PROP) R Q l l1 l2 :
  IsApp l l1 l2 →
  Frame p R (([∗ list] k ↦ y ∈ l1, Φ k y) ∗
           [∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q | 2. (* Same cost as default. *)
Proof. rewrite /IsApp=>->. by rewrite /Frame big_sepL_app. Qed.

Global Instance frame_big_sepL2_cons {A B} p (Φ : nat → A → B → PROP)
    R Q l1 x1 l1' l2 x2 l2' :
  IsCons l1 x1 l1' → IsCons l2 x2 l2' →
  Frame p R (Φ 0 x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1';l2', Φ (S k) y1 y2) Q →
  Frame p R ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q. (* Default cost > 1. *)
Proof. rewrite /IsCons=>-> ->. by rewrite /Frame big_sepL2_cons. Qed.
Global Instance frame_big_sepL2_app {A B} p (Φ : nat → A → B → PROP)
    R Q l1 l1' l1'' l2 l2' l2'' :
  IsApp l1 l1' l1'' → IsApp l2 l2' l2'' →
  Frame p R (([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
           [∗ list] k ↦ y1;y2 ∈ l1'';l2'', Φ (length l1' + k) y1 y2) Q →
  Frame p R ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q.
Proof. rewrite /IsApp /Frame=>-> -> ->. apply wand_elim_l', big_sepL2_app. Qed.

Global Instance frame_big_sepMS_disj_union `{Countable A} p (Φ : A → PROP) R Q X X1 X2 :
  IsDisjUnion X X1 X2 ->
  Frame p R (([∗ mset] y ∈ X1, Φ y) ∗ [∗ mset] y ∈ X2, Φ y) Q →
  Frame p R ([∗ mset] y ∈ X, Φ y) Q | 2.
Proof. rewrite /IsDisjUnion=>->. by rewrite /Frame big_sepMS_disj_union. Qed.

(** The instances that allow framing under [∨] and [∧] need to be carefully
constructed. Such instances should make progress on at least one, but
possibly _both_ sides of the connective---unlike [∗], where we want to make
progress on exactly one side.

Naive implementations of this idea can cause Coq to do multiple searches
for [Frame] instances of the subterms. For terms with nested [∧]s or [∨]s,
this can cause an exponential blowup in the time it takes for Coq to
_fail_ to construct a [Frame] instance. This happens especially when the
resource we are framing in contains evars, since Coq's typeclass search
does more backtracking in this case.

To combat this, the [∧] and [∨] instances use [MaybeFrame] classes---
a notation for [MaybeFrame'] guarded by a [TCNoBackTrack]. The [MaybeFrame]
clauses for the subterms output a boolean [progress] indicator, on which some
condition is posed. The [TCNoBackTrack] ensures that when this condition is not
met, Coq will not backtrack on the [MaybeFrame] clauses to consider different
[progress]es. *)

(* For framing below [∧], we can frame [R] away in *both* conjuncts
(unlike with [∗] where we can only frame it in one conjunct).
We require at least one of those to make progress though. *)
Global Instance frame_and p progress1 progress2 R P1 P2 Q1 Q2 Q' :
  MaybeFrame p R P1 Q1 progress1 →
  MaybeFrame p R P2 Q2 progress2 →
  (** If below [TCEq] fails, the [frame_and] instance is immediately abandoned:
    the [TCNoBackTrack]s above prevent Coq from considering other ways to
    construct [MaybeFrame] instances. *)
  TCEq (progress1 || progress2) true →
  MakeAnd Q1 Q2 Q' →
  Frame p R (P1 ∧ P2) Q' | 9.
Proof.
  rewrite /MaybeFrame' /Frame /MakeAnd => [[<-]] [<-] _ <-.
  apply and_intro; [rewrite and_elim_l|rewrite and_elim_r]; done.
Qed.

(** We could in principle write the instance [frame_or_spatial] by a bunch of
instances (omitting the parameter [p = false]):

  Frame R P1 Q1 → Frame R P2 Q2 → Frame R (P1 ∨ P2) (Q1 ∨ Q2)
  Frame R P1 True → Frame R (P1 ∨ P2) P2
  Frame R P2 True → Frame R (P1 ∨ P2) P1

The problem here is that Coq will try to infer [Frame R P1 ?] and [Frame R P2 ?]
multiple times, whereas the current solution makes sure that said inference
appears at most once.

If Coq would memorize the results of type class resolution, the solution with
multiple instances would be preferred (and more Prolog-like). *)

(** Framing a spatial resource [R] under [∨] is done only when:
  - [R] can be framed on both sides of the [∨]; or
  - [R] completely solves one side of the [∨], reducing it to [True].
This instance does _not_ framing spatial resources when they can be framed in
exactly one side, since that can make your goal unprovable. *)
Global Instance frame_or_spatial progress1 progress2 R P1 P2 Q1 Q2 Q :
  MaybeFrame false R P1 Q1 progress1 →
  MaybeFrame false R P2 Q2 progress2 →
  (** Below [TCOr] encodes the condition described above. If this condition
    cannot be satisfied, the [frame_or_spatial] instance is immediately
    abandoned: the [TCNoBackTrack]s present in the [MaybeFrame] notation
    prevent Coq from considering other ways to construct [MaybeFrame']
    instances. *)
  TCOr (TCEq (progress1 && progress2) true) (TCOr
    (TCAnd (TCEq progress1 true) (TCEq Q1 True%I))
    (TCAnd (TCEq progress2 true) (TCEq Q2 True%I))) →
  MakeOr Q1 Q2 Q →
  Frame false R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => [[<-]] [<-] _ <-. by rewrite -sep_or_l. Qed.

(** Framing a persistent resource [R] under [∨] is done when [R] can be framed
on _at least_ one side. This does not affect provability of your goal,
since you can keep the resource after framing. *)
Global Instance frame_or_persistent progress1 progress2 R P1 P2 Q1 Q2 Q :
  MaybeFrame true R P1 Q1 progress1 →
  MaybeFrame true R P2 Q2 progress2 →
  (** If below [TCEq] fails, the [frame_or_persistent] instance is immediately
    abandoned: the [TCNoBackTrack]s present in the [MaybeFrame] notation
    prevent Coq from considering other ways to construct [MaybeFrame']
    instances. *)
  TCEq (progress1 || progress2) true →
  MakeOr Q1 Q2 Q → Frame true R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => [[<-]] [<-] _ <-. by rewrite -sep_or_l. Qed.

Global Instance frame_wand p R P1 P2 Q2 :
  (FrameInstantiateExistDisabled → Frame p R P2 Q2) →
  Frame p R (P1 -∗ P2) (P1 -∗ Q2) | 2.
Proof.
  rewrite /Frame=> /(_ ltac:(constructor)) ?. apply wand_intro_l.
  by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Qed.

Global Instance frame_affinely p R P Q Q' :
  TCOr (TCEq p true) (QuickAffine R) →
  Frame p R P Q → MakeAffinely Q Q' →
  Frame p R (<affine> P) Q'. (* Default cost > 1 *)
Proof.
  rewrite /QuickAffine /Frame /MakeAffinely=> -[->|?] <- <- /=;
    by rewrite -{1}(affine_affinely (_ R)) affinely_sep_2.
Qed.

Global Instance frame_intuitionistically R P Q Q' :
  Frame true R P Q → MakeIntuitionistically Q Q' →
  Frame true R (□ P) Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeIntuitionistically=> <- <- /=.
  rewrite -intuitionistically_sep_2 intuitionistically_idemp //.
Qed.

Global Instance frame_absorbingly p R P Q Q' :
  Frame p R P Q → MakeAbsorbingly Q Q' →
  Frame p R (<absorb> P) Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeAbsorbingly=> <- <- /=. by rewrite absorbingly_sep_r.
Qed.

Global Instance frame_persistently R P Q Q' :
  Frame true R P Q → MakePersistently Q Q' →
  Frame true R (<pers> P) Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakePersistently=> <- <- /=.
  rewrite -persistently_and_intuitionistically_sep_l.
  by rewrite -persistently_sep_2 -persistently_and_sep_l_1
    persistently_affinely_elim persistently_idemp.
Qed.

(** We construct an instance for [Frame]ing under existentials that can both
instantiate the existential and leave it untouched:

- If we have [H : P a] and goal [∃ b, P b ∗ Q b], framing [H] turns the goal
  into [Q a], i.e., instantiates the existential.
- If we have [H : P] and goal [∃ b, P ∗ Q b], framing [H] turns the goal
  into [∃ b, Q b], i.e., leaves the existential untouched.

Below we describe the instances. More information can be found in the paper
https://doi.org/10.1145/3636501.3636950 The general lemma is: *)
Local Lemma frame_exist_helper {A} p R (Φ : A → PROP)
    {C} (g : C → A) (Ψ : C → PROP) :
  (∀ c, Frame p R (Φ $ g c) (Ψ c)) →
  Frame p R (∃ a, Φ a) (∃ c, Ψ c).
Proof.
  rewrite /Frame=> HΨ. rewrite sep_exist_l.
  apply bi.exist_elim=> c. rewrite HΨ. apply exist_intro.
Qed.
(** [frame_exist_helper] captures the two common usecases:
- To instantiate the existential with witness [a], take [C = unit] and
  use [g = λ _, a].
- To keep the existential quantification untouched, take [C = A] and [g = id]
Note that having separate instances for these two cases is a bad idea:
typeclass search for [n] existential quantifiers would have [2^n] possibilities!

We cannot use [frame_exist] directly in type class search. One reason
is that we do not want to present the user with a useless existential
quantification on [unit]. This means we want to replace [∃ c, Φ c] with
the telescopic quantification [∃.. c, Φ c].
Another reason is that [frame_exist] does not indicate how [C] and [g] should
be inferred, so type class search would simply fail.

We want to infer these as follows. On a goal [Frame p R (∃ a, Φ a) _]:
- We first run type class search on [Frame p R (Φ ?a) _].
  If an instance is found, [?a] is a term that might still contain evars.
  The idea is to turn these evars back into existential quantifiers,
  whenever that is possible.
- To do so, choose [C] to be the telescope with types for each of the evars
  in [?a].
- This means [c : C] is (morally) a tuple with an element for each of the
  evars in [?a]---so we can unify all evars to be a projection of [c].
- After this unification, [?a] is an explicit function of [c], which means
  we have found [g].
*)

(** To perform above inference, we introduce a separate equality type class. *)
Inductive GatherEvarsEq {A} (x : A) : A → Prop := 
  GatherEvarsEq_refl : GatherEvarsEq x x.
Existing Class GatherEvarsEq.
(** The goal [GatherEvarsEq a (?g c)] with [a : A] and [g : ?C → A] is solved
in the way described above. This is done by tactic [solve_gather_evars_eq],
given at the end of this section, with an accompanying [Hint Extern]. *)

(** We are now able to state a lemma for building [Frame] instances directly:

[Lemma frame_exist_slow {A} p R (Φ : A → PROP)
    (TT : tele) (g : TT → A) (Ψ : TT → PROP) :
  (∀ c, ∃ a' G,
    Frame p R (Φ a') G ∧
    GatherEvarsEq a' (g c) ∧
    TCEq G (Ψ c)) →
  Frame p R (∃ a, Φ a) (∃.. c, Ψ c)%I.]

Although this would function as intended, the two inner [ex] and [conj]s
repeat terms in the implicit arguments; in particular, they repeat the
quantified goal [Φ] a bunch of times. This means the term size can get quite
big, and make type checking slower than need. We therefore make an effort to
reduce term size and type-checking time by creating a tailored [Class], which
furthermore can be solved automatically by type class search. *)
#[projections(primitive)] Class FrameExistRequirements
    (p : bool) (R : PROP) {A} (Φ : A → PROP) (a' : A) (G' : PROP) := {
  frame_exist_witness : A;
  frame_exist_resource : PROP;
  frame_exist_proof : Frame p R (Φ frame_exist_witness) frame_exist_resource;
  frame_exist_witness_eq : GatherEvarsEq frame_exist_witness a';
  frame_exist_resource_eq : TCEq frame_exist_resource G'
}.
Global Existing Instance Build_FrameExistRequirements.

(* This class is used so that we can [cbn] away the [bi_texist] in the result
of framing. This is done by the [Hint Extern] at the bottom of the file. *)
Inductive TCCbnTele {A} (x : A) : A → Prop :=
  TCCbnTele_refl : TCCbnTele x x.
Existing Class TCCbnTele.
Global Hint Mode TCCbnTele ! - - : typeclass_instances.

(* We include a dependency on [FrameInstantiateExistEnabled] so as to disable
this instance when framing beneath [∀], [-∗] and [→] *)
Global Instance frame_exist {A} p R (Φ : A → PROP)
    (TT : tele) (g : TT → A) (Ψ : TT → PROP) Q :
  FrameInstantiateExistEnabled →
  (∀ c, FrameExistRequirements p R Φ (g c) (Ψ c)) →
  TCCbnTele (∃.. c, Ψ c)%I Q →
  Frame p R (∃ a, Φ a) Q.
Proof.
  move=> _ H <-. rewrite /Frame bi_texist_exist.
  eapply frame_exist_helper=> c.
  by specialize (H c) as [a G HG -> ->].
Qed.
(* If [FrameInstantiateExistDisabled] holds we are not allowed to instantiate
existentials, so we just frame below the quantifier without instantiating
anything. *)
Global Instance frame_exist_no_instantiate {A} p R (Φ Ψ : A → PROP) :
  FrameInstantiateExistDisabled →
  (∀ a, Frame p R (Φ a) (Ψ a)) →
  Frame p R (∃ a, Φ a) (∃ a, Ψ a).
Proof. move=> _ H. eapply frame_exist_helper, H. Qed.

Global Instance frame_texist {TT : tele} p R (Φ Ψ : TT → PROP) :
  (∀ x, Frame p R (Φ x) (Ψ x)) → Frame p R (∃.. x, Φ x) (∃.. x, Ψ x) | 2.
Proof. rewrite /Frame !bi_texist_exist. apply frame_exist_helper. Qed.
Global Instance frame_forall {A} p R (Φ Ψ : A → PROP) :
  (FrameInstantiateExistDisabled → ∀ a, Frame p R (Φ a) (Ψ a)) →
  Frame p R (∀ x, Φ x) (∀ x, Ψ x) | 2.
Proof.
  rewrite /Frame=> /(_ ltac:(constructor)) ?.
  by rewrite sep_forall_l; apply forall_mono.
Qed.
Global Instance frame_tforall {TT : tele} p R (Φ Ψ : TT → PROP) :
  (FrameInstantiateExistDisabled → (∀ x, Frame p R (Φ x) (Ψ x))) →
  Frame p R (∀.. x, Φ x) (∀.. x, Ψ x) | 2.
Proof. rewrite /Frame !bi_tforall_forall. apply frame_forall. Qed.

Global Instance frame_impl_persistent R P1 P2 Q2 :
  (FrameInstantiateExistDisabled → Frame true R P2 Q2) →
  Frame true R (P1 → P2) (P1 → Q2) | 2.
Proof.
  rewrite /Frame /= => /(_ ltac:(constructor)) ?. apply impl_intro_l.
  by rewrite -persistently_and_intuitionistically_sep_l assoc (comm _ P1) -assoc impl_elim_r
             persistently_and_intuitionistically_sep_l.
Qed.
(** You may wonder why this uses [Persistent] and not [QuickPersistent].
The reason is that [QuickPersistent] is not needed anywhere else, and
even without [QuickPersistent], this instance avoids quadratic complexity:
we usually use the [Quick*] classes to not traverse the same term over and over
again, but here [P1] is encountered at most once. It is hence not worth adding
a new typeclass just for this extremely rarely used instance. *)
Global Instance frame_impl R P1 P2 Q2 :
  Persistent P1 → QuickAbsorbing P1 →
  (FrameInstantiateExistDisabled → Frame false R P2 Q2) →
  Frame false R (P1 → P2) (P1 → Q2). (* Default cost > 1 *)
Proof.
  rewrite /Frame /QuickAbsorbing /==> ?? /(_ ltac:(constructor)) ?.
  apply impl_intro_l.
  rewrite {1}(persistent P1) persistently_and_intuitionistically_sep_l assoc.
  rewrite (comm _ (□ P1)%I) -assoc -persistently_and_intuitionistically_sep_l.
  rewrite persistently_elim impl_elim_r //.
Qed.

Global Instance frame_eq_embed `{!BiEmbed PROP PROP', !BiInternalEq PROP,
    !BiInternalEq PROP', !BiEmbedInternalEq PROP PROP'}
    p P Q (Q' : PROP') {A : ofe} (a b : A) :
  Frame p (a ≡ b) P Q → MakeEmbed Q Q' →
  Frame p (a ≡ b) ⎡P⎤ Q'. (* Default cost > 1 *)
Proof. rewrite /Frame /MakeEmbed -embed_internal_eq. apply (frame_embed p P Q). Qed.

Global Instance frame_later p R R' P Q Q' :
  TCNoBackTrack (MaybeIntoLaterN true 1 R' R) →
  Frame p R P Q → MakeLaterN 1 Q Q' →
  Frame p R' (▷ P) Q'. (* Default cost > 1 *)
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite later_intuitionistically_if_2 later_sep.
Qed.
Global Instance frame_laterN p n R R' P Q Q' :
  TCNoBackTrack (MaybeIntoLaterN true n R' R) →
  Frame p R P Q → MakeLaterN n Q Q' →
  Frame p R' (▷^n P) Q'. (* Default cost > 1 *)
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite laterN_intuitionistically_if_2 laterN_sep.
Qed.

Global Instance frame_bupd `{!BiBUpd PROP} p R P Q :
  Frame p R P Q → Frame p R (|==> P) (|==> Q) | 2.
Proof. rewrite /Frame=><-. by rewrite bupd_frame_l. Qed.
Global Instance frame_fupd `{!BiFUpd PROP} p E1 E2 R P Q :
  Frame p R P Q → Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q) | 2.
Proof. rewrite /Frame=><-. by rewrite fupd_frame_l. Qed.

Global Instance frame_except_0 p R P Q Q' :
  Frame p R P Q → MakeExcept0 Q Q' →
  Frame p R (◇ P) Q' | 2. (* Same cost as default *)
Proof.
  rewrite /Frame /MakeExcept0=><- <-.
  by rewrite except_0_sep -(except_0_intro (□?p R)).
Qed.
End class_instances_frame.

(** We now write the tactic for constructing [GatherEvarsEq] instances.
We want to prove goals of shape [GatherEvarsEq a (?g c)] with [a : A],
and [g : ?C → A]. We need to infer both the function [g] and [C : tele].*)
Ltac solve_gather_evars_eq :=
  lazymatch goal with
  | |- GatherEvarsEq ?a (?g ?c) =>
    let rec retcon_tele T arg :=
      (* [retcon_tele] takes two arguments:
      - [T], an evar that has type [tele]
      - [arg], a term that has type [tele_arg T]
        (recall that [tele_arg] is the [tele → Type] coercion)
      [retcon_tele] will find all the evars occurring in [a], and unify [T]
      to be the telescope with types for all these evars. These evars will be
      unified with projections of [arg].
      In effect, it ensures 'retro-active continuity', namely that the
      telescope [T] was appropriately chosen all along. *)
      match a with
      | context [?term] =>
        is_evar term;
        let X := type of term in
        lazymatch X with
        | tele => fail (* Shortcircuit, since nesting telescopes is a bad idea *)
        | _ => idtac
        end;
        let T' := open_constr:(_) in (* creates a new evar *)
        unify T (TeleS (λ _ : X, T')); 
        (* The evar telescope [T'] is used for any remaining evars *)
        unify term (tele_arg_head (λ _ : X, T') arg);
        (* [tele_arg_head] is the first projection of [arg] *)
        retcon_tele T' (tele_arg_tail (λ _ : X, T') arg)
        (* recurse with the tail projection of [arg] *)
      | _ => 
        (* no more evars: unify [T] with the empty telescope *)
        unify T TeleO
      end
    in
    let T' := lazymatch (type of c) with tele_arg ?T => T end in
    retcon_tele T' c;
    exact (GatherEvarsEq_refl _)
  end.

Global Hint Extern 0 (GatherEvarsEq _ _) =>
  solve_gather_evars_eq : typeclass_instances.

Global Hint Extern 0 (TCCbnTele _ _) =>
  cbn [bi_texist tele_fold tele_bind tele_arg_head tele_arg_tail];
  exact (TCCbnTele_refl _) : typeclass_instances.
