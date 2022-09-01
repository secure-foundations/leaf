From stdpp Require Import namespaces hlist pretty.
From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import base intro_patterns spec_patterns
                                   sel_patterns coq_tactics reduction
                                   string_ident.
From iris.proofmode Require Export classes notation.
From iris.prelude Require Import options.
Export ident.

(** For most of the tactics, we want to have tight control over the order and
way in which type class inference is performed. To that end, many tactics make
use of [notypeclasses refine] and the [iSolveTC] tactic to manually invoke type
class inference.

The tactic [iSolveTC] does not use [apply _], as that often leads to issues
because it will try to solve all evars whose type is a typeclass, in
dependency order (according to Matthieu). If one fails, it aborts. However, we
generally rely on progress on the main goal to be solved to make progress
elsewhere. With [typeclasses eauto], that seems to work better.

A drawback of [typeclasses eauto] is that it is multi-success, i.e. whenever
subsequent tactics fail, it will backtrack to [typeclasses eauto] to try the
next type class instance. This is almost always undesired and leads to poor
performance and horrible error messages, so we wrap it in a [once]. *)
Ltac iSolveTC :=
  solve [once (typeclasses eauto)].

(** Tactic used for solving side-conditions arising from TC resolution in [iMod]
and [iInv]. *)
Ltac iSolveSideCondition :=
  lazymatch goal with
  | |- pm_error ?err => fail "" err
  | _ => split_and?; try solve [ fast_done | solve_ndisj | iSolveTC ]
  end.

(** Used for printing [string]s and [ident]s. *)
Ltac pretty_ident H :=
  lazymatch H with
  | INamed ?H => H
  | ?H => H
  end.

(** * Misc *)

Ltac iGetCtx :=
  lazymatch goal with
  | |- envs_entails ?Δ _ => Δ
  | |- context[ envs_split _ _ ?Δ ] => Δ
  end.

Ltac iMissingHypsCore Δ Hs :=
  let Hhyps := pm_eval (envs_dom Δ) in
  eval vm_compute in (list_difference Hs Hhyps).

Ltac iMissingHyps Hs :=
  let Δ := iGetCtx in
  iMissingHypsCore Δ Hs.

Ltac iTypeOf H :=
  let Δ := match goal with |- envs_entails ?Δ _ => Δ end in
  pm_eval (envs_lookup H Δ).

Ltac iBiOfGoal :=
  match goal with |- @envs_entails ?PROP _ _ => PROP end.

Tactic Notation "iMatchHyp" tactic1(tac) :=
  match goal with
  | |- context[ environments.Esnoc _ ?x ?P ] => tac x P
  end.

Tactic Notation "iSelect" open_constr(pat) tactic1(tac) :=
  lazymatch goal with
  | |- context[ environments.Esnoc _ ?x pat ] =>
    (* Before runnig [tac] on the hypothesis name [x] we must first unify the
       pattern [pat] with the term it matched against. This forces every evar
       coming from [pat] (and in particular from the [_] it contains and from
       the implicit arguments it uses) to be instantiated. If we do not do so
       then shelved goals are produced for every such evar. *)
    lazymatch iTypeOf x with
    | Some (_,?T) => unify T pat; tac x
    end
  end.

(** * Start a proof *)
Tactic Notation "iStartProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => idtac
  | |- ?φ => notypeclasses refine (as_emp_valid_2 φ _ _);
               [iSolveTC || fail "iStartProof: not a BI assertion"
               |notypeclasses refine (tac_start _ _)]
  end.

(* Same as above, with 2 differences :
   - We can specify a BI in which we want the proof to be done
   - If the goal starts with a let or a ∀, they are automatically
     introduced. *)
Tactic Notation "iStartProof" uconstr(PROP) :=
  lazymatch goal with
  | |- @envs_entails ?PROP' _ _ =>
    (* This cannot be shared with the other [iStartProof], because
    type_term has a non-negligible performance impact. *)
    let x := type_term (eq_refl : @eq Type PROP PROP') in idtac

  (* We eta-expand [as_emp_valid_2], in order to make sure that
     [iStartProof PROP] works even if [PROP] is the carrier type. In
     this case, typing this expression will end up unifying PROP with
     [bi_car _], and hence trigger the canonical structures mechanism
     to find the corresponding bi. *)
  | |- ?φ => notypeclasses refine ((λ P : PROP, @as_emp_valid_2 φ _ P) _ _ _);
               [iSolveTC || fail "iStartProof: not a BI assertion"
               |apply tac_start]
  end.

Tactic Notation "iStopProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => apply tac_stop; pm_reduce
  | |- _ => fail "iStopProof: proofmode not started"
  end.

(** * Generate a fresh identifier *)
(** The tactic [iFresh] bumps the fresh name counter in the proof mode
environment and returns the old value.

Note that we use [Ltac] instead of [Tactic Notation] since [Tactic Notation]
tactics can only have side-effects, but cannot return terms. *)
Ltac iFresh :=
  (* We make use of an Ltac hack to allow the [iFresh] tactic to both have a
  side-effect (i.e. to bump the counter) and to return a value (the fresh name).
  We do this by wrapped the side-effect under a [match] in a let-binding. See
  https://stackoverflow.com/a/46178884 *)
  let start :=
    lazymatch goal with
    | _ => iStartProof
    end in
  let c :=
    lazymatch goal with
    | |- envs_entails (Envs _ _ ?c) _ => c
    end in
  let inc :=
    lazymatch goal with
    | |- envs_entails (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails (Envs Δp Δs c') Q)
    end in
  constr:(IAnon c).

(** * Context manipulation *)
Tactic Notation "iRename" constr(H1) "into" constr(H2) :=
  eapply tac_rename with H1 H2 _ _; (* (i:=H1) (j:=H2) *)
    [pm_reflexivity ||
     let H1 := pretty_ident H1 in
     fail "iRename:" H1 "not found"
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H2 := pretty_ident H2 in
         fail "iRename:" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

Tactic Notation "iRename" "select" open_constr(pat) "into" constr(n) :=
  iSelect pat ltac:(fun H => iRename H into n).

(** Elaborated selection patterns, unlike the type [sel_pat], contains
only specific identifiers, and no wildcards like `#` (with the
exception of the pure selection pattern `%`) *)
Inductive esel_pat :=
  | ESelPure
  | ESelIdent : (* whether the ident is intuitionistic *) bool → ident → esel_pat.

Local Ltac iElaborateSelPat_go pat Δ Hs :=
  lazymatch pat with
  | [] => eval cbv in Hs
  | SelPure :: ?pat =>  iElaborateSelPat_go pat Δ (ESelPure :: Hs)
  | SelIntuitionistic :: ?pat =>
    let Hs' := pm_eval (env_dom (env_intuitionistic Δ)) in
    let Δ' := pm_eval (envs_clear_intuitionistic Δ) in
    iElaborateSelPat_go pat Δ' ((ESelIdent true <$> Hs') ++ Hs)
  | SelSpatial :: ?pat =>
    let Hs' := pm_eval (env_dom (env_spatial Δ)) in
    let Δ' := pm_eval (envs_clear_spatial Δ) in
    iElaborateSelPat_go pat Δ' ((ESelIdent false <$> Hs') ++ Hs)
  | SelIdent ?H :: ?pat =>
    lazymatch pm_eval (envs_lookup_delete false H Δ) with
    | Some (?p,_,?Δ') =>  iElaborateSelPat_go pat Δ' (ESelIdent p H :: Hs)
    | None =>
      let H := pretty_ident H in
      fail "iElaborateSelPat:" H "not found"
    end
  end.
(** Converts a selection pattern (given as a string) to a list of
elaborated selection patterns. *)
Ltac iElaborateSelPat pat :=
  lazymatch goal with
  | |- envs_entails ?Δ _ =>
    let pat := sel_pat.parse pat in iElaborateSelPat_go pat Δ (@nil esel_pat)
  end.

Local Ltac iClearHyp H :=
  eapply tac_clear with H _ _; (* (i:=H) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iClear:" H "not found"
    |pm_reduce; iSolveTC ||
     let H := pretty_ident H in
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iClear:" H ":" P "not affine and the goal not absorbing"
    |pm_reduce].

Local Ltac iClear_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs => clear; iClear_go Hs
  | ESelIdent _ ?H :: ?Hs => iClearHyp H; iClear_go Hs
  end.
Tactic Notation "iClear" constr(Hs) :=
  iStartProof; let Hs := iElaborateSelPat Hs in iClear_go Hs.

Tactic Notation "iClear" "(" ident_list(xs) ")" constr(Hs) :=
  iClear Hs; clear xs.

Tactic Notation "iClear" "select" open_constr(pat) :=
  iSelect pat ltac:(fun H => iClear H).

(** ** Simplification *)
Tactic Notation "iEval" tactic3(t) :=
  iStartProof;
  eapply tac_eval;
    [let x := fresh in intros x; t; unfold x; reflexivity
    |].

Local Ltac iEval_go t Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs => fail "iEval: %: unsupported selection pattern"
  | ESelIdent _ ?H :: ?Hs =>
    eapply tac_eval_in with H _ _ _;
      [pm_reflexivity || let H := pretty_ident H in fail "iEval:" H "not found"
      |let x := fresh in intros x; t; unfold x; reflexivity
      |pm_reduce; iEval_go t Hs]
  end.

Tactic Notation "iEval" tactic3(t) "in" constr(Hs) :=
  iStartProof; let Hs := iElaborateSelPat Hs in iEval_go t Hs.

Tactic Notation "iSimpl" := iEval (simpl).
Tactic Notation "iSimpl" "in" constr(H) := iEval (simpl) in H.

(* It would be nice to also have an `iSsrRewrite`, however, for this we need to
pass arguments to Ssreflect's `rewrite` like `/= foo /bar` in Ltac, see:

  https://sympa.inria.fr/sympa/arc/coq-club/2018-01/msg00000.html

PMP told me (= Robbert) in person that this is not possible with the current
Ltac, but it may be possible in Ltac2. *)

(** * Assumptions *)
Tactic Notation "iExact" constr(H) :=
  eapply tac_assumption with H _ _; (* (i:=H) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExact:" H "not found"
    |iSolveTC ||
     let H := pretty_ident H in
     let P := match goal with |- FromAssumption _ ?P _ => P end in
     fail "iExact:" H ":" P "does not match goal"
    |pm_reduce; iSolveTC ||
     let H := pretty_ident H in
     fail "iExact: remaining hypotheses not affine and the goal not absorbing"].

Tactic Notation "iAssumptionCore" :=
  let rec find Γ i P :=
    lazymatch Γ with
    | Esnoc ?Γ ?j ?Q => first [unify P Q; unify i j|find Γ i P]
    end in
  match goal with
  | |- envs_lookup ?i (Envs ?Γp ?Γs _) = Some (_, ?P) =>
     first [is_evar i; fail 1 | pm_reflexivity]
  | |- envs_lookup ?i (Envs ?Γp ?Γs _) = Some (_, ?P) =>
     is_evar i; first [find Γp i P | find Γs i P]; pm_reflexivity
  | |- envs_lookup_delete _ ?i (Envs ?Γp ?Γs _) = Some (_, ?P, _) =>
     first [is_evar i; fail 1 | pm_reflexivity]
  | |- envs_lookup_delete _ ?i (Envs ?Γp ?Γs _) = Some (_, ?P, _) =>
     is_evar i; first [find Γp i P | find Γs i P]; pm_reflexivity
  end.

Tactic Notation "iAssumptionCoq" :=
  let Hass := fresh in
  match goal with
  | H : ⊢ ?P |- envs_entails _ ?Q =>
     pose proof (_ : FromAssumption true P Q) as Hass;
     notypeclasses refine (tac_assumption_coq _ P _ H _ _);
       [exact Hass
       |pm_reduce; iSolveTC ||
        fail 2 "iAssumption: remaining hypotheses not affine and the goal not absorbing"]
  end.

Tactic Notation "iAssumption" :=
  let Hass := fresh in
  let rec find p Γ Q :=
    lazymatch Γ with
    | Esnoc ?Γ ?j ?P => first
       [pose proof (_ : FromAssumption p P Q) as Hass;
        eapply (tac_assumption _ j p P);
          [pm_reflexivity
          |exact Hass
          |pm_reduce; iSolveTC ||
           fail 2 "iAssumption: remaining hypotheses not affine and the goal not absorbing"]
       |assert (P = False%I) as Hass by reflexivity;
        apply (tac_false_destruct _ j p P);
          [pm_reflexivity
          |exact Hass]
       |find p Γ Q]
    end in
  lazymatch goal with
  | |- envs_entails (Envs ?Γp ?Γs _) ?Q =>
     first [find true Γp Q
           |find false Γs Q
           |iAssumptionCoq
           |fail "iAssumption:" Q "not found"]
  end.

(** * False *)
Tactic Notation "iExFalso" := apply tac_ex_falso.

(** * Making hypotheses intuitionistic or pure *)
Local Tactic Notation "iIntuitionistic" constr(H) :=
  eapply tac_intuitionistic with H _ _ _; (* (i:=H) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iIntuitionistic:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoPersistent _ ?P _ => P end in
     fail "iIntuitionistic:" P "not persistent"
    |pm_reduce; iSolveTC ||
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iIntuitionistic:" P "not affine and the goal not absorbing"
    |pm_reduce].

Local Tactic Notation "iSpatial" constr(H) :=
  eapply tac_spatial with H _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iSpatial:" H "not found"
    |pm_reduce; iSolveTC
    |pm_reduce].

Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
  eapply tac_pure with H _ _ _; (* (i:=H1) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iPure:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoPure ?P _ => P end in
     fail "iPure:" P "not pure"
    |pm_reduce; iSolveTC ||
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iPure:" P "not affine and the goal not absorbing"
    |pm_reduce; intros pat].

Tactic Notation "iEmpIntro" :=
  iStartProof;
  eapply tac_emp_intro;
    [pm_reduce; iSolveTC ||
     fail "iEmpIntro: spatial context contains non-affine hypotheses"].

Tactic Notation "iPureIntro" :=
  iStartProof;
  eapply tac_pure_intro;
    [iSolveTC ||
     let P := match goal with |- FromPure _ ?P _ => P end in
     fail "iPureIntro:" P "not pure"
    |pm_reduce; iSolveTC ||
     fail "iPureIntro: spatial context contains non-affine hypotheses"
    |].

(** Framing *)
(** Helper tactics are exposed for users that build their own custom framing
logic *)
Ltac iFrameFinish :=
  pm_prettify;
  try match goal with
  | |- envs_entails _ True => by iPureIntro
  | |- envs_entails _ emp => iEmpIntro
  end.

Ltac iFramePure t :=
  iStartProof;
  let φ := type of t in
  eapply (tac_frame_pure _ _ _ _ t);
    [iSolveTC || fail "iFrame: cannot frame" φ
    |iFrameFinish].

Ltac iFrameHyp H :=
  iStartProof;
  eapply tac_frame with H _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iFrame:" H "not found"
    |iSolveTC ||
     let R := match goal with |- Frame _ ?R _ _ => R end in
     fail "iFrame: cannot frame" R
    |pm_reduce; iFrameFinish].

Ltac iFrameAnyPure :=
  repeat match goal with H : _ |- _ => iFramePure H end.

Ltac iFrameAnyIntuitionistic :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval cbv in (env_dom (env_intuitionistic Δ)) in go Hs
  end.

Ltac iFrameAnySpatial :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
  end.

Tactic Notation "iFrame" := iFrameAnySpatial.

Tactic Notation "iFrame" "(" constr(t1) ")" :=
  iFramePure t1.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" :=
  iFramePure t1; iFrame ( t2 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" :=
  iFramePure t1; iFrame ( t2 t3 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ).

Local Ltac iFrame_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | SelPure :: ?Hs => iFrameAnyPure; iFrame_go Hs
  | SelIntuitionistic :: ?Hs => iFrameAnyIntuitionistic; iFrame_go Hs
  | SelSpatial :: ?Hs => iFrameAnySpatial; iFrame_go Hs
  | SelIdent ?H :: ?Hs => iFrameHyp H; iFrame_go Hs
  end.

Tactic Notation "iFrame" constr(Hs) :=
  let Hs := sel_pat.parse Hs in iFrame_go Hs.
Tactic Notation "iFrame" "(" constr(t1) ")" constr(Hs) :=
  iFramePure t1; iFrame Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")"
    constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ) Hs.

Tactic Notation "iFrame" "select" open_constr(pat) :=
  iSelect pat ltac:(fun H => iFrame H).

(** * Basic introduction tactics *)
Local Tactic Notation "iIntro" "(" simple_intropattern(x) ")" :=
  (* In the case the goal starts with an [let x := _ in _], we do not
     want to unfold x and start the proof mode. Instead, we want to
     use intros. So [iStartProof] has to be called only if [intros]
     fails *)
  (* We use [_ || _] instead of [first [..|..]] so that the error in the second
  branch propagates upwards. *)
  (
    (* introduction at the meta level *)
    intros x
  ) || (
    (* introduction in the logic *)
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ _ =>
      eapply tac_forall_intro;
        [iSolveTC ||
         let P := match goal with |- FromForall ?P _ _ => P end in
         fail "iIntro: cannot turn" P "into a universal quantifier"
        |let name := lazymatch goal with
                     | |- let _ := (λ name, _) in _ => name
                     end in
         pm_prettify;
         let y := fresh name in
         intros y; revert y; intros x
         (* subgoal *)]
    end).

Local Tactic Notation "iIntro" constr(H) :=
  iStartProof;
  first
  [(* (?Q → _) *)
    eapply tac_impl_intro with H _ _ _; (* (i:=H) *)
      [iSolveTC
      |pm_reduce; iSolveTC ||
       let P := lazymatch goal with |- Persistent ?P => P end in
       let H := pretty_ident H in
       fail 1 "iIntro: introducing non-persistent" H ":" P
              "into non-empty spatial context"
      |iSolveTC
      |pm_reduce;
       let H := pretty_ident H in
        lazymatch goal with
        | |- False =>
          let H := pretty_ident H in
          fail 1 "iIntro:" H "not fresh"
        | _ => idtac (* subgoal *)
        end]
  |(* (_ -∗ _) *)
    eapply tac_wand_intro with H _ _; (* (i:=H) *)
      [iSolveTC
      | pm_reduce;
        lazymatch goal with
        | |- False =>
          let H := pretty_ident H in
          fail 1 "iIntro:" H "not fresh"
        | _ => idtac (* subgoal *)
        end]
  | let H := pretty_ident H in
    fail 1 "iIntro: could not introduce" H ", goal is not a wand or implication" ].

Local Tactic Notation "iIntro" "#" constr(H) :=
  iStartProof;
  first
  [(* (?P → _) *)
   eapply tac_impl_intro_intuitionistic with H _ _ _; (* (i:=H) *)
     [iSolveTC
     |iSolveTC ||
      let P := match goal with |- IntoPersistent _ ?P _ => P end in
      fail 1 "iIntro:" P "not persistent"
     |pm_reduce;
      lazymatch goal with
      | |- False =>
        let H := pretty_ident H in
        fail 1 "iIntro:" H "not fresh"
      | _ => idtac (* subgoal *)
      end]
  |(* (?P -∗ _) *)
   eapply tac_wand_intro_intuitionistic with H _ _ _; (* (i:=H) *)
     [iSolveTC
     |iSolveTC ||
      let P := match goal with |- IntoPersistent _ ?P _ => P end in
      fail 1 "iIntro:" P "not intuitionistic"
     |iSolveTC ||
      let P := match goal with |- TCOr (Affine ?P) _ => P end in
      fail 1 "iIntro:" P "not affine and the goal not absorbing"
     |pm_reduce;
      lazymatch goal with
      | |- False =>
        let H := pretty_ident H in
        fail 1 "iIntro:" H "not fresh"
      | _ => idtac (* subgoal *)
      end]
  |fail 1 "iIntro: nothing to introduce"].

Local Tactic Notation "iIntro" constr(H) "as" constr(p) :=
  lazymatch p with
  | true => iIntro #H
  | _ =>  iIntro H
  end.

Local Tactic Notation "iIntro" "_" :=
  iStartProof;
  first
  [(* (?Q → _) *)
   eapply tac_impl_intro_drop;
     [iSolveTC
     |(* subgoal *)]
  |(* (_ -∗ _) *)
   eapply tac_wand_intro_drop;
     [iSolveTC
     |iSolveTC ||
      let P := match goal with |- TCOr (Affine ?P) _ => P end in
      fail 1 "iIntro:" P "not affine and the goal not absorbing"
     |(* subgoal *)]
  |(* (∀ _, _) *)
   iIntro (_)
   (* subgoal *)
  |fail 1 "iIntro: nothing to introduce"].

Local Tactic Notation "iIntroForall" :=
  lazymatch goal with
  | |- ∀ _, ?P => fail (* actually an →, this is handled by iIntro below *)
  | |- ∀ _, _ => intro
  | |- let _ := _ in _ => intro
  | |- _ =>
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (∀ x : _, _) => let x' := fresh x in iIntro (x')
    end
  end.
Local Tactic Notation "iIntro" :=
  lazymatch goal with
  | |- _ → ?P => intro
  | |- _ =>
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (_ -∗ _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
    | |- envs_entails _ (_ → _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
    end
  end.

(** * Revert *)
Local Tactic Notation "iForallRevert" ident(x) :=
  let err x :=
    intros x;
    iMatchHyp (fun H P =>
      lazymatch P with
      | context [x] =>
         let H := pretty_ident H in fail 2 "iRevert:" x "is used in hypothesis" H
      end) in
  iStartProof;
  first [let A := type of x in idtac|fail 1 "iRevert:" x "not in scope"];
  let A := type of x in
  lazymatch type of A with
  | Prop => revert x; first [apply tac_pure_revert|err x]
  | _ => revert x; first [apply tac_forall_revert|err x]
  end.

(** The tactic [iRevertHyp H with tac] reverts the hypothesis [H] and calls
[tac] with a Boolean that is [true] iff [H] was in the intuitionistic context. *)
Tactic Notation "iRevertHyp" constr(H) "with" tactic1(tac) :=
  eapply tac_revert with H;
    [lazymatch goal with
     | |- match envs_lookup_delete true ?i ?Δ with _ => _ end =>
        lazymatch eval pm_eval in (envs_lookup_delete true i Δ) with
        | Some (?p,_,_) => pm_reduce; tac p
        | None =>
           let H := pretty_ident H in
           fail "iRevert:" H "not found"
        end
     end].

Tactic Notation "iRevertHyp" constr(H) := iRevertHyp H with (fun _ => idtac).

Tactic Notation "iRevert" constr(Hs) :=
  let rec go Hs :=
    lazymatch Hs with
    | [] => idtac
    | ESelPure :: ?Hs =>
       repeat match goal with x : _ |- _ => revert x end;
       go Hs
    | ESelIdent _ ?H :: ?Hs => iRevertHyp H; go Hs
    end in
  iStartProof; let Hs := iElaborateSelPat Hs in go Hs.

Tactic Notation "iRevert" "(" ident(x1) ")" :=
  iForallRevert x1.
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" :=
  iForallRevert x2; iRevert ( x1 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" :=
  iForallRevert x3; iRevert ( x1 x2 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
  iForallRevert x4; iRevert ( x1 x2 x3 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" :=
  iForallRevert x5; iRevert ( x1 x2 x3 x4 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" :=
  iForallRevert x6; iRevert ( x1 x2 x3 x4 x5 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" :=
  iForallRevert x7; iRevert ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" :=
  iForallRevert x8; iRevert ( x1 x2 x3 x4 x5 x6 x7 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")" :=
  iForallRevert x9; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ")" :=
  iForallRevert x10; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ")" :=
  iForallRevert x11; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ")" :=
  iForallRevert x12; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ident(x13) ")" :=
  iForallRevert x13; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ident(x13) ident(x14) ")" :=
  iForallRevert x14; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ident(x13) ident(x14) ident(x15) ")" :=
  iForallRevert x15; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ).

Tactic Notation "iRevert" "(" ident(x1) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ident(x13) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ident(x13) ident(x14) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ).
Tactic Notation "iRevert" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
    ident(x11) ident(x12) ident(x13) ident(x14) ident(x15) ")" constr(Hs) :=
  iRevert Hs; iRevert ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ).

Tactic Notation "iRevert" "select" open_constr(pat) :=
  iSelect pat ltac:(fun H => iRevert H).

(** * The specialize and pose proof tactics *)
Record iTrm {X As S} :=
  ITrm { itrm : X ; itrm_vars : hlist As ; itrm_hyps : S }.
Global Arguments ITrm {_ _ _} _ _ _.

Notation "( H $! x1 .. xn )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) "") (at level 0, x1, xn at level 9).
Notation "( H $! x1 .. xn 'with' pat )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) pat) (at level 0, x1, xn at level 9).
Notation "( H 'with' pat )" := (ITrm H hnil pat) (at level 0).

Tactic Notation "iPoseProofCoreHyp" constr(H) "as" constr(Hnew) :=
  let Δ := iGetCtx in
  notypeclasses refine (tac_pose_proof_hyp _ H Hnew _ _);
    pm_reduce;
    lazymatch goal with
    | |- False =>
      let lookup := pm_eval (envs_lookup_delete false H Δ) in
      lazymatch lookup with
      | None =>
        let H := pretty_ident H in
        fail "iPoseProof:" H "not found"
      | _ =>
        let Hnew := pretty_ident Hnew in
        fail "iPoseProof:" Hnew "not fresh"
      end
    | _ => idtac
    end.

(* The tactic [iIntoEmpValid] tactic "imports a Coq lemma into the proofmode",
i.e., it solves a goal [IntoEmpValid ψ ?Q]. The argument [ψ] must be of the
following shape:

[∀ (x_1 : A_1) .. (x_n : A_n), φ]

for which we have an instance [AsEmpValid φ ?Q].

Examples of such [φ]s are

- [⊢ P], in which case [?Q] is unified with [P].
- [P1 ⊢ P2], in which case [?Q] is unified with [P1 -∗ P2].
- [P1 ⊣⊢ P2], in which case [?Q] is unified with [P1 ↔ P2].

The tactic instantiates each dependent argument [x_i : A_i] with an evar, and
generates a goal [A_i] for each non-dependent argument [x_i : A_i].

For example, if goal is [IntoEmpValid (∀ x, P x → R1 x ⊢ R2 x) ?Q], then the
[iIntoEmpValid] tactic generates an evar [?x], a subgoal [P ?x], and unifies
[?Q] with [R1 ?x -∗ R2 ?x]. *)
Ltac iIntoEmpValid_go := first
  [(* Case [φ → ψ] *)
   notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
     [(*goal for [φ] *)|iIntoEmpValid_go]
  |(* Case [∀ x : A, φ] *)
   notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
  |(* Case [∀.. x : TT, φ] *)
   notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
  |(* Case [P ⊢ Q], [P ⊣⊢ Q], [⊢ P] *)
   notypeclasses refine (into_emp_valid_here _ _ _)].

Ltac iIntoEmpValid :=
  (* Factor out the base case of the loop to avoid needless backtracking *)
  iIntoEmpValid_go;
    [.. (* goals for premises *)
    |iSolveTC ||
     let φ := lazymatch goal with |- AsEmpValid ?φ _ => φ end in
     fail "iPoseProof:" φ "not a BI assertion"].

Tactic Notation "iPoseProofCoreLem" open_constr(lem) "as" tactic3(tac) :=
  let Hnew := iFresh in
  notypeclasses refine (tac_pose_proof _ Hnew _ _ (into_emp_valid_proj _ _ _ lem) _);
    [iIntoEmpValid
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let Hnew := pretty_ident Hnew in
       fail "iPoseProof:" Hnew "not fresh"
     | _ => tac Hnew
     end];
  (* Solve all remaining TC premises generated by [iIntoEmpValid] *)
  try iSolveTC.

(** There is some hacky stuff going on here: because of Coq bug #6583, unresolved
type classes in e.g. the arguments [xs] of [iSpecializeArgs_go] are resolved at
arbitrary moments. That is because tactics like [apply], [split] and [eexists]
wrongly trigger type class search. To avoid TC being triggered too eagerly, the
tactics below use [notypeclasses refine] instead of [apply], [split] and
[eexists]. *)
Local Ltac iSpecializeArgs_go H xs :=
  lazymatch xs with
  | hnil => idtac
  | hcons ?x ?xs =>
     notypeclasses refine (tac_forall_specialize _ H _ _ _ _ _ _ _);
       [pm_reflexivity ||
        let H := pretty_ident H in
        fail "iSpecialize:" H "not found"
       |iSolveTC ||
        let P := match goal with |- IntoForall ?P _ => P end in
        fail "iSpecialize: cannot instantiate" P "with" x
       |lazymatch goal with (* Force [A] in [ex_intro] to deal with coercions. *)
        | |- ∃ _ : ?A, _ =>
          notypeclasses refine (@ex_intro A _ x _)
        end; [shelve..|pm_reduce; iSpecializeArgs_go H xs]]
  end.
Local Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
  iSpecializeArgs_go H xs.

Ltac iSpecializePat_go H1 pats :=
  let solve_to_wand H1 :=
    iSolveTC ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand" in
  let solve_done d :=
    lazymatch d with
    | true =>
       first [ done
             | let Q := match goal with |- envs_entails _ ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done"
             | let Q := match goal with |- ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done" ]
    | false => idtac
    end in
  let Δ := iGetCtx in
  lazymatch pats with
    | [] => idtac
    | SForall :: ?pats =>
       idtac "[IPM] The * specialization pattern is deprecated because it is applied implicitly.";
       iSpecializePat_go H1 pats
    | SIdent ?H2 [] :: ?pats =>
       (* If we not need to specialize [H2] we can avoid a lot of unncessary
       context manipulation. *)
       notypeclasses refine (tac_specialize false _ H2 _ H1 _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H2 := pretty_ident H2 in
          fail "iSpecialize:" H2 "not found"
         |pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |iSolveTC ||
          let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in
          let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in
          fail "iSpecialize: cannot instantiate" P "with" Q
         |pm_reduce; iSpecializePat_go H1 pats]
    | SIdent ?H2 ?pats1 :: ?pats =>
       (* If [H2] is in the intuitionistic context, we copy it into a new
       hypothesis [Htmp], so that it can be used multiple times. *)
       let H2tmp := iFresh in
       iPoseProofCoreHyp H2 as H2tmp;
       (* Revert [H1] and re-introduce it later so that it will not be consumsed
       by [pats1]. *)
       iRevertHyp H1 with (fun p =>
         iSpecializePat_go H2tmp pats1;
           [.. (* side-conditions of [iSpecialize] *)
           |iIntro H1 as p]);
         (* We put the stuff below outside of the closure to get less verbose
         Ltac backtraces (which would otherwise include the whole closure). *)
         [.. (* side-conditions of [iSpecialize] *)
         |(* Use [remove_intuitionistic = true] to remove the copy [Htmp]. *)
          notypeclasses refine (tac_specialize true _ H2tmp _ H1 _ _ _ _ _ _ _ _ _);
            [pm_reflexivity ||
             let H2tmp := pretty_ident H2tmp in
             fail "iSpecialize:" H2tmp "not found"
            |pm_reflexivity ||
             let H1 := pretty_ident H1 in
             fail "iSpecialize:" H1 "not found"
            |iSolveTC ||
             let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in
             let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in
             fail "iSpecialize: cannot instantiate" P "with" Q
            |pm_reduce; iSpecializePat_go H1 pats]]
    | SPureGoal ?d :: ?pats =>
       notypeclasses refine (tac_specialize_assert_pure _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |iSolveTC ||
          let Q := match goal with |- FromPure _ ?Q _ => Q end in
          fail "iSpecialize:" Q "not pure"
         |solve_done d (*goal*)
         |pm_reduce;
          iSpecializePat_go H1 pats]
    | SGoal (SpecGoal GIntuitionistic false ?Hs_frame [] ?d) :: ?pats =>
       notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |iSolveTC ||
          let Q := match goal with |- Persistent ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |iSolveTC
         |pm_reduce; iFrame Hs_frame; solve_done d (*goal*)
         |pm_reduce; iSpecializePat_go H1 pats]
    | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: ?pats =>
       fail "iSpecialize: cannot select hypotheses for intuitionistic premise"
    | SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d) :: ?pats =>
       let Hs' := eval cbv in (if lr then Hs else Hs_frame ++ Hs) in
       notypeclasses refine (tac_specialize_assert _ H1 _
           (if m is GModal then true else false) lr Hs' _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |iSolveTC || fail "iSpecialize: goal not a modality"
         |pm_reduce;
          lazymatch goal with
          | |- False =>
            let Hs' := iMissingHypsCore Δ Hs' in
            fail "iSpecialize: hypotheses" Hs' "not found"
          | _ =>
            notypeclasses refine (conj _ _);
              [iFrame Hs_frame; solve_done d (*goal*)
              |iSpecializePat_go H1 pats]
          end]
    | SAutoFrame GIntuitionistic :: ?pats =>
       notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |iSolveTC ||
          let Q := match goal with |- Persistent ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |pm_reduce; solve [iFrame "∗ #"]
         |pm_reduce; iSpecializePat_go H1 pats]
    | SAutoFrame ?m :: ?pats =>
       notypeclasses refine (tac_specialize_frame _ H1 _
           (if m is GModal then true else false) _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |iSolveTC || fail "iSpecialize: goal not a modality"
         |pm_reduce;
          first
            [notypeclasses refine (tac_unlock_emp _ _ _)
            |notypeclasses refine (tac_unlock_True _ _ _)
            |iFrame "∗ #"; notypeclasses refine (tac_unlock _ _ _)
            |fail "iSpecialize: premise cannot be solved by framing"]
         |exact eq_refl]; iIntro H1; iSpecializePat_go H1 pats
    end.

Local Tactic Notation "iSpecializePat" open_constr(H) constr(pat) :=
  let pats := spec_pat.parse pat in iSpecializePat_go H pats.

(** The tactics [iSpecialize trm as #] and [iSpecializeCore trm as true] allow
one to use the entire spatial context /twice/: the first time for proving the
premises [Q1 .. Qn] of [H : Q1 -* .. -∗ Qn -∗ R], and the second time for
proving the remaining goal. This is possible if all of the following properties
hold:
1. The conclusion [R] of the hypothesis [H] is persistent.
2. The specialization pattern [[> ..]] for wrapping a modality is not used for
   any of the premises [Q1 .. Qn].
3. The BI is either affine, or the hypothesis [H] resides in the intuitionistic
   context.

The copying of the context for proving the premises of [H] and the remaining
goal is implemented using the lemma [tac_specialize_intuitionistic_helper].

Since the tactic [iSpecialize .. as #] is used a helper to implement
[iDestruct .. as "#.."], [iPoseProof .. as "#.."], [iSpecialize .. as "#.."],
and friends, the behavior on violations of these conditions is as follows:

- If condition 1 is violated (i.e. the conclusion [R] of [H] is not persistent),
  the tactic will fail.
- If condition 2 or 3 is violated, the tactic will fall back to consuming the
  hypotheses for proving the premises [Q1 .. Qn]. That is, it will fall back to
  not using [tac_specialize_intuitionistic_helper].

The function [use_tac_specialize_intuitionistic_helper Δ pat] below returns
[true] iff the specialization pattern [pat] consumes any spatial hypotheses,
and does not contain the pattern [[> ..]] (cf. condition 2). If the function
returns [false], then the conclusion can be moved in the intuitionistic context
even if conditions 1 and 3 do not hold. Therefore, in that case, we prefer
putting the conclusion to the intuitionistic context directly and not using
[tac_specialize_intuitionistic_helper], which requires conditions 1 and 3. *)
Fixpoint use_tac_specialize_intuitionistic_helper {M}
    (Δ : envs M) (pats : list spec_pat) : bool :=
  match pats with
  | [] => false
  | (SForall | SPureGoal _) :: pats =>
     use_tac_specialize_intuitionistic_helper Δ pats
  | SAutoFrame _ :: _ => true
  | SIdent H _ :: pats =>
     match envs_lookup_delete false H Δ with
     | Some (false, _, Δ) => true
     | Some (true, _, Δ) => use_tac_specialize_intuitionistic_helper Δ pats
     | None => false (* dummy case (invalid pattern, will fail in the tactic anyway) *)
     end
  | SGoal (SpecGoal GModal _ _ _ _) :: _ => false
  | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: pats =>
     use_tac_specialize_intuitionistic_helper Δ pats
  | SGoal (SpecGoal GSpatial neg Hs_frame Hs _) :: pats =>
     match envs_split (if neg is true then Right else Left)
                      (if neg then Hs else pm_app Hs_frame Hs) Δ with
     | Some (Δ1,Δ2) => if env_spatial_is_nil Δ1
                       then use_tac_specialize_intuitionistic_helper Δ2 pats
                       else true
     | None => false (* dummy case (invalid pattern, will fail in the tactic anyway) *)
     end
  end.

(** The argument [p] of [iSpecializeCore] can either be a Boolean, or an
introduction pattern that is coerced into [true] when it solely contains [#] or
[%] patterns at the top-level. *)
Tactic Notation "iSpecializeCore" open_constr(H)
    "with" open_constr(xs) open_constr(pat) "as" constr(p) :=
  let p := intro_pat_intuitionistic p in
  let pat := spec_pat.parse pat in
  let H :=
    lazymatch type of H with
    | string => constr:(INamed H)
    | _ => H
    end in
  iSpecializeArgs H xs; [..|
    lazymatch type of H with
    | ident =>
       let pat := spec_pat.parse pat in
       let Δ := iGetCtx in
       (* Check if we should use [tac_specialize_intuitionistic_helper]. Notice
       that [pm_eval] does not unfold [use_tac_specialize_intuitionistic_helper],
       so we should do that first. *)
       let b := eval cbv [use_tac_specialize_intuitionistic_helper] in
         (if p then use_tac_specialize_intuitionistic_helper Δ pat else false) in
       lazymatch eval pm_eval in b with
       | true =>
          (* Check that the BI is either affine, or the hypothesis [H] resides
          in the intuitionistic context. *)
          lazymatch iTypeOf H with
          | Some (?q, _) =>
             let PROP := iBiOfGoal in
             lazymatch eval compute in (q || tc_to_bool (BiAffine PROP)) with
             | true =>
                notypeclasses refine (tac_specialize_intuitionistic_helper _ H _ _ _ _ _ _ _ _ _ _);
                  [pm_reflexivity
                   (* This premise, [envs_lookup j Δ = Some (q,P)],
                   holds because the [iTypeOf] above succeeded *)
                  |pm_reduce; iSolveTC
                   (* This premise, [if q then TCTrue else BiAffine PROP], holds
                   because we established that [q || TC_to_bool (BiAffine PROP)]
                   is true *)
                  |iSpecializePat H pat;
                    [..
                    |notypeclasses refine (tac_specialize_intuitionistic_helper_done _ H _ _ _);
                     pm_reflexivity]
                  |iSolveTC ||
                   let Q := match goal with |- IntoPersistent _ ?Q _ => Q end in
                   fail "iSpecialize:" Q "not persistent"
                  |pm_reduce (* goal *)]
             | false => iSpecializePat H pat
             end
          | None =>
             let H := pretty_ident H in
             fail "iSpecialize:" H "not found"
          end
       | false => iSpecializePat H pat
       end
    | _ => fail "iSpecialize:" H "should be a hypothesis, use iPoseProof instead"
    end].

Tactic Notation "iSpecializeCore" open_constr(t) "as" constr(p) :=
  lazymatch type of t with
  | string => iSpecializeCore t with hnil "" as p
  | ident => iSpecializeCore t with hnil "" as p
  | _ =>
    lazymatch t with
    | ITrm ?H ?xs ?pat => iSpecializeCore H with xs pat as p
    | _ => fail "iSpecialize:" t "should be a proof mode term"
    end
  end.

Tactic Notation "iSpecialize" open_constr(t) :=
  iSpecializeCore t as false.
Tactic Notation "iSpecialize" open_constr(t) "as" "#" :=
  iSpecializeCore t as true.

(** The tactic [iPoseProofCore lem as p tac] inserts the resource
described by [lem] into the context. The tactic takes a continuation [tac] as
its argument, which is called with a temporary fresh name [H] that refers to
the hypothesis containing [lem].

The argument [p] is like that of [iSpecialize]. It is a Boolean that denotes
whether the conclusion of the specialized term [lem] is persistent. *)
Tactic Notation "iPoseProofCore" open_constr(lem)
    "as" constr(p) tactic3(tac) :=
  iStartProof;
  let t := lazymatch lem with ITrm ?t ?xs ?pat => t | _ => lem end in
  let t := lazymatch type of t with string => constr:(INamed t) | _ => t end in
  let spec_tac Htmp :=
    lazymatch lem with
    | ITrm _ ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as p
    | _ => idtac
    end in
  lazymatch type of t with
  | ident =>
     let Htmp := iFresh in
     iPoseProofCoreHyp t as Htmp; spec_tac Htmp; [..|tac Htmp]
  | _ => iPoseProofCoreLem t as (fun Htmp => spec_tac Htmp; [..|tac Htmp])
  end.

(** * The apply tactic *)
(** [iApply lem] takes an argument [lem : P₁ -∗ .. -∗ Pₙ -∗ Q] (after the
specialization patterns in [lem] have been executed), where [Q] should match
the goal, and generates new goals [P1] ... [Pₙ]. Depending on the number of
premises [n], the tactic will have the following behavior:

- If [n = 0], it will immediately solve the goal (i.e. it will not generate any
  subgoals). When working in a general BI, this means that the tactic can fail
  in case there are non-affine spatial hypotheses in the context prior to using
  the [iApply] tactic. Note that if [n = 0], the tactic behaves exactly like
  [iExact lem].
- If [n > 0] it will generate a goals [P₁] ... [Pₙ]. All spatial hypotheses
  will be transferred to the last goal, i.e. [Pₙ]; the other goals will receive
  no spatial hypotheses. If you want to control more precisely how the spatial
  hypotheses are subdivided, you should add additional introduction patterns to
  [lem]. *)

(* The helper [iApplyHypExact] takes care of the [n=0] case. It fails with level
0 if we should proceed to the [n > 0] case, and with level 1 if there is an
actual error. *)
Local Ltac iApplyHypExact H :=
  eapply tac_assumption with H _ _; (* (i:=H) *)
    [pm_reflexivity
    |iSolveTC
    |pm_reduce; iSolveTC ||
     fail 1 "iApply: remaining hypotheses not affine and the goal not absorbing"].

Local Ltac iApplyHypLoop H :=
  first
    [eapply tac_apply with H _ _ _;
      [pm_reflexivity
      |iSolveTC
      |pm_reduce;
       pm_prettify (* reduce redexes created by instantiation *)]
    |iSpecializePat H "[]"; last iApplyHypLoop H].

Tactic Notation "iApplyHyp" constr(H) :=
  first
    [iApplyHypExact H
    |iApplyHypLoop H
    |lazymatch iTypeOf H with
     | Some (_,?Q) => fail 1 "iApply: cannot apply" Q
     end].

Tactic Notation "iApply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H => iApplyHyp H).

(** * Disjunction *)
Tactic Notation "iLeft" :=
  iStartProof;
  eapply tac_or_l;
    [iSolveTC ||
     let P := match goal with |- FromOr ?P _ _ => P end in
     fail "iLeft:" P "not a disjunction"
    |(* subgoal *)].
Tactic Notation "iRight" :=
  iStartProof;
  eapply tac_or_r;
    [iSolveTC ||
     let P := match goal with |- FromOr ?P _ _ => P end in
     fail "iRight:" P "not a disjunction"
    |(* subgoal *)].

Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_or_destruct with H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iOrDestruct:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoOr ?P _ _ => P end in
     fail "iOrDestruct: cannot destruct" P
    | pm_reduce;
      lazymatch goal with
      | |- False =>
        let H1 := pretty_ident H1 in
        let H2 := pretty_ident H2 in
        fail "iOrDestruct:" H1 "or" H2 "not fresh"
      |  _ => split
      end].

(** * Conjunction and separating conjunction *)
Tactic Notation "iSplit" :=
  iStartProof;
  eapply tac_and_split;
    [iSolveTC ||
     let P := match goal with |- FromAnd ?P _ _ => P end in
     fail "iSplit:" P "not a conjunction"
    |(* subgoal 1 *)
    |(* subgoal 2 *)].

Tactic Notation "iSplitL" constr(Hs) :=
  iStartProof;
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let Δ := iGetCtx in
  eapply tac_sep_split with Left Hs _ _; (* (js:=Hs) *)
    [iSolveTC ||
     let P := match goal with |- FromSep ?P _ _ => P end in
     fail "iSplitL:" P "not a separating conjunction"
    |pm_reduce;
     lazymatch goal with
     | |- False => let Hs := iMissingHypsCore Δ Hs in
                 fail "iSplitL: hypotheses" Hs "not found"
     | _ => split; [(* subgoal 1 *)|(* subgoal 2 *)]
     end].

Tactic Notation "iSplitR" constr(Hs) :=
  iStartProof;
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let Δ := iGetCtx in
  eapply tac_sep_split with Right Hs _ _; (* (js:=Hs) *)
    [iSolveTC ||
     let P := match goal with |- FromSep ?P _ _ => P end in
     fail "iSplitR:" P "not a separating conjunction"
    |pm_reduce;
     lazymatch goal with
     | |- False => let Hs := iMissingHypsCore Δ Hs in
                 fail "iSplitR: hypotheses" Hs "not found"
     | _ => split; [(* subgoal 1 *)|(* subgoal 2 *)]
     end].

Tactic Notation "iSplitL" := iSplitR "".
Tactic Notation "iSplitR" := iSplitL "".

Local Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_and_destruct with H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iAndDestruct:" H "not found"
    |pm_reduce; iSolveTC ||
     let P :=
       lazymatch goal with
       | |- IntoSep ?P _ _ => P
       | |- IntoAnd _ ?P _ _ => P
       end in
     fail "iAndDestruct: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H1 := pretty_ident H1 in
         let H2 := pretty_ident H2 in
         fail "iAndDestruct:" H1 "or" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

Local Tactic Notation "iAndDestructChoice" constr(H) "as" constr(d) constr(H') :=
  eapply tac_and_destruct_choice with H _ d H' _ _ _;
    [pm_reflexivity || fail "iAndDestructChoice:" H "not found"
    |pm_reduce; iSolveTC ||
     let P := match goal with |- TCOr (IntoAnd _ ?P _ _) _ => P end in
     fail "iAndDestructChoice: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iAndDestructChoice:" H' "not fresh"
     | _ => idtac (* subgoal *)
     end].

(** * Existential *)
Tactic Notation "iExists" uconstr(x1) :=
  iStartProof;
  eapply tac_exist;
    [iSolveTC ||
     let P := match goal with |- FromExist ?P _ => P end in
     fail "iExists:" P "not an existential"
    |pm_prettify; eexists x1
     (* subgoal *) ].

Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) :=
  iExists x1; iExists x2.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) :=
  iExists x1; iExists x2, x3.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) :=
  iExists x1; iExists x2, x3, x4.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) :=
  iExists x1; iExists x2, x3, x4, x5.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) :=
  iExists x1; iExists x2, x3, x4, x5, x6.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7.
Tactic Notation "iExists" uconstr(x1) "," uconstr(x2) "," uconstr(x3) ","
    uconstr(x4) "," uconstr(x5) "," uconstr(x6) "," uconstr(x7) ","
    uconstr(x8) :=
  iExists x1; iExists x2, x3, x4, x5, x6, x7, x8.

Local Tactic Notation "iExistDestruct" constr(H)
    "as" simple_intropattern(x) constr(Hx) :=
  eapply tac_exist_destruct with H _ Hx _ _ _; (* (i:=H) (j:=Hx) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistDestruct:" H "not found"
    |iSolveTC ||
     let P := match goal with |- IntoExist ?P _ _ => P end in
     fail "iExistDestruct: cannot destruct" P|];
    let name := lazymatch goal with
                | |- let _ := (λ name, _) in _ => name
                end in
    intros _;
    let y := fresh name in
    intros y; pm_reduce;
    match goal with
    | |- False =>
      let Hx := pretty_ident Hx in
      fail "iExistDestruct:" Hx "not fresh"
    | _ => revert y; intros x (* subgoal *)
    end.

(** * Modality introduction *)
Tactic Notation "iModIntro" uconstr(sel) :=
  iStartProof;
  notypeclasses refine (tac_modal_intro _ _ sel _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [iSolveTC ||
     fail "iModIntro: the goal is not a modality"
    |iSolveTC ||
     let s := lazymatch goal with |- IntoModalIntuitionisticEnv _ _ _ ?s => s end in
     lazymatch eval hnf in s with
     | MIEnvForall ?C => fail "iModIntro: intuitionistic context does not satisfy" C
     | MIEnvIsEmpty => fail "iModIntro: intuitionistic context is non-empty"
     end
    |iSolveTC ||
     let s := lazymatch goal with |- IntoModalSpatialEnv _ _ _ ?s _ => s end in
     lazymatch eval hnf in s with
     | MIEnvForall ?C => fail "iModIntro: spatial context does not satisfy" C
     | MIEnvIsEmpty => fail "iModIntro: spatial context is non-empty"
     end
    |pm_reduce; iSolveTC ||
     fail "iModIntro: cannot filter spatial context when goal is not absorbing"
    |iSolveSideCondition
    |pm_prettify (* reduce redexes created by instantiation *)
     (* subgoal *) ].
Tactic Notation "iModIntro" := iModIntro _.

(** DEPRECATED *)
#[deprecated(note = "Use iModIntro instead")]
Tactic Notation "iAlways" := iModIntro.

(** * Later *)
Tactic Notation "iNext" open_constr(n) := iModIntro (▷^n _)%I.
Tactic Notation "iNext" := iModIntro (▷^_ _)%I.

(** * Update modality *)
Tactic Notation "iModCore" constr(H) :=
  eapply tac_modal_elim with H _ _ _ _ _ _;
    [pm_reflexivity || fail "iMod:" H "not found"
    |iSolveTC ||
     let P := match goal with |- ElimModal _ _ _ ?P _ _ _ => P end in
     let Q := match goal with |- ElimModal _ _ _ _ _ ?Q _ => Q end in
     fail "iMod: cannot eliminate modality" P "in" Q
    |iSolveSideCondition
    |pm_reduce; pm_prettify(* subgoal *)].

(** * Basic destruct tactic *)

(** [pat0] is the unparsed pattern, and is only used in error messages *)
Local Ltac iDestructHypGo Hz pat0 pat :=
  lazymatch pat with
  | IFresh =>
     lazymatch Hz with
     | IAnon _ => idtac
     | INamed ?Hz => let Hz' := iFresh in iRename Hz into Hz'
     end
  | IDrop => iClearHyp Hz
  | IFrame => iFrameHyp Hz
  | IIdent ?y => iRename Hz into y
  | IList [[]] => iExFalso; iExact Hz

  (* conjunctive patterns like [H1 H2] *)
  | IList [[?pat1; IDrop]] =>
     iAndDestructChoice Hz as Left Hz;
     iDestructHypGo Hz pat0 pat1
  | IList [[IDrop; ?pat2]] =>
     iAndDestructChoice Hz as Right Hz;
     iDestructHypGo Hz pat0 pat2
  (* [% ...] is always interpreted as an existential; there are [IntoExist]
  instances in place to handle conjunctions with a pure left-hand side this way
  as well. *)
  | IList [[IPure IGallinaAnon; ?pat2]] =>
     iExistDestruct Hz as ? Hz; iDestructHypGo Hz pat0 pat2
  | IList [[IPure (IGallinaNamed ?s); ?pat2]] =>
     let x := fresh in
     iExistDestruct Hz as x Hz;
     rename_by_string x s;
     iDestructHypGo Hz pat0 pat2
  | IList [[?pat1; ?pat2]] =>
     let Hy := iFresh in iAndDestruct Hz as Hz Hy;
     iDestructHypGo Hz pat0 pat1; iDestructHypGo Hy pat0 pat2
  | IList [_ :: _ :: _] => fail "iDestruct:" pat0 "has too many conjuncts"
  | IList [[_]] => fail "iDestruct:" pat0 "has just a single conjunct"

  (* disjunctive patterns like [H1|H2] *)
  | IList [[?pat1];[?pat2]] =>
     iOrDestruct Hz as Hz Hz;
     [iDestructHypGo Hz pat0 pat1|iDestructHypGo Hz pat0 pat2]
  (* this matches a list of three or more disjunctions [H1|H2|H3] *)
  | IList (_ :: _ :: _ :: _) => fail "iDestruct:" pat0 "has too many disjuncts"
  (* the above patterns don't match [H1 H2|H3] *)
  | IList [_;_] => fail "iDestruct: in" pat0 "a disjunct has multiple patterns"

  | IPure IGallinaAnon => iPure Hz as ?
  | IPure (IGallinaNamed ?s) =>
     let x := fresh in
     iPure Hz as x;
     rename_by_string x s
  | IRewrite Right => iPure Hz as ->
  | IRewrite Left => iPure Hz as <-
  | IIntuitionistic ?pat => iIntuitionistic Hz; iDestructHypGo Hz pat0 pat
  | ISpatial ?pat => iSpatial Hz; iDestructHypGo Hz pat0 pat
  | IModalElim ?pat => iModCore Hz; iDestructHypGo Hz pat0 pat
  | _ => fail "iDestruct:" pat0 "is not supported due to" pat
  end.
Local Ltac iDestructHypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify (* post-tactic prettification *)
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ISimpl :: ?pats => simpl; iDestructHypFindPat Hgo pat found pats
  | IClear ?H :: ?pats => iClear H; iDestructHypFindPat Hgo pat found pats
  | IClearFrame ?H :: ?pats => iFrame H; iDestructHypFindPat Hgo pat found pats
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => iDestructHypGo Hgo pat pat1; iDestructHypFindPat Hgo pat true pats
     | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
     end
  end.
Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
  let pats := intro_pat.parse pat in
  iDestructHypFindPat H pat false pats.

Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as @ pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "iDestructHyp" constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  iExistDestruct H as x1 H; iDestructHyp H as ( x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

(** * Combinining hypotheses *)
Tactic Notation "iCombine" constr(Hs) "as" constr(pat) :=
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let H := iFresh in
  let Δ := iGetCtx in
  eapply tac_combine with _ _ Hs _ _ H _;
    [pm_reflexivity ||
     let Hs := iMissingHypsCore Δ Hs in
     fail "iCombine: hypotheses" Hs "not found"
    |iSolveTC
    |pm_reflexivity ||
     let H := pretty_ident H in
     fail "iCombine:" H "not fresh"
    |iDestructHyp H as pat].

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(pat) :=
  iCombine [H1;H2] as pat.

(** * Introduction tactic *)
Ltac iIntros_go pats startproof :=
  lazymatch pats with
  | [] =>
    lazymatch startproof with
    | true => iStartProof
    | false => idtac
    end
  (* Optimizations to avoid generating fresh names *)
  | IPure (IGallinaNamed ?s) :: ?pats =>
     let i := fresh in
     iIntro (i);
     rename_by_string i s;
     iIntros_go pats startproof
  | IPure IGallinaAnon :: ?pats => iIntro (?); iIntros_go pats startproof
  | IIntuitionistic (IIdent ?H) :: ?pats => iIntro #H; iIntros_go pats false
  | IDrop :: ?pats => iIntro _; iIntros_go pats startproof
  | IIdent ?H :: ?pats => iIntro H; iIntros_go pats startproof
  (* Introduction patterns that can only occur at the top-level *)
  | IPureIntro :: ?pats => iPureIntro; iIntros_go pats false
  | IModalIntro :: ?pats => iModIntro; iIntros_go pats false
  | IForall :: ?pats => repeat iIntroForall; iIntros_go pats startproof
  | IAll :: ?pats => repeat (iIntroForall || iIntro); iIntros_go pats startproof
  (* Clearing and simplifying introduction patterns *)
  | ISimpl :: ?pats => simpl; iIntros_go pats startproof
  | IClear ?H :: ?pats => iClear H; iIntros_go pats false
  | IClearFrame ?H :: ?pats => iFrame H; iIntros_go pats false
  | IDone :: ?pats => try done; iIntros_go pats startproof
  (* Introduction + destruct *)
  | IIntuitionistic ?pat :: ?pats =>
     let H := iFresh in iIntro #H; iDestructHyp H as pat; iIntros_go pats false
  | ?pat :: ?pats =>
     let H := iFresh in iIntro H; iDestructHyp H as pat; iIntros_go pats false
  end.
Tactic Notation "iIntros" constr(pat) :=
  let pats := intro_pat.parse pat in iIntros_go pats true.
Tactic Notation "iIntros" := iIntros [IAll].

Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" :=
  iIntro ( x1 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" :=
  iIntros ( x1 ); iIntro ( x2 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" :=
  iIntros ( x1 x2 ); iIntro ( x3 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) ")" :=
  iIntros ( x1 x2 x3 ); iIntro ( x4 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5) ")" :=
  iIntros ( x1 x2 x3 x4 ); iIntro ( x5 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) ")" :=
  iIntros ( x1 x2 x3 x4 x5 ); iIntro ( x6 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 ); iIntro ( x7 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntro ( x8 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntro ( x9 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntro ( x10 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntro ( x11 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntro ( x12 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) simple_intropattern(x13) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntro ( x13 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); iIntro ( x14 ).
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
    simple_intropattern(x15) ")" :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ); iIntro ( x15 ).

Tactic Notation "iIntros" "(" simple_intropattern(x1) ")" constr(p) :=
  iIntros ( x1 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    ")" constr(p) :=
  iIntros ( x1 x2 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" constr(p) :=
  iIntros ( x1 x2 x3 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) simple_intropattern(x13) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
    ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ); iIntros p.
Tactic Notation "iIntros" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) simple_intropattern(x5)
    simple_intropattern(x6) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) simple_intropattern(x11)
    simple_intropattern(x12) simple_intropattern(x13) simple_intropattern(x14)
    simple_intropattern(x15) ")" constr(p) :=
  iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ); iIntros p.

Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1) ")" :=
  iIntros p; iIntros ( x1 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" :=
  iIntros p; iIntros ( x1 x2 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" :=
  iIntros p; iIntros ( x1 x2 x3 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) simple_intropattern(x13) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) simple_intropattern(x13)
    simple_intropattern(x14) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ).
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) simple_intropattern(x13)
    simple_intropattern(x14) simple_intropattern(x15) ")" :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ).

Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1) ")" constr(p2) :=
  iIntros p; iIntros ( x1 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) simple_intropattern(x13)
    ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) simple_intropattern(x13)
    simple_intropattern(x14) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ); iIntros p2.
Tactic Notation "iIntros" constr(p) "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) simple_intropattern(x12) simple_intropattern(x13)
    simple_intropattern(x14) simple_intropattern(x15) ")" constr(p2) :=
  iIntros p; iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 ); iIntros p2.

(* Used for generalization in iInduction and iLöb *)
Ltac iRevertIntros_go Hs tac :=
  lazymatch Hs with
  | [] => tac
  | ESelPure :: ?Hs => fail "iRevertIntros: % not supported"
  | ESelIdent ?p ?H :: ?Hs => iRevertHyp H; iRevertIntros_go Hs tac; iIntro H as p
  end.

Tactic Notation "iRevertIntros" constr(Hs) "with" tactic3(tac) :=
  try iStartProof; let Hs := iElaborateSelPat Hs in iRevertIntros_go Hs tac.

Tactic Notation "iRevertIntros" "(" ident(x1) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1); tac; iIntros (x1)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ")" constr(Hs)
    "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2); tac; iIntros (x1 x2)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs)
    "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3); tac; iIntros (x1 x2 x3)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4); tac; iIntros (x1 x2 x3 x4)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5); tac; iIntros (x1 x2 x3 x4 x5)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6);
    tac; iIntros (x1 x2 x3 x4 x5 x6)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")" constr(Hs)
    "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ")" constr(Hs)
    "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ")"
    constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)).
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ident(x15) ")" constr(Hs) "with" tactic3(tac):=
  iRevertIntros Hs with (iRevert (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x14);
    tac; iIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)).

Tactic Notation "iRevertIntros" "with" tactic3(tac) :=
  iRevertIntros "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ")" "with" tactic3(tac):=
  iRevertIntros (x1) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ")"
    "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")"
    "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ")"
    "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11) ")"
    "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with tac.
Tactic Notation "iRevertIntros" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ident(x15) ")" "with" tactic3(tac):=
  iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with tac.

(** * Destruct and PoseProof tactics *)
(** The tactics [iDestruct] and [iPoseProof] are similar, but there are some
subtle differences:

1. The [iDestruct] tactic can be called with a natural number [n] instead of a
   hypothesis/lemma, i.e., [iDestruct n as ...]. This introduces [n] hypotheses,
   and then calls [iDestruct] on the last introduced hypothesis. The
   [iPoseProof] tactic does not support this feature.
2. When the argument [lem] of [iDestruct lem as ...] is a proof mode identifier
   (instead of a proof mode term, i.e., no quantifiers or wands/implications are
   eliminated), then the original hypothesis will always be removed. For
   example, calling [iDestruct "H" as ...] on ["H" : P ∨ Q] will remove ["H"].
   Conversely, [iPoseProof] always tries to keep the hypothesis. For example,
   calling [iPoseProof "H" as ...] on ["H" : P ∨ Q] will keep ["H"] if it
   resides in the intuitionistic context.

These differences are also present in Coq's [destruct] and [pose proof] tactics.
However, Coq's [destruct lem as ...] is more eager on removing the original
hypothesis, it might also remove the original hypothesis if [lem] is not an
identifier, but an applied term. For example, calling [destruct (H HP) as ...]
on [H : P → Q] and [HP : P] will remove [H]. The [iDestruct] does not do this
because it could lead to information loss if [H] resides in the intuitionistic
context and [HP] resides in the spatial context. *)
Tactic Notation "iDestructCore" open_constr(lem) "as" constr(p) tactic3(tac) :=
  let intro_destruct n :=
    let rec go n' :=
      lazymatch n' with
      | 0 => fail "iDestruct: cannot introduce" n "hypotheses"
      | 1 => repeat iIntroForall; let H := iFresh in iIntro H; tac H
      | S ?n' => repeat iIntroForall; let H := iFresh in iIntro H; go n'
      end in
    intros; go n in
  lazymatch type of lem with
  | nat => intro_destruct lem
  | Z =>
     (** This case is used to make the tactic work in [Z_scope]. It would be
     better if we could bind tactic notation arguments to notation scopes, but
     that is not supported by Ltac. *)
     let n := eval compute in (Z.to_nat lem) in intro_destruct n
  | ident => tac lem
  | string => tac constr:(INamed lem)
  | _ => iPoseProofCore lem as p tac
  end.

Tactic Notation "iDestruct" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat).
Tactic Notation "iDestruct" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  iDestructCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat).

Tactic Notation "iDestruct" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as true (fun H => iPure H as pat).

Tactic Notation "iDestruct" "select" open_constr(pat) "as" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 x6 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x7) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x7) simple_intropattern(x8)
    ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "%" simple_intropattern(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as % ipat).

Tactic Notation "iPoseProof" open_constr(lem) "as" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat).

(** * Induction *)
(* An invocation of [iInduction (x) as pat IH forall (x1...xn) Hs] will
result in the following actions:

- Revert the proofmode hypotheses [Hs]
- Revert all remaining spatial hypotheses and the remaining intuitionistic
  hypotheses containing the induction variable [x]
- Revert the pure hypotheses [x1..xn]

- Actuall perform induction

- Introduce thee pure hypotheses [x1..xn]
- Introduce the spatial hypotheses and intuitionistic hypotheses involving [x]
- Introduce the proofmode hypotheses [Hs]
*)
Tactic Notation "iInductionCore" tactic3(tac) "as" constr(IH) :=
  let rec fix_ihs rev_tac :=
    lazymatch goal with
    | H : context [envs_entails _ _] |- _ =>
       eapply (tac_revert_ih _ _ _ H _);
         [pm_reflexivity
          || fail "iInduction: spatial context not empty, this should not happen"
         |clear H];
       fix_ihs ltac:(fun j =>
         let IH' := eval vm_compute in
           match j with 0%N => IH | _ => IH +:+ pretty j end in
         iIntros [IIntuitionistic (IIdent IH')];
         let j := eval vm_compute in (1 + j)%N in
         rev_tac j)
    | _ => rev_tac 0%N
    end in
  tac; fix_ihs ltac:(fun _ => idtac).

Ltac iHypsContaining x :=
  let rec go Γ x Hs :=
    lazymatch Γ with
    | Enil => constr:(Hs)
    | Esnoc ?Γ ?H ?Q =>
       match Q with
       | context [x] => go Γ x (H :: Hs)
       | _ => go Γ x Hs
       end
     end in
  let Γp := lazymatch goal with |- envs_entails (Envs ?Γp _ _) _ => Γp end in
  let Γs := lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ => Γs end in
  let Hs := go Γp x (@nil ident) in go Γs x Hs.

Tactic Notation "iInductionRevert" constr(x) constr(Hs) "with" tactic3(tac) :=
  iRevertIntros Hs with (
    iRevertIntros "∗" with (
      idtac;
      let Hsx := iHypsContaining x in
      iRevertIntros Hsx with tac
    )
  ).

Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) :=
  iInductionRevert x "" with (iInductionCore (induction x as pat) as IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ")" :=
  iInductionRevert x "" with (
    iRevertIntros (x1) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident(x9) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ident(x13) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ident(x13)
    ident(x14) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ident(x13)
    ident(x14) ident(x15) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with
      (iInductionCore (induction x as pat) as IH)).

Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" constr(Hs) :=
  iInductionRevert x Hs with (iInductionCore (induction x as pat) as IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ")"
    constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5) "" with (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ")"
    constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident(x9) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ident(x13)
    ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ident(x13)
    ident(x14) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with
      (iInductionCore (induction x as pat) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6)
    ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ident(x12) ident(x13)
    ident(x14) ident(x15) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with
      (iInductionCore (induction x as pat) as IH)).

Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) :=
  iInductionRevert x "" with (iInductionCore (induction x as pat using u) as IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ")" :=
  iInductionRevert x "" with (
    iRevertIntros (x1) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ident(x15) ")" :=
  iInductionRevert x "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with
      (iInductionCore (induction x as pat using u) as IH)).

Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" constr(Hs) :=
  iInductionRevert x Hs with (iInductionCore (induction x as pat using u) as IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5) "" with (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11) ")"
    constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with
      (iInductionCore (induction x as pat using u) as IH)).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ident(x1) ident(x2) ident(x3) ident(x4)
    ident(x5) ident(x6) ident(x7) ident(x8) ident (x9) ident(x10) ident(x11)
    ident(x12) ident(x13) ident(x14) ident(x15) ")" constr(Hs) :=
  iInductionRevert x Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with
      (iInductionCore (induction x as pat using u) as IH)).

(** * Löb Induction *)
Tactic Notation "iLöbCore" "as" constr (IH) :=
  iStartProof;
  (* apply is sometimes confused wrt. canonical structures search.
     refine should use the other unification algorithm, which should
     not have this issue. *)
  notypeclasses refine (tac_löb _ IH _ _ _ _);
    [iSolveTC || fail "iLöb: no 'BiLöb' instance found"
    |reflexivity || fail "iLöb: spatial context not empty; this should not happen, please report a bug"
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let IH := pretty_ident IH in
       fail "iLöb:" IH "not fresh"
     | _ => idtac
     end].

Tactic Notation "iLöbRevert" constr(Hs) "with" tactic3(tac) :=
  iRevertIntros Hs with (
    iRevertIntros "∗" with tac
  ).

Tactic Notation "iLöb" "as" constr (IH) :=
  iLöbRevert "" with (iLöbCore as IH).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ")" :=
  iLöbRevert "" with (iRevertIntros (x1) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2 x3) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2 x3 x4) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2 x3 x4 x5) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2 x3 x4 x5 x6) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ")" :=
  iLöbRevert "" with (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")" :=
  iLöbRevert "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ")" :=
  iLöbRevert "" with
     (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ")" :=
  iLöbRevert "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ")" :=
  iLöbRevert "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ident(x13) ")" :=
  iLöbRevert "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ident(x13) ident(x14) ")" :=
  iLöbRevert "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ident(x13) ident(x14) ident(x15) ")" :=
  iLöbRevert "" with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with (iLöbCore as IH)).

Tactic Notation "iLöb" "as" constr (IH) "forall" constr(Hs) :=
  iLöbRevert Hs with (iLöbCore as IH).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2) ")"
    constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3 x4) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3 x4 x5) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3 x4 x5 x6) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3 x4 x5 x6 x7) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ")" constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9) ")"
    constr(Hs) :=
  iLöbRevert Hs with (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ")" constr(Hs) :=
  iLöbRevert Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ")" constr(Hs) :=
  iLöbRevert Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ")" constr(Hs) :=
  iLöbRevert Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ident(x13) ")" constr(Hs) :=
  iLöbRevert Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ident(x13) ident(x14) ")" constr(Hs) :=
  iLöbRevert Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) "" with (iLöbCore as IH)).
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ident(x1) ident(x2)
    ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) ident(x9)
    ident(x10) ident(x11) ident(x12) ident(x13) ident(x14) ident(x15) ")" constr(Hs) :=
  iLöbRevert Hs with
    (iRevertIntros (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) "" with (iLöbCore as IH)).

(** * Assert *)
(* The argument [p] denotes whether [Q] is persistent. It can either be a
Boolean or an introduction pattern, which will be coerced into [true] if it
only contains [#] or [%] patterns at the top-level, and [false] otherwise. *)
Tactic Notation "iAssertCore" open_constr(Q)
    "with" constr(Hs) "as" constr(p) tactic3(tac) :=
  iStartProof;
  let pats := spec_pat.parse Hs in
  lazymatch pats with
  | [_] => idtac
  | _ => fail "iAssert: exactly one specialization pattern should be given"
  end;
  let H := iFresh in
  eapply tac_assert with H Q;
  [pm_reduce;
   iSpecializeCore H with hnil pats as p; [..|tac H]].

Tactic Notation "iAssertCore" open_constr(Q) "as" constr(p) tactic3(tac) :=
  let p := intro_pat_intuitionistic p in
  lazymatch p with
  | true => iAssertCore Q with "[#]" as p tac
  | false => iAssertCore Q with "[]" as p tac
  end.

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1) pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1 x2) pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1 x2 x3) pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => iDestructHyp H as (x1 x2 x3 x4) pat).

Tactic Notation "iAssert" open_constr(Q) "as" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1) pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1 x2) pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1 x2 x3) pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)
    simple_intropattern(x4) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => iDestructHyp H as (x1 x2 x3 x4) pat).

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs)
    "as" "%" simple_intropattern(pat) :=
  iAssertCore Q with Hs as true (fun H => iPure H as pat).
Tactic Notation "iAssert" open_constr(Q) "as" "%" simple_intropattern(pat) :=
  iAssert Q with "[-]" as %pat.

(** * Rewrite *)
Local Ltac iRewriteFindPred :=
  match goal with
  | |- _ ⊣⊢ ?Φ ?x =>
     generalize x;
     match goal with |- (∀ y, @?Ψ y ⊣⊢ _) => unify Φ Ψ; reflexivity end
  end.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite _ Heq _ _ lr);
      [pm_reflexivity ||
       let Heq := pretty_ident Heq in
       fail "iRewrite:" Heq "not found"
      |iSolveTC ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity|pm_prettify; iClearHyp Heq]).

Tactic Notation "iRewrite" open_constr(lem) := iRewriteCore Right lem.
Tactic Notation "iRewrite" "-" open_constr(lem) := iRewriteCore Left lem.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) "in" constr(H) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
      [pm_reflexivity ||
       let Heq := pretty_ident Heq in
       fail "iRewrite:" Heq "not found"
      |pm_reflexivity ||
       let H := pretty_ident H in
       fail "iRewrite:" H "not found"
      |iSolveTC ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity
      |pm_reduce; pm_prettify; iClearHyp Heq]).

Tactic Notation "iRewrite" open_constr(lem) "in" constr(H) :=
  iRewriteCore Right lem in H.
Tactic Notation "iRewrite" "-" open_constr(lem) "in" constr(H) :=
  iRewriteCore Left lem in H.

Ltac iSimplifyEq := repeat (
  iMatchHyp (fun H P => match P with ⌜_ = _⌝%I => iDestruct H as %? end)
  || simplify_eq/=).

(** * Update modality *)
Tactic Notation "iMod" open_constr(lem) :=
  iDestructCore lem as false (fun H => iModCore H).
Tactic Notation "iMod" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as ( x1 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H; last iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructCore lem as false (fun H =>
    iModCore H; last iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Tactic Notation "iMod" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as false (fun H => iModCore H; iPure H as pat).

(** * Invariant *)

(* Finds a hypothesis in the context that is an invariant with
   namespace [N].  To do so, we check whether for each hypothesis
   ["H":P] we can find an instance of [IntoInv P N] *)
Tactic Notation "iAssumptionInv" constr(N) :=
  let rec find Γ i :=
    lazymatch Γ with
    | Esnoc ?Γ ?j ?P' =>
      first [let H := constr:(_: IntoInv P' N) in unify i j|find Γ i]
    end in
  lazymatch goal with
  | |- envs_lookup ?i (Envs ?Γp ?Γs _) = Some _ =>
     first [find Γp i|find Γs i]; pm_reflexivity
  end.

(* The argument [select] is the namespace [N] or hypothesis name ["H"] of the
invariant. *)
Tactic Notation "iInvCore" constr(select) "with" constr(pats) "as" open_constr(Hclose) "in" tactic3(tac) :=
  iStartProof;
  let pats := spec_pat.parse pats in
  lazymatch pats with
  | [_] => idtac
  | _ => fail "iInv: exactly one specialization pattern should be given"
  end;
  let H := iFresh in
  let Pclose_pat :=
    lazymatch Hclose with
    | Some _ => open_constr:(Some _)
    | None => open_constr:(None)
    end in
  lazymatch type of select with
  | string =>
     notypeclasses refine (tac_inv_elim _ select H _ _ _ _ _ Pclose_pat _ _ _ _ _ _);
     [ (by iAssumptionCore) || fail "iInv: invariant" select "not found" |..]
  | ident  =>
     notypeclasses refine (tac_inv_elim _ select H _ _ _ _ _ Pclose_pat _ _ _ _ _ _);
     [ (by iAssumptionCore) || fail "iInv: invariant" select "not found" |..]
  | namespace =>
     notypeclasses refine (tac_inv_elim _ _ H _ _ _ _ _ Pclose_pat _ _ _ _ _ _);
     [ (by iAssumptionInv select) || fail "iInv: invariant" select "not found" |..]
  | _ => fail "iInv: selector" select "is not of the right type "
  end;
    [iSolveTC ||
     let I := match goal with |- ElimInv _ ?I  _ _ _ _ _ => I end in
     fail "iInv: cannot eliminate invariant" I
    |iSolveSideCondition
    |let R := fresh in intros R; pm_reduce;
     (* Now we are left proving [envs_entails Δ'' R]. *)
     iSpecializePat H pats; last (
       iApplyHyp H; clear R; pm_reduce;
       (* Now the goal is
          [∀ x, Pout x -∗ pm_option_fun Pclose x -∗? Q' x],
          reduced because we can rely on Pclose being a constructor. *)
       let x := fresh in
       iIntros (x);
       iIntro H; (* H was spatial, so it's gone due to the apply and we can reuse the name *)
       lazymatch Hclose with
       | Some ?Hcl => iIntros Hcl
       | None => idtac
       end;
       tac x H
    )].

(* Without closing view shift *)
Tactic Notation "iInvCore" constr(N) "with" constr(pats) "in" tactic3(tac) :=
  iInvCore N with pats as (@None string) in ltac:(tac).
(* Without pattern *)
Tactic Notation "iInvCore" constr(N) "as" constr(Hclose) "in" tactic3(tac) :=
  iInvCore N with "[$]" as Hclose in ltac:(tac).
(* Without both *)
Tactic Notation "iInvCore" constr(N) "in" tactic3(tac) :=
  iInvCore N with "[$]" as (@None string) in ltac:(tac).

(* With everything *)
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H => iDestructHyp H as pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H => iDestructHyp H as (x1) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H => iDestructHyp H as (x1 x2) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H => iDestructHyp H as (x1 x2 x3) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H => iDestructHyp H as (x1 x2 x3 x4) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H =>
    iDestructHyp H as (x1 x2 x3 x4 x5) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H =>
    iDestructHyp H as (x1 x2 x3 x4 x5 x6) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H =>
    iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H =>
    iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H =>
    iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9) pat).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in (fun x H =>
    iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) pat).

(* Without closing view shift *)
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as pat
                | _ => fail "Missing intro pattern for accessor variable"
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1) pat
                | _ => revert x; intros x1; iDestructHyp H as      pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")"
    constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8 x9) pat
                end).
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  iInvCore N with Hs in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8 x9 x10) pat
                end).

(* Without pattern *)
Tactic Notation "iInv" constr(N) "as" constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as pat
                | _ => fail "Missing intro pattern for accessor variable"
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1) pat
                | _ => revert x; intros x1; iDestructHyp H as      pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8 x9) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8 x9 x10) pat
                end).

(* Without both *)
Tactic Notation "iInv" constr(N) "as" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as pat
                | _ => fail "Missing intro pattern for accessor variable"
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1) pat
                | _ => revert x; intros x1; iDestructHyp H as      pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2)  pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3)  pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4)  pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5)  pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8 x9) pat
                end).
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  iInvCore N in
    (fun x H => lazymatch type of x with
                | unit => destruct x as []; iDestructHyp H as (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) pat
                | _ => revert x; intros x1; iDestructHyp H as (   x2 x3 x4 x5 x6 x7 x8 x9 x10) pat
                end).

(** Miscellaneous *)
Tactic Notation "iAccu" :=
  iStartProof; eapply tac_accu; [pm_reflexivity || fail "iAccu: not an evar"].

(** Automation *)
Global Hint Extern 0 (_ ⊢ _) => iStartProof : core.
Global Hint Extern 0 (⊢ _) => iStartProof : core.

(* Make sure that [by] and [done] solve trivial things in proof mode.
[iPureIntro] invokes [FromPure], so adding [FromPure] instances can help improve
what [done] can do. *)
Global Hint Extern 0 (envs_entails _ _) => iPureIntro; try done : core.
Global Hint Extern 0 (envs_entails _ ?Q) =>
  first [is_evar Q; fail 1|iAssumption] : core.
Global Hint Extern 0 (envs_entails _ emp) => iEmpIntro : core.

(* TODO: look for a more principled way of adding trivial hints like those
below; see the discussion in !75 for further details. *)
Global Hint Extern 0 (envs_entails _ (_ ≡ _)) =>
  rewrite envs_entails_eq; apply internal_eq_refl : core.
Global Hint Extern 0 (envs_entails _ (big_opL _ _ _)) =>
  rewrite envs_entails_eq; apply (big_sepL_nil' _) : core.
Global Hint Extern 0 (envs_entails _ (big_sepL2 _ _ _)) =>
  rewrite envs_entails_eq; apply (big_sepL2_nil' _) : core.
Global Hint Extern 0 (envs_entails _ (big_opM _ _ _)) =>
  rewrite envs_entails_eq; apply (big_sepM_empty' _) : core.
Global Hint Extern 0 (envs_entails _ (big_sepM2 _ _ _)) =>
  rewrite envs_entails_eq; apply (big_sepM2_empty' _) : core.
Global Hint Extern 0 (envs_entails _ (big_opS _ _ _)) =>
  rewrite envs_entails_eq; apply (big_sepS_empty' _) : core.
Global Hint Extern 0 (envs_entails _ (big_opMS _ _ _)) =>
  rewrite envs_entails_eq; apply (big_sepMS_empty' _) : core.

(* These introduce as much as possible at once, for better performance. *)
Global Hint Extern 0 (envs_entails _ (∀ _, _)) => iIntros : core.
Global Hint Extern 0 (envs_entails _ (_ → _)) => iIntros : core.
Global Hint Extern 0 (envs_entails _ (_ -∗ _)) => iIntros : core.
(* Multi-intro doesn't work for custom binders. *)
Global Hint Extern 0 (envs_entails _ (∀.. _, _)) => iIntros (?) : core.

Global Hint Extern 1 (envs_entails _ (_ ∧ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (_ ∗ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (_ ∗-∗ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (▷ _)) => iNext : core.
Global Hint Extern 1 (envs_entails _ (■ _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (<pers> _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (<affine> _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (□ _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (∃ _, _)) => iExists _ : core.
Global Hint Extern 1 (envs_entails _ (∃.. _, _)) => iExists _ : core.
Global Hint Extern 1 (envs_entails _ (◇ _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (_ ∨ _)) => iLeft : core.
Global Hint Extern 1 (envs_entails _ (_ ∨ _)) => iRight : core.
Global Hint Extern 1 (envs_entails _ (|==> _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (<absorb> _)) => iModIntro : core.
Global Hint Extern 2 (envs_entails _ (|={_}=> _)) => iModIntro : core.

Global Hint Extern 2 (envs_entails _ (_ ∗ _)) => progress iFrame : iFrame.
