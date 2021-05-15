From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.

Section stuff.

Class TPCM (M : Type) `{EqDecision M} :=
{
  valid : M -> Prop ;
  dot : M -> M -> M ;
  mov : M -> M -> Prop ;
  unit : M ;
  
  valid_monotonic : forall x y , valid (dot x y) -> valid x ;
  unit_valid : valid unit ;
  unit_dot : forall x , dot x unit = x ;
  comm : forall x y , dot x y = dot y x ;
  assoc : forall x y z , dot x (dot y z) = dot (dot x y) z ;
  reflex : forall x , mov x x ;
  trans : forall x y z , mov x y -> mov y z -> mov x z ;
  mov_monotonic : forall x y z ,
      mov x y -> valid (dot x z) -> valid (dot y z) /\ mov (dot x z) (dot y z)
}.

Definition tpcm_le `{TPCM M} (a : M) (b : M) := ∃ c , dot a c = b.

Record Refinement R M `{ TPCM R , TPCM M } :=
{
  (*rel : R -> M -> bool ;
  
  rel_valid : forall r m , rel r m -> valid r /\ valid m ;
  rel_unit : rel unit unit ;
  mov_refines : forall b b' q , mov b b' -> rel b q -> exists q' , rel b' q' /\ mov q q' ;
  rel_self : forall b q q' , rel b q -> rel b q' -> mov q q' ;*)
  
  rel : R -> option M ;
  rel_valid_left : forall r m , rel r = Some m -> valid r ;
  rel_valid_right : forall r m , rel r = Some m -> valid m ;
  rel_unit : rel unit = Some unit ;
  mov_refines : forall b b' q , mov b b' -> rel b = Some q -> exists q' , rel b' = Some q' /\ mov q q' ;
}.

Context `{TPCM M}.

Context `{EqDecision RefinementIndex}.
Variables refinement_of_index : RefinementIndex -> Refinement M M.

Definition L := nat.
      
Inductive Loc :=
  | LBase : L -> Loc
  | LExt : L -> RefinementIndex -> Loc -> Loc
 .

Instance eqloc : EqDecision Loc. solve_decision. Defined.

Instance countableloc : Countable Loc. Admitted.

Definition Lifetime := gset nat.
Definition lifetime_intersect (l: Lifetime) (m: Lifetime) := gset_union l m.
Definition lifetime_included (l: Lifetime) (m: Lifetime) := subseteq m l.

Instance lifetime_included_dec l m : Decision (lifetime_included l m). unfold lifetime_included. solve_decision. Defined.

(*Lemma fresh_borrow_inst : ∀ (l : Lifetime) , ∃ b , ∀ t, gset_elem_of t l -> t < b.
Proof.
apply set_ind.
 - by intros ?? ->%leibniz_equiv_iff.
 - exists 0. intro. unfold gset_elem_of.
 Abort.*)
 
Inductive BorrowObject : Type :=
  | BorrowO : Lifetime -> Loc -> M -> BorrowObject
.
Instance eqdec_borrow_object : EqDecision BorrowObject. solve_decision. Defined.
Instance countable_borrow_object : Countable BorrowObject. Admitted.

Inductive LifetimeStatus := LSNone | LSActive | LSFail.

Record AllState : Type := {
  active_lifetimes: nat -> LifetimeStatus;
  borrows: BorrowObject -> bool;
  live_objects: Loc -> M;
  reserved_objects: gset BorrowObject;
}.

Record InvState : Type := {
  locs_in_use: gset Loc;
  max_lt_index: nat; 
  
  ltotal : Loc -> M;
  view: Loc -> Lifetime -> M -> Prop ;
}.
  
Instance allstate_equiv : Equiv AllState := λ x y , x = y.

Print merge.
Definition merge_lifetime_status (x: LifetimeStatus) (y: LifetimeStatus) :=
  match x, y with
  | LSNone, m => m
  | LSActive, LSNone => LSActive
  | LSActive, LSActive => LSFail
  | LSActive, LSFail => LSFail
  | LSFail, _ => LSFail
  end.
  
Definition merge_active (x : nat -> LifetimeStatus) (y : nat -> LifetimeStatus) :=
  λ n, merge_lifetime_status (x n) (y n).
  
Definition merge_borrows (x y : BorrowObject -> bool) :=
  λ bo, orb (x bo) (y bo).
  
Definition merge_live_objects (x y : Loc -> M) :=
  λ lo , dot (x lo) (y lo).

Definition merge_reserved_objects (x y : (gset (BorrowObject))) :=
  union x y.

Instance alls_op_instance : Op AllState := λ x y,
  {|
    active_lifetimes := merge_active (active_lifetimes x) (active_lifetimes y);
    borrows := merge_borrows (borrows x) (borrows y);
    live_objects := merge_live_objects (live_objects x) (live_objects y);
    reserved_objects := merge_reserved_objects (reserved_objects x) (reserved_objects y)
  |} .
  
Instance alls_pcore_instance : PCore AllState := λ x,
  Some({|
    active_lifetimes := λ _ , LSNone;
    borrows := borrows x;
    live_objects := λ _ , unit;
    reserved_objects := reserved_objects x
  |}) .
  
Definition Live (s: AllState) (loc: Loc) :=
    live_objects s loc.

Definition borrow_object_has_loc (loc: Loc) (bo: BorrowObject) :=
  match bo with
  BorrowO _ loc1 _ => loc = loc1
  end
.
Definition borrow_object_has_loc_dec loc : ∀ bo, Decision (borrow_object_has_loc loc bo). intro. unfold borrow_object_has_loc. destruct bo. solve_decision. Defined.

Definition borrow_object_has_loc_over_lt
    (loc: Loc) (borrow_lt: Lifetime)
    (reserve_object: BorrowObject) :=
  match reserve_object with
  BorrowO reserve_lt loc1 _ => loc = loc1 /\ lifetime_included borrow_lt reserve_lt
  end
.
Definition borrow_object_has_loc_over_lt_dec loc borrow_lt : ∀ reserve_object ,
    Decision (borrow_object_has_loc_over_lt loc borrow_lt reserve_object).
intro. unfold borrow_object_has_loc_over_lt.
destruct reserve_object. solve_decision.
Defined.

Definition lifetime_included_in_active (lt: Lifetime) (active: nat -> LifetimeStatus) :=
  ∀ n , n ∈ lt -> active n = LSActive.

Definition borrow_object_has_loc_over_active
    (loc: Loc) (active: nat -> LifetimeStatus)
    (reserve_object: BorrowObject) :=
  match reserve_object with
  BorrowO reserve_lt loc1 _ => loc = loc1 /\ lifetime_included_in_active reserve_lt active
  end
.

Definition lifetime_included_in_active_dec lt active :
    Decision (lifetime_included_in_active lt active).
unfold lifetime_included_in_active. Admitted.

Definition borrow_object_has_loc_over_active_dec loc active :
    ∀ reserve_object , Decision (borrow_object_has_loc_over_active loc active reserve_object). 
intro. unfold borrow_object_has_loc_over_active. destruct reserve_object.  Admitted.


Definition ReservedHere (s: AllState) (u: InvState) (loc: Loc) (active: nat -> LifetimeStatus) :=
    set_fold (λ reserveObject m, (match reserveObject with BorrowO _ _ k => dot m k end))
    unit
    (
      set_filter
          (borrow_object_has_loc_over_active loc active)
          (borrow_object_has_loc_over_active_dec loc active)
          (reserved_objects s)
    ).
    
Definition ReservedHereOver (s: AllState) (u: InvState) (loc: Loc) (lt: Lifetime) :=
    set_fold (λ reserveObject m, (match reserveObject with BorrowO _ _ k => dot m k end))
    unit
    (
      set_filter
          (borrow_object_has_loc_over_lt loc lt)
          (borrow_object_has_loc_over_lt_dec loc lt)
          (reserved_objects s)
    ).
    
Definition IsLocExt (l: Loc) (lext: Loc) : Prop :=
  match lext with
  | LBase _ => False
  | LExt _ _ subl => l = subl
  end.
  
Definition is_loc_ext_dec loc : ∀ lext, Decision (IsLocExt loc lext). intro. unfold IsLocExt. destruct lext; solve_decision. Defined.
  
Definition rel_total `{TPCM R, TPCM M} (ref : Refinement R M) (r: R) := match (rel R M ref) r with | Some t => t | None => unit end.

Definition get_ref_idx (loc: Loc) (extloc: Loc) (ile: IsLocExt loc extloc) : RefinementIndex.
unfold IsLocExt in ile. destruct extloc in ile.
  - contradiction.
  - apply r.
Defined.

Definition Project (extloc: Loc) (m: M) : M :=
  match extloc with
  | LBase _ => m (* for totality *)
  | LExt _ ri _ => rel_total (refinement_of_index ri) m
  end
.

Definition fold_over_locs {A}
    (map_fn: Loc -> A)
    (reduce_fn: A -> A -> A)
    (unit_a: A)
    (loc_domain: gset Loc) 
    (base_loc: Loc) : A :=
   set_fold (λ extloc a , reduce_fn a (map_fn extloc))
    unit_a
    (
      set_filter (IsLocExt base_loc) (is_loc_ext_dec base_loc) loc_domain
    ).

Definition FoldProjectTotal (u : InvState) (loc : Loc) :=
  fold_over_locs (λ lext , ltotal u lext) dot unit (locs_in_use u) loc.

Definition Unlive (s: AllState) (u: InvState) (loc: Loc) :=
  dot (ReservedHere s u loc (active_lifetimes s))
      (FoldProjectTotal u loc).
  
Definition UnliveOver (s: AllState) (u: InvState) (loc: Loc) (lt: Lifetime) :=
  dot (ReservedHereOver s u loc lt) (FoldProjectTotal u loc).

Definition inv_loc_total_identity (s : AllState) (u : InvState) (loc: Loc) : Prop :=
  (ltotal u loc) = dot (Live s loc) (Unlive s u loc).

Definition umbrella : M -> (M -> Prop) := tpcm_le.

Definition umbrella_unit : (M -> Prop) := λ _ , True.

Definition intersect_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , a m /\ b m.

Definition conjoin_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , ∃ x y , a x /\ b y /\ dot x y = m.

Definition project_umbrella
    (refinement: Refinement M M) (umbrella : M -> Prop) : (M -> Prop) :=
    λ m , ∃ r t , umbrella r /\ (rel M M refinement r = Some t) /\ tpcm_le t m.
  
Definition ProjectFancy (extloc : Loc) (umbrella : M -> Prop) : (M -> Prop) :=
  match extloc with
  | LBase _ => umbrella (* for totality *)
  | LExt _ ri _ => project_umbrella (refinement_of_index ri) umbrella
  end
.

Definition FoldProjectFancyView (u : InvState) (loc : Loc) (lt : Lifetime) :=
  fold_over_locs (λ lext , view u loc lt) conjoin_umbrella umbrella_unit (locs_in_use u) loc.

Definition inv_loc_lt_view_identity
    (s : AllState) (u : InvState)
    (loc: Loc) (lt: Lifetime) : Prop :=
  (view u loc lt) = conjoin_umbrella
    (umbrella (ReservedHereOver s u loc lt))
    (FoldProjectFancyView u loc lt).
    
Definition inv_loc_view_identity
    (s : AllState) (u : InvState)
    (loc: Loc) : Prop := ∀ lt , inv_loc_lt_view_identity s u loc lt.

Definition view_sat (umbrella : M -> Prop) (m : M) := umbrella m.

Definition inv_loc_lt_view_sat (s: AllState) (u: InvState) (loc: Loc) (lt: Lifetime) :=
  view_sat (view u loc lt) (UnliveOver s u loc lt).
  
Definition inv_loc_view_sat (s: AllState) (u: InvState) (loc: Loc) :=
  ∀ lt , inv_loc_lt_view_sat s u loc lt.
  
Definition inv_loc_valid (u: InvState) (loc: Loc) :=
  valid (ltotal u loc).
  
Definition inv_loc_borrow_sound (s: AllState) (u: InvState) (loc: Loc) :=
  ∀ lt m y , (BorrowO lt loc m) ∈ (reserved_objects s) -> view u loc lt y -> tpcm_le m y.
  
Definition inv_loc (s: AllState) (u: InvState) (loc: Loc) :=
     inv_loc_view_sat s u loc
  /\ inv_loc_view_identity s u loc
  /\ inv_loc_total_identity s u loc
  /\ inv_loc_valid u loc
  /\ inv_loc_borrow_sound s u loc.

Definition inv (s: AllState) (u: InvState) :=
  ∀ l , inv_loc s u l.

Print set_equiv.
Lemma set_filter_eq  fn1 fn2 (fn1_dec : ∀ x , Decision (fn1 x)) (fn2_dec : ∀ x , Decision (fn2 x)) (s : gset Loc) :
    (∀ x , x ∈ s -> fn1 x = fn2 x) ->
    set_filter fn1 fn1_dec s = set_filter fn2 fn2_dec s.
  Proof. intro. apply set_eq. intros. split.
    - rewrite elem_of_filter. rewrite elem_of_filter. intro. destruct H1. rewrite <- H0.
      * split; trivial. * trivial.
    - rewrite elem_of_filter. rewrite elem_of_filter. intro. destruct H1. rewrite H0.
      * split; trivial. * trivial.
Qed.

(*Lemma foldr_ext_2 {A B} (f1 f2 : B → A → A) x1 x2 l : 
  (∀ b a, b ∈ l -> f1 b a = f2 b a) → x1 = x2 → foldr f1 x1 l = foldr f2 x2 l.
Proof. induction l.
    - intros. unfold foldr. trivial.
    - intros. unfold foldr. 
   - unfold foldr. trivial.
   - unfold foldr. *)

Print foldr_permutation.
Lemma set_fold_eq {X: Type} (fn1 fn2 : Loc -> X -> X) (a : X) (s : gset Loc) :
  (∀ x y , y ∈ s -> fn1 y x = fn2 y x) ->
  set_fold fn1 a s = set_fold fn2 a s.
(*Proof. intro. unfold set_fold. unfold "∘". apply foldr_ext; auto. 
  intros. apply H0.*)
  Admitted.

Lemma fold_project_total_on_total_change :
    ∀ (u: InvState) (u': InvState) (loc_changed: Loc) (loc: Loc),
    (∀ r , r <> loc_changed -> ltotal u r = ltotal u' r) ->
    (locs_in_use u) = (locs_in_use u') ->
    not (IsLocExt loc loc_changed) ->
    FoldProjectTotal u loc = FoldProjectTotal u' loc.
Proof.
  intros. unfold FoldProjectTotal. rewrite H1. unfold fold_over_locs.
  apply set_fold_eq. intros. rewrite H0; trivial.
  generalize H3. rewrite elem_of_filter. intro. destruct H4. intro. rewrite H6 in H4. contradiction.
Qed.

(*
Lemma fold_project_fancy_view_on_total_change :
    ∀ (u: InvState) (u': InvState) (loc_changed: Loc) (loc: Loc) (lt: Lifetime),
    (∀ r , r <> loc_changed -> ltotal u r = ltotal u' r) ->
    (locs_in_use u) = (locs_in_use u') ->
    (view u) = (view u') ->
    not (IsLocExt loc loc_changed) ->
    FoldProjectFancyView u loc lt = FoldProjectFancyView u' loc lt.
Proof.
  intros. unfold FoldProjectFancyView. rewrite H1.
  apply set_fold_eq. intros. rewrite H0; trivial.
  generalize H3. rewrite elem_of_filter. intro. destruct H4. intro. rewrite H6 in H4. contradiction.
Qed.*)
  
Lemma inv_loc_view_sat_preserve_total_change :
    ∀ (s: AllState) (u: InvState) (u': InvState) (loc_changed: Loc) (loc: Loc),
    (∀ r , r <> loc_changed -> ltotal u r = ltotal u' r) ->
    locs_in_use u = locs_in_use u' ->
    max_lt_index u = max_lt_index u' ->
    view u = view u' ->
    not (IsLocExt loc loc_changed) ->
    inv_loc_view_sat s u loc ->
    inv_loc_view_sat s u' loc.
Proof.
  intros.
    unfold inv_loc_view_sat in *.
    unfold inv_loc_lt_view_sat in *.
    unfold view_sat in *.
    unfold view in *.
    unfold UnliveOver in *.
    destruct u. destruct u'. simpl in *.
    replace (FoldProjectTotal {| locs_in_use := locs_in_use1; max_lt_index := max_lt_index1; ltotal := ltotal1; view := view1 |} loc) with (FoldProjectTotal {| locs_in_use := locs_in_use0; max_lt_index := max_lt_index0; ltotal := ltotal0; view := view0 |} loc).
      - rewrite <- H3. trivial.
      - apply fold_project_total_on_total_change with (loc_changed := loc_changed).
        + simpl. apply H0; trivial.
        + simpl. trivial.
        + simpl. trivial.
Qed. 

(*Lemma conjoin_umbrella_equiv (a b c : M -> Prop) :
  (∀ x , b x <-> c x) -> (∀ x , conjoin_umbrella a b x <-> conjoin_umbrella a c x).
Proof. intros. unfold conjoin_umbrella. split.
  - intro. destruct H1. destruct H1. exists x0. exists x1. rewrite <- H0. trivial.
  - intro. destruct H1. destruct H1. exists x0. exists x1. rewrite H0. trivial.
Qed.*)
 
Lemma inv_loc_view_identity_on_total_change :
    ∀ (s: AllState) (u: InvState) (u': InvState) (loc: Loc),
    locs_in_use u = locs_in_use u' ->
    max_lt_index u = max_lt_index u' ->
    view u = view u' ->
    inv_loc_view_identity s u loc ->
    inv_loc_view_identity s u' loc.
Proof.
  intros.
    unfold inv_loc_view_identity in *.
    unfold inv_loc_lt_view_identity in *.
    unfold ReservedHereOver in *.
    intros. rewrite <- H2. rewrite H3.
    unfold FoldProjectFancyView.
    rewrite H0. rewrite H2. trivial.
Qed. 
 
Lemma Unlive_on_total_change :
    ∀ (s: AllState) (u: InvState) (u': InvState) (loc_changed: Loc) (loc: Loc),
    (∀ r , r <> loc_changed -> ltotal u r = ltotal u' r) ->
    locs_in_use u = locs_in_use u' ->
    (*view u = view u' ->*)
    not (IsLocExt loc loc_changed) ->
    Unlive s u loc = Unlive s u' loc.
Proof.
  intros.
    unfold Unlive. unfold ReservedHere.
    replace (FoldProjectTotal u loc) with (FoldProjectTotal u' loc); trivial.
    apply fold_project_total_on_total_change with (loc_changed := loc_changed).
     + intros. symmetry. apply H0. trivial.
     + symmetry. trivial.
     + trivial.
Qed.
 
Lemma inv_loc_total_identity_on_total_change :
    ∀ (s: AllState) (u: InvState) (u': InvState) (loc_changed: Loc) (loc: Loc),
    (∀ r , r <> loc_changed -> ltotal u r = ltotal u' r) ->
    locs_in_use u = locs_in_use u' ->
    max_lt_index u = max_lt_index u' ->
    view u = view u' ->
    not (IsLocExt loc loc_changed) ->
    loc <> loc_changed ->
    inv_loc_total_identity s u loc ->
    inv_loc_total_identity s u' loc.
Proof.
  intros.
    unfold inv_loc_total_identity in *.
    unfold Live in *.
    unfold Unlive in *.
    unfold ReservedHere in *.
    replace (FoldProjectTotal u' loc) with (FoldProjectTotal u loc).
      - rewrite <- H6. symmetry. apply H0. trivial.
      - apply fold_project_total_on_total_change with (loc_changed := loc_changed); trivial.
Qed.

Definition update_total_at_loc (s: AllState) (u: InvState) (loc_changed: Loc) :=
  let new_value := (dot (Live s loc_changed) (Unlive s u loc_changed)) in
  {|
    locs_in_use := locs_in_use u;
    max_lt_index := max_lt_index u;
    ltotal := (λ z , if decide (z = loc_changed) then new_value else ltotal u z);
    view := view u;
  |}.

Lemma result_of_mov_is_valid (m: M) (m': M) : mov m m' -> valid m -> valid m'.
Proof. intros. have h := mov_monotonic m m' unit.
    rewrite <- unit_dot. apply h; trivial. rewrite unit_dot. trivial. Qed.
  
Lemma update_total_preserves_most_stuff : ∀ (s: AllState) (u: InvState) (loc: Loc)
        (inv_vs: ∀ l, inv_loc_view_sat s u l)
        (inv_vi: ∀ l, inv_loc_view_identity s u l)
        (inv_lv: ∀ l, inv_loc_valid u l)
        (inv_bs: ∀ l, inv_loc_borrow_sound s u l)
        (inv_ti_almost: ∀ l, l <> loc -> inv_loc_total_identity s u l)
        (is_mov: mov (ltotal u loc)
                     (dot (Live s loc) (Unlive s u loc))) ,
                     
       let u' := update_total_at_loc s u loc in
            (∀ l, (not (IsLocExt l loc)) -> inv_loc_view_sat s u' l)
        /\ (∀ l, inv_loc_view_identity s u' l)
        /\ (∀ l, IsLocExt l loc -> inv_loc_valid u' l)
        /\ (∀ l, inv_loc_borrow_sound s u' l)
        /\ (∀ l, (not (IsLocExt l loc)) -> inv_loc_total_identity s u' l).
Proof.
  intros. repeat split.
    + intros.
        apply inv_loc_view_sat_preserve_total_change with (u := u) (loc_changed := loc); simpl; trivial.
          * simpl. intros. case_decide; trivial. contradiction.
    + intros.
        apply inv_loc_view_identity_on_total_change with (u := u); simpl; trivial.
    + intros. unfold inv_loc_valid in *. unfold ltotal. unfold update_total_at_loc in u'.
        simpl. case_decide; trivial.
            apply result_of_mov_is_valid with (m := ltotal u loc); trivial.
    + unfold inv_loc_borrow_sound in *. unfold view in *. trivial.
    
    + intros. have eqcase : Decision (l = loc).
      * solve_decision.
      * destruct eqcase.
        -- rewrite e. unfold update_total_at_loc in u'. unfold inv_loc_total_identity.
            unfold ltotal. simpl. case_decide; trivial. 
            ** f_equal. apply Unlive_on_total_change with (loc_changed := loc).
              ++ intros. unfold ltotal. simpl. case_decide; trivial. contradiction.
              ++ simpl. trivial.
              ++ rewrite e in H0. trivial.
            ** contradiction.
        -- apply inv_loc_total_identity_on_total_change with (u := u) (loc_changed := loc); simpl; trivial.
          ** intros. case_decide; trivial. contradiction.
          ** apply inv_ti_almost. trivial.
Qed.

Lemma recursive_update_total : ∀ (s: AllState) (loc: Loc) (u: InvState)
        (inv_vs: ∀ l, inv_loc_view_sat s u l)
        (inv_vi: ∀ l, inv_loc_view_identity s u l)
        (inv_lv: ∀ l, inv_loc_valid u l)
        (inv_bs: ∀ l, inv_loc_borrow_sound s u l)
        (inv_ti_almost: ∀ l, l <> loc -> inv_loc_total_identity s u l)
        (is_mov: mov (ltotal u loc)
                     (dot (Live s loc) (Unlive s u loc))) ,
        ∃ u' , inv s u'.
induction loc.
  - intros.
    exists (update_total_at_loc s u (LBase l)).
    have ninv := update_total_preserves_most_stuff s u (LBase l) inv_vs inv_vi inv_lv
                        inv_bs inv_ti_almost is_mov.
    destruct ninv. destruct H1. destruct H2. destruct H3.
    unfold inv. intros. unfold inv_loc. repeat split.
      + apply H0. auto.
      + apply H1.
      + apply H4. auto.
      + apply H2. auto.
      + apply H3.
  - intros.
    have ninv := update_total_preserves_most_stuff s u (LExt l r loc) inv_vs inv_vi inv_lv
                        inv_bs inv_ti_almost is_mov.
    destruct ninv.  destruct H1. destruct H2. destruct H3.
    apply IHloc with (u := update_total_at_loc s u (LExt l r loc)).
      + intro. apply H0.

Lemma live_update_preserve_inv : ∀ (s: AllState) (s': AllState) (u: InvState) (loc: Loc)
    (al_eq : active_lifetimes s = active_lifetimes s')
    (b_eq : borrows s = borrows s')
    (l_eq : ∀ l , l <> loc -> live_objects s l = live_objects s' loc)
    (r_eq : reserved_objects s = reserved_objects s')
    (va : valid (live_objects s' loc)) ,
    inv s u -> ∃ u' , inv s' u'.
intros.
    
Instance alls_valid_instance : Valid AllState := λ x, True.
  
Definition allstate_ra_mixin : RAMixin AllState.
split. 

Print Proper.
Print relation.*)

