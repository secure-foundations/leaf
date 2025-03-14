From iris.algebra Require Import ofe.
From iris.proofmode Require Import proofmode.
From lrust.util Require Import basic.

(** * Heterogeneous List *)

(* TODO : put relevant parts of this into stdpp ? *)

Inductive hlist {A} (F: A → Type) : list A → Type :=
| hnil: hlist F []
| hcons {X Xl} : F X → hlist F Xl → hlist F (X :: Xl).
Notation "+[ ]" := (hnil _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (hnil F) (at level 1, only parsing).
Infix "+::" := (hcons _) (at level 60, right associativity).
Infix "+::@{ F }" := (hcons F) (at level 60, right associativity, only parsing).
Notation "+[ x ; .. ; z ]" := (x +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ x ;  .. ;  z ]").
Notation "+[ x ; .. ; z ]@{ F }" := (x +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

Section hlist.
Context {A: Type} {F: A → Type}.

Definition hlist_nil_inv (P: hlist F [] → Type) (H: P +[]) xl : P xl :=
  match xl with +[] => H end.

Definition hlist_cons_inv {X Xl'}
  (P: hlist F (X :: Xl') → Type) (H: ∀x xl', P (x +:: xl')) xl : P xl.
Proof.
  move: P H. refine match xl with x +:: xl' => λ _ H, H x xl' end.
Defined.

Fixpoint happ {Xl Yl} (xl: hlist F Xl) (yl: hlist F Yl)
  : hlist F (Xl ++ Yl) :=
  match xl with +[] => yl | x +:: xl' => x +:: happ xl' yl end.

Fixpoint hmap {G} (f: ∀X, F X → G X) {Xl} (xl: hlist F Xl)
  : hlist G Xl :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hmap f xl' end.

Fixpoint hcmap {Y} (f: ∀X, F X → Y) {Xl} (xl: hlist F Xl)
  : list Y :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hcmap f xl' end.

Fixpoint hlookup {Xl} : ∀(xl: hlist F Xl) i, F (Xl !!ₗ i) :=
  match Xl with
  | [] => λ _, fin_0_inv _
  | X :: Xl' => hlist_cons_inv _
      (λ x xl', fin_S_inv _ x (hlookup xl'))
  end.

Fixpoint hrepeat {X} (x: F X) n : hlist F (repeat X n) :=
  match n with 0 => +[] | S m => x +:: hrepeat x m end.

Fixpoint max_hlist_with {Xl} (f: ∀X, F X → nat) (xl: hlist F Xl) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Lemma max_hlist_with_ge {Xl} (f: ∀X, F X → _) (xl: hlist F Xl) i :
  f _ (hlookup xl i) ≤ max_hlist_with f xl.
Proof.
  induction xl; inv_fin i=>/=. { rewrite /llookup /=. lia. }
  move=> i. etrans; [by apply IHxl|lia].
Qed.

Fixpoint happly {Y Xl} (fl: hlist (λ X, Y → F X) Xl) (x: Y)
  : hlist F Xl :=
  match fl with +[] => +[] | f +:: fl' => f x +:: happly fl' x end.
End hlist.

Ltac inv_hlist xl := let A := type of xl in
  match eval hnf in A with hlist _ ?Xl =>
    match eval hnf in Xl with
    | [] => revert dependent xl;
        match goal with |- ∀xl, @?P xl => apply (hlist_nil_inv P) end
    | _ :: _ => revert dependent xl;
        match goal with |- ∀xl, @?P xl => apply (hlist_cons_inv P) end;
        (* Try going on recursively. *)
        try (let x := fresh "x" in intros x xl; inv_hlist xl; revert x)
    end
  end.

Infix "h++" := happ (at level 60, right associativity).
Infix "+<$>" := hmap (at level 61, left associativity).
Infix "+c<$>" := hcmap (at level 61, left associativity).
Infix "+!!" := hlookup (at level 20, right associativity).
Infix "+$" := happly (at level 61, left associativity).
Notation "( fl +$.)" := (happly fl) (only parsing).

Lemma hlookup_apply {A} {F: A → Type} {Xl Y}
    (fl: hlist (λ X, Y → F X) Xl) (x: Y) i :
  (fl +$ x) +!! i = (fl +!! i) x.
Proof. induction Xl; inv_fin i; inv_hlist fl; [done|]=>/= *. apply IHXl. Qed.

(** * Passive Heterogeneous List *)

Inductive nil_unit: Set := nil_tt: nil_unit.
Record cons_prod (A B: Type) : Type := cons_pair { phd: A; ptl: B }.
Arguments cons_pair {_ _} _ _.
Arguments phd {_ _} _.
Arguments ptl {_ _} _.

Notation "-[ ]" := nil_tt (at level 1, format "-[ ]").
Infix "-::" := cons_pair (at level 60, right associativity).
Notation "(-::)" := cons_pair (only parsing).
Notation "-[ x ; .. ; z ]" := (x -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ x ;  .. ;  z ]").


Notation "*[ ]" := nil_unit (at level 1, format "*[ ]") : type_scope.
Infix "*::" := cons_prod (at level 60, right associativity) : type_scope.
Notation "*[ A ; .. ; Z ]" := (A *:: .. (Z *:: *[]) ..)
  (at level 1, format "*[ A ;  .. ;  Z ]") : type_scope.

Global Instance nil_unit_iso : Iso (const -[]) (const ()).
Proof. split; fun_ext; by case. Qed.
Global Instance nil_unit_iso' : Iso (const ()) (const -[]) | 10.
Proof. split; apply _. Qed.

Definition to_cons_prod {A B} : A * B → A *:: B := λ '(a, al), a -:: al.
Definition of_cons_prod {A B} : A *:: B → A * B := λ '(a -:: al), (a, al).
Global Instance cons_prod_iso {A B} : Iso (@to_cons_prod A B) of_cons_prod.
Proof. split; fun_ext; by case. Qed.

Section plist.
Context {A: Type} {F: A → Type}.

Fixpoint plist (Xl: list A) : Type :=
  match Xl with [] => *[] | X :: Xl' => F X *:: plist Xl' end.

Fixpoint papp {Xl Yl} (xl: plist Xl) (yl: plist Yl) :
  plist (Xl ++ Yl) :=
  match Xl, xl with [], _ => yl | _::_, x -:: xl' => x -:: papp xl' yl end.

Fixpoint psepl {Xl Yl} (xl: plist (Xl ++ Yl)) : plist Xl :=
  match Xl, xl with [], _ => -[] | _::_, x -:: xl' => x -:: psepl xl' end.
Fixpoint psepr {Xl Yl} (xl: plist (Xl ++ Yl)) : plist Yl :=
  match Xl, xl with [], _ => xl | _::_, _ -:: xl' => psepr xl' end.

Lemma papp_sepl {Xl Yl} (xl: plist Xl) (yl: plist Yl) : psepl (papp xl yl) = xl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.
Lemma papp_sepr {Xl Yl} (xl: plist Xl) (yl: plist Yl) : psepr (papp xl yl) = yl.
Proof. move: xl yl. elim Xl; [by case|]=>/= > IH [??]?. by rewrite IH. Qed.

Lemma psep_app {Xl Yl} (xl: plist (Xl ++ Yl)) : papp (psepl xl) (psepr xl) = xl.
Proof. move: xl. elim Xl; [done|]=>/= > IH [??]. by rewrite IH. Qed.
Lemma papp_ex {Xl Yl} (xl: plist (Xl ++ Yl)) :
  ∃(yl: plist Xl) (zl: plist Yl), xl = papp yl zl.
Proof. exists (psepl xl), (psepr xl). by rewrite psep_app. Qed.

Fixpoint plookup {Xl} (xl: plist Xl) : ∀i, F (Xl !!ₗ i) :=
  match Xl, xl with
  | [], _ => fin_0_inv _
  | _::_, x -:: xl' => fin_S_inv _ x (plookup xl')
  end.

Global Instance papp_psep_iso {Xl Yl}
  : Iso (uncurry (@papp Xl Yl)) (λ xl, (psepl xl, psepr xl)).
Proof.
  split; fun_ext.
  - case=>/= [??]. by rewrite papp_sepl papp_sepr.
  - move=>/= ?. by rewrite psep_app.
Qed.

Fixpoint hlist_to_plist {Xl} (xl: hlist F Xl) : plist Xl :=
  match xl with +[] => -[] | x +:: xl' => x -:: hlist_to_plist xl' end.
Fixpoint plist_to_hlist {Xl} (xl: plist Xl) : hlist F Xl :=
  match Xl, xl with [], _ => +[] | _::_, x -:: xl' => x +:: plist_to_hlist xl' end.
Global Instance hlist_plist_iso {Xl} :
  Iso (@hlist_to_plist Xl) plist_to_hlist.
Proof.
  split.
  - fun_ext. by elim; [done|]=>/= > ->.
  - fun_ext. elim Xl; [by case|]=>/= ?? IH [??] /=. by rewrite IH.
Qed.

Fixpoint vec_to_plist {X n} (xl: vec (F X) n) : plist (replicate n X) :=
  match xl with [#] => -[] | x ::: xl' => x -:: vec_to_plist xl' end.
Fixpoint plist_to_vec {X n} (xl: plist (replicate n X)) : vec (F X) n :=
  match n, xl with 0, _ => [#] | S _, x -:: xl' => x ::: plist_to_vec xl' end.
End plist.

Arguments plist {_} _ _.

Infix "-++" := papp (at level 60, right associativity).
Notation psep := (λ xl, (psepl xl, psepr xl)).
Infix "-!!" := plookup (at level 20, right associativity).

Fixpoint pmap {A} {F G: A → Type} (f: ∀X, F X → G X) {Xl} : plist F Xl → plist G Xl :=
  match Xl with [] => id | _::_ => λ '(x -:: xl'), f _ x -:: pmap f xl' end.
Infix "-<$>" := pmap (at level 61, left associativity).

Lemma pmap_app {A} {F G: A → Type} {Xl Yl} (f: ∀X, F X → G X)
      (xl: plist F Xl) (yl: plist F Yl) :
  f -<$> (xl -++ yl) = (f -<$> xl) -++ (f -<$> yl).
Proof. move: xl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint papply {A} {F: A → Type} {B Xl}
         (fl: plist (λ X, B → F X) Xl) (x: B) : plist F Xl :=
  match Xl, fl with
  | [], _ => -[]
  | _::_, f -:: fl' => f x -:: papply fl' x
  end.
Infix "-$" := papply (at level 61, left associativity).
Notation "( fl -$.)" := (papply fl) (only parsing).

Lemma papply_app {A} {F: A → Type} {B Xl Yl}
  (fl: plist (λ X, B → F X) Xl) (gl: plist (λ X, B → F X) Yl) (x: B) :
  (fl -++ gl) -$ x = (fl -$ x) -++ (gl -$ x).
Proof. move: fl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

Fixpoint hzip_with {A} {F G H: A → Type} {Xl} (f: ∀X, F X → G X → H X)
  (xl: hlist F Xl) (yl: plist G Xl) : hlist H Xl :=
  match xl, yl with
  | +[], _ => +[]
  | x +:: xl', y -:: yl' => f _ x y +:: hzip_with f xl' yl'
  end.
Notation hzip := (hzip_with (λ _, pair)).

Fixpoint pzip_with {A} {F G H: A → Type} {Xl} (f: ∀X, F X → G X → H X)
  (xl: plist F Xl) (yl: plist G Xl) : plist H Xl :=
  match Xl, xl, yl with
  | [], _, _ => -[]
  | _::_, x -:: xl', y -:: yl' => f _ x y -:: pzip_with f xl' yl'
  end.
Notation pzip := (pzip_with (λ _, pair)).

(* We don't use [∘] here because [∘] is universe-monomorphic
  and thus causes universe inconsistency *)
Fixpoint ptrans {A B} {F: A → B} {G Xl} (xl: plist (λ X, G (F X)) Xl)
    : plist G (map F Xl) :=
  match Xl, xl with [], _ => -[] | _::_, x -:: xl' => x -:: ptrans xl' end.

Fixpoint pbyidx {A} {F: A → Type} {Xl} : (∀i, F (Xl !!ₗ i)) → plist F Xl :=
  match Xl with
  | [] => λ _, -[]
  | _::_ => λ f, f 0%fin -:: pbyidx (λ j, f (FS j))
  end.

Global Instance pbyidx_plookup_iso {A} {F: A → Type} {Xl} :
  Iso (pbyidx (F:=F) (Xl:=Xl)) plookup.
Proof.
  split; fun_ext.
  - move=>/= f. fun_ext_dep=> i. induction Xl; inv_fin i; [done|]=>/= ?.
    by rewrite IHXl.
  - move=>/= xl. induction Xl; case xl; [done|]=>/= ??. by rewrite IHXl.
Qed.

Lemma pbyidx_plookup {A} {F: A → Type} {Xl} (f: ∀i, F (Xl !!ₗ i)) i :
  pbyidx f -!! i = f i.
Proof. by rewrite semi_iso'. Qed.

(** * Passive Heterogeneous List over Two Lists *)

Section plist2.
Context {A: Type} {F: A → A → Type}.

Fixpoint plist2 Xl Yl : Type :=
  match Xl, Yl with
  | [], [] => *[]
  | X :: Xl', Y :: Yl' => (F X Y) *:: (plist2 Xl' Yl')
  | _, _ => ∅
  end.

Fixpoint plist2_eq_nat_len {Xl Yl} :
  plist2 Xl Yl → eq_nat (length Xl) (length Yl) :=
  match Xl, Yl with
  | [], [] => λ _, I
  | _::_, _::_ => λ '(_ -:: xl'), plist2_eq_nat_len xl'
  | _, _ => absurd
  end.

Lemma plist2_eq_len {Xl Yl} : plist2 Xl Yl → length Xl = length Yl.
Proof. by move=> /plist2_eq_nat_len/eq_nat_is_eq ?. Qed.

Definition fin_renew_by_plist2 {Xl Yl} (xl: plist2 Xl Yl) (i: fin (length Xl))
    : fin (length Yl) :=
  fin_renew (plist2_eq_nat_len xl) i.

Fixpoint p2lookup {Xl Yl} : ∀(xl: plist2 Xl Yl) i,
    F (Xl !!ₗ i) (Yl !!ₗ fin_renew_by_plist2 xl i) :=
  match Xl, Yl with
  | [], [] => λ _, fin_0_inv _
  | _::_, _::_ => λ '(x -:: xl'), fin_S_inv _ x (p2lookup xl')
  | _, _ => λ xl, absurd xl
  end.
End plist2.

Arguments plist2 {_} _ _ _.

Infix "-2!!" := p2lookup (at level 20, right associativity).

Fixpoint p2map {A} {F G: A → A → Type} (f: ∀X Y, F X Y → G X Y) {Xl Yl}
  : plist2 F Xl Yl → plist2 G Xl Yl :=
  match Xl, Yl with
  | [], [] => id
  | _::_, _::_ => λ '(x -:: xl'), f _ _ x -:: p2map f xl'
  | _, _ => absurd
  end.
Infix "-2<$>" := p2map (at level 61, left associativity).

Fixpoint plist_map {A} {F: A → Type} {Xl Yl} :
  plist2 (λ X Y, F X → F Y) Xl Yl → plist F Xl → plist F Yl :=
  match Xl, Yl with
  | [], [] => λ _, id
  | _::_, _::_ => λ '(f -:: fl') '(x -:: xl'), f x -:: plist_map fl' xl'
  | _, _ => absurd
  end.

Fixpoint plist_map_with {A} {F: A → Type} {G} {Xl Yl} (h: ∀X Y, G X Y → F X → F Y) :
  plist2 G Xl Yl → plist F Xl → plist F Yl :=
  match Xl, Yl with
  | [], [] => λ _, id
  | _::_, _::_ => λ '(f -:: fl') '(x -:: xl'), h _ _ f x -:: plist_map_with h fl' xl'
  | _, _ => absurd
  end.

(** * [plist] with a Constant Functor *)

Definition plistc {A} (B: Type) (Xl: list A) : Type := plist (const B) Xl.

Fixpoint plistc_to_vec {A B} {Xl: list A} (xl: plistc B Xl) : vec B (length Xl) :=
  match Xl, xl with [], _ => [#] | _::_, x -:: xl' => x ::: plistc_to_vec xl' end.
Coercion plistc_to_vec: plistc >-> vec.

Lemma plistc_to_vec_lookup {A B} {Xl: list A} (xl: plistc B Xl) i :
  plistc_to_vec xl !!! i = xl -!! i.
Proof. induction Xl; inv_fin i; case xl; [done|]=>/= _. apply IHXl. Qed.

Fixpoint plistc_renew {A} {Xl: list A} {A'} {Yl: list A'} {B}
  : eq_nat (length Xl) (length Yl) → plistc B Xl → plistc B Yl :=
  match Xl, Yl with
  | [], [] => λ _ _, -[]
  | _ :: Xl', _ :: Yl' => λ e '(x -:: xl'), x -:: plistc_renew (Xl:=Xl') e xl'
  | _, _ => absurd
  end.

Lemma vec_to_list_plistc_renew {A} {Xl: list A} {A'} {Yl: list A'} {B}
    (xl: plistc B Xl) (e: eq_nat (length Xl) (length Yl)) :
  vec_to_list (plistc_renew e xl) = vec_to_list xl.
Proof.
  move: Xl Yl e xl. fix FIX 1. case=> [|??]; case=>//= ???[??]/=. by rewrite FIX.
Qed.

Class IntoPlistc {A} {Xl: list A} {B} (xl: list B) (yl: plistc B Xl) :=
  into_plistc: xl = yl.

Global Instance into_plistc_nil {A B} : @IntoPlistc A [] B [] -[].
Proof. done. Qed.

Global Instance into_plistc_cons {A B X Xl} x xl yl :
  IntoPlistc xl yl → @IntoPlistc A (X :: Xl) B (x :: xl) (x -:: yl).
Proof. by move=> ->. Qed.

(* We need the following hint because usually [into_plistc_cons] works
  with [apply] but not with [simple apply] *)
Global Hint Extern 0 (IntoPlistc _ _) => apply into_plistc_cons : typeclass_instances.

(** * Sum *)

Section psum.
Context {A} {F: A → Type}.

Fixpoint psum (Xl: list A) : Type :=
  match Xl with [] => ∅ | X :: Xl' => F X + psum Xl' end.

Fixpoint pinj {Xl: list A} : ∀i, F (Xl !!ₗ i) → psum Xl :=
  match Xl with
  | [] => fin_0_inv _
  | X :: Xl' => fin_S_inv (λ i, F ((X :: Xl') !!ₗ i) → F X + psum Xl')
      inl (λ j x, inr (@pinj Xl' j x))
  end.

Lemma pinj_inj {Xl} i j (x: F (Xl !!ₗ i)) y :
  pinj i x = pinj j y → i = j ∧ x ~= y.
Proof.
  move: Xl i j x y. elim; [move=> i; by inv_fin i|]=>/= ?? IH i j.
  inv_fin i; inv_fin j=>//=. { by move=> ??[=->]. }
  move=> ????[=/IH[??]]. split; [|done]. by f_equal.
Qed.

Global Instance pinj_Inj {Xl} i : Inj eq eq (@pinj Xl i).
Proof.
  move: i. elim Xl; [move=> i; by inv_fin i|]=>/= ?? IH i.
  inv_fin i. { by move=>/= ??[=?]. } by move=>/= ???[=/IH ?].
Qed.

Fixpoint psum_map {Xl Yl} :
    plist2 (λ X Y, F X → F Y) Xl Yl → psum Xl → psum Yl :=
  match Xl, Yl with
  | [], [] => λ _, absurd
  | _::_, _::_ => λ '(f -:: fl'), sum_map f (psum_map fl')
  | _, _ => absurd
  end.

Lemma psum_map_pinj {Xl Yl} (fl: plist2 (λ X Y, F X → F Y) Xl Yl) i x :
  psum_map fl (pinj i x) = pinj (fin_renew_by_plist2 fl i) ((fl -2!! i) x).
Proof.
  move: Xl Yl fl i x. fix FIX 1. move=> [|??][|??]//=; [move=> ? i; by inv_fin i|].
  move=>/= [??]i. inv_fin i; [done|]=>/= ??. by rewrite FIX.
Qed.

Definition to_psum_2 {X Y} (s: F X + F Y) : psum [X; Y] :=
  match s with inl x => inl x | inr y => inr (inl y) end.
Definition of_psum_2 {X Y} (s: psum [X; Y]) : F X + F Y :=
  match s with inl x => inl x | inr (inl y) => inr y | inr (inr e) => absurd e end.
Global Instance psum_2_iso {X Y} : Iso (@to_psum_2 X Y) of_psum_2.
Proof. split; fun_ext; by [case|case=> [?|[?|[]]]]. Qed.
End psum.

Arguments psum {_} _ _.

Section xsum.
Context {A} {F: A → Type}.

Inductive xsum (Xl: list A) := xinj i : F (Xl !!ₗ i) → xsum Xl.
Arguments xinj {_} _ _.

Fixpoint to_xsum {Xl} : psum F Xl → xsum Xl :=
  match Xl with
  | [] => absurd
  | _::_ => λ s, match s with
    | inl a => @xinj (_::_) 0%fin a
    | inr s' => let 'xinj j b := to_xsum s' in @xinj (_::_) (FS j) b
    end
  end.

Lemma to_xsum_pinj {Xl} i (x: F (Xl !!ₗ i)) :
  to_xsum (pinj i x) = xinj i x.
Proof.
  move: Xl i x. elim; [move=> i; by inv_fin i|]=>/= ?? IH i.
  inv_fin i; [done|]=>/= ??. by rewrite IH.
Qed.

Definition of_xsum {Xl} (s: xsum Xl) : psum F Xl :=
  let 'xinj i a := s in pinj i a.

Global Instance xsum_iso {Xl} : Iso (@to_xsum Xl) of_xsum.
Proof.
  split; fun_ext=>/=; [|case=>/= ??; by apply to_xsum_pinj].
  elim Xl; [by case|]=>/= ?? IH [|]; [done|]=>/= s. move: (IH s).
  by case: (to_xsum s)=>/= ??->.
Qed.
End xsum.

Arguments xinj {_ _ _} _ _.
Arguments xsum {_} _ _.

(** * Forall *)

Section Forall.
Context {A} {F G: A → Type}.

Inductive HForall (Φ: ∀X, F X → Prop) : ∀{Xl}, hlist F Xl → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {X Xl} (x: _ X) (xl: _ Xl) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Fixpoint pforall {Xl} (Φ: ∀X, F X → Prop) (xl: plist F Xl) : Prop :=
  match Xl, xl with [], _ => True | _::_, x -:: xl' => Φ _ x ∧ pforall Φ xl' end.

Inductive TCHForall (Φ: ∀X, F X → Prop) : ∀{Xl}, hlist F Xl → Prop :=
| TCHForall_nil: TCHForall Φ +[]
| TCHForall_cons {X Xl} (x: _ X) (xl: _ Xl) :
    Φ _ x → TCHForall Φ xl → TCHForall Φ (x +:: xl).
Existing Class TCHForall.
Global Existing Instance TCHForall_nil.
Global Existing Instance TCHForall_cons.

Inductive HForall_1 (Φ: ∀X, F X → G X → Prop)
  : ∀{Xl}, hlist F Xl → plist G Xl → Prop :=
| HForall_1_nil: HForall_1 Φ +[] -[]
| HForall_1_cons {X Xl} (x: _ X) y (xl: _ Xl) yl :
    Φ _ x y → HForall_1 Φ xl yl → HForall_1 Φ (x +:: xl) (y -:: yl).

Inductive HForall_1' {H: A → A → Type} (Φ: ∀X Y, F X → H X Y → Prop)
  : ∀{Xl Yl}, hlist F Xl → plist2 H Xl Yl → Prop :=
| HForall_1'_nil: HForall_1' Φ +[] (-[]: plist2 _ [] [])
| HForall_1'_cons {X Y Xl Yl} x z xl zl :
    Φ _ _ x z → HForall_1' Φ xl zl →
    HForall_1' Φ (x +:: xl) (z -:: zl: plist2 _ (X :: Xl) (Y :: Yl)).

Inductive HForall2_1 {H: A → A → Type} (Φ: ∀X Y, F X → G Y → H X Y → Prop)
  : ∀{Xl Yl}, hlist F Xl → hlist G Yl → plist2 H Xl Yl → Prop :=
| HForall2_1_nil: HForall2_1 Φ +[] +[] -[]
| HForall2_1_cons {X Y Xl Yl} (x: _ X) (y: _ Y) z (xl: _ Xl) (yl: _ Yl) zl :
    Φ _ _ x y z → HForall2_1 Φ xl yl zl → HForall2_1 Φ (x +:: xl) (y +:: yl) (z -:: zl).

Inductive HForall2_2flip {H K: A → A → Type} (Φ: ∀X Y, F X → G Y → H X Y → K Y X → Prop)
  : ∀{Xl Yl}, hlist F Xl → hlist G Yl → plist2 H Xl Yl → plist2 K Yl Xl → Prop :=
| HForall2_2flip_nil: HForall2_2flip Φ +[] +[] -[] -[]
| HForall2_2flip_cons {X Y Xl Yl} (x: _ X) (y: _ Y) z w (xl: _ Xl) (yl: _ Yl) zl wl :
    Φ _ _ x y z w → HForall2_2flip Φ xl yl zl wl →
    HForall2_2flip Φ (x +:: xl) (y +:: yl) (z -:: zl) (w -:: wl).

Inductive HForallTwo (Φ: ∀X, F X → G X → Prop) : ∀{Xl}, hlist F Xl → hlist G Xl → Prop :=
| HForallTwo_nil: HForallTwo Φ +[] +[]
| HForallTwo_cons {X Xl} (x: _ X) y (xl: _ Xl) yl :
    Φ _ x y → HForallTwo Φ xl yl → HForallTwo Φ (x +:: xl) (y +:: yl).

Lemma TCHForall_impl {Xl} (Φ Ψ: ∀X, F X → Prop) (xl: hlist F Xl) :
  (∀X x, Φ X x → Ψ _ x) → TCHForall Φ xl → TCHForall Ψ xl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma HForallTwo_impl {Xl} (Φ Ψ: ∀X, F X → G X → Prop) (xl: hlist F Xl) yl :
  (∀X x y, Φ X x y → Ψ X x y) → HForallTwo Φ xl yl → HForallTwo Ψ xl yl.
Proof. move=> Imp. elim; constructor; by [apply Imp|]. Qed.

Lemma TCHForall_lookup {Xl} i (Φ: ∀X, F X → Prop) (xl: hlist F Xl) :
  TCHForall Φ xl → Φ _ (xl +!! i).
Proof. move=> All. induction All; inv_fin i; [done|]. apply IHAll. Qed.

Lemma HForall_1_lookup {Xl} i (Φ: ∀X, F X → G X → Prop) (xl: _ Xl) yl :
  HForall_1 Φ xl yl → Φ _ (xl +!! i) (yl -!! i).
Proof. move=> All. induction All; inv_fin i; [done|]. apply IHAll. Qed.

Lemma HForall_1'_lookup {H: A → A → Type} {Xl Yl} i
    (Φ: ∀X Y, F X → H X Y → Prop) xl (yl: plist2 _ Xl Yl) :
  HForall_1' Φ xl yl → Φ _ _ (xl +!! i) (yl -2!! i).
Proof. move=> All. induction All; inv_fin i; [done|]. apply IHAll. Qed.

Lemma HForallTwo_lookup {Xl} i (Φ: ∀X, F X → G X → Prop) (xl: _ Xl) yl :
  HForallTwo Φ xl yl → Φ _ (xl +!! i) (yl +!! i).
Proof. move=> All. induction All; inv_fin i; [done|]. apply IHAll. Qed.

Lemma HForallTwo_forall `{!Inhabited Y} {Xl}
  (Φ: ∀X, Y → F X → G X → Prop) (xl yl: _ Xl) :
  (∀z, HForallTwo (λ X, Φ X z) xl yl) ↔ HForallTwo (λ X x y, ∀z, Φ _ z x y) xl yl.
Proof.
  split; [|elim; by constructor]. move=> All. set One := All inhabitant.
  induction One; [by constructor|]. constructor.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  have All': ∀z, HForallTwo (λ X, Φ X z) xl yl.
  { move=> z. move/(.$ z) in All. by dependent destruction All. }
  auto.
Qed.
End Forall.

Section HForallTwo.
Context {A} {F: A → Type} {Xl: list A} (R: ∀X, F X → F X → Prop).

Global Instance HForallTwo_reflexive :
  (∀X, Reflexive (R X)) → Reflexive (HForallTwo R (Xl:=Xl)).
Proof. move=> ?. elim; by constructor. Qed.
Global Instance HForallTwo_symmetric :
  (∀X, Symmetric (R X)) → Symmetric (HForallTwo R (Xl:=Xl)).
Proof. move=> >. elim; by constructor. Qed.
Global Instance HForallTwo_transitive :
  (∀X, Transitive (R X)) → Transitive (HForallTwo R (Xl:=Xl)).
Proof.
  move=> ??? zl All. move: zl. elim: All; [done|]=> > ?? IH ? All.
  dependent destruction All. constructor; by [etrans|apply IH].
Qed.

Global Instance HForallTwo_equivalence :
  (∀X, Equivalence (R X)) → Equivalence (HForallTwo R (Xl:=Xl)).
Proof. split; apply _. Qed.
End HForallTwo.

(** * Ofe *)

Section hlist_ofe.
Context {A} {F: A → ofe} {Xl: list A}.

Global Instance hlist_equiv : Equiv (hlist F Xl) := HForallTwo (λ _, (≡)).
Global Instance hlist_dist : Dist (hlist F Xl) := λ n, HForallTwo (λ _, dist n).

Definition hlist_ofe_mixin : OfeMixin (hlist F Xl).
Proof.
  split=> >.
  - rewrite /equiv /hlist_equiv HForallTwo_forall.
    split=> H; induction H; constructor=>//; by apply equiv_dist.
  - apply _.
  - rewrite /dist /hlist_dist. apply HForallTwo_impl=> >. apply dist_S.
Qed.

Canonical Structure hlistO := Ofe (hlist F Xl) hlist_ofe_mixin.
End hlist_ofe.

Arguments hlistO {_} _ _.

(* FIXME : this is to improve the corresponding hints defined in Iris,
   which are not able to find the canonical structure for hlist, probably
   because this is using eapply and its different unification algorithm. *)
Global Hint Extern 0 (Equiv _) => refine (ofe_equiv _); shelve : typeclass_instances.
Global Hint Extern 0 (Dist _) => refine (ofe_dist _); shelve : typeclass_instances.

Section hlist_ofe_lemmas.
Context {A} {F: A → ofe} {Xl: list A}.

Global Instance hcons_ne {X} : NonExpansive2 (@hcons _ F X Xl).
Proof. by constructor. Qed.
Global Instance hcons_proper {X} : Proper ((≡) ==> (≡) ==> (≡)) (@hcons _ F X Xl).
Proof. by constructor. Qed.

Global Instance hlookup_ne n :
  Proper (dist n ==> forall_relation (λ i, dist n)) (@hlookup _ F Xl).
Proof. move=> ????. by apply (HForallTwo_lookup _ (λ X, ofe_dist (F X) n)). Qed.
Global Instance hlookup_proper :
  Proper ((≡) ==> forall_relation (λ _, (≡))) (@hlookup _ F Xl).
Proof. move=> ?? /equiv_dist ??. apply equiv_dist=> ?. by apply hlookup_ne. Qed.
End hlist_ofe_lemmas.

(** * big_sep *)

Section big_sep.
Context {PROP: bi} {A: Type}.

Fixpoint big_sepHL {F: A → Type} {Xl} (Φ: ∀X, F X → PROP) (xl: hlist F Xl) : PROP :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end%I.

Fixpoint big_sepHL_1 {F G: A → Type} {Xl} (Φ: ∀X, F X → G X → PROP)
    (xl: hlist F Xl) (yl: plist G Xl) : PROP :=
  match xl, yl with
  | +[], _ => True
  | x +:: xl', y -:: yl' => Φ _ x y ∗ big_sepHL_1 Φ xl' yl'
  end%I.

Fixpoint big_sepHL_2 {F G H: A → Type} {Xl} (Φ: ∀X, F X → G X → H X → PROP)
    (xl: hlist F Xl) (yl: plist G Xl) (zl: plist H Xl) : PROP :=
  match xl, yl, zl with
  | +[], _, _ => True
  | x +:: xl', y -:: yl', z -:: zl' => Φ _ x y z ∗ big_sepHL_2 Φ xl' yl' zl'
  end%I.

Fixpoint big_sepHL2_1 {F: A → Type} {G H Xl Yl} (Φ: ∀X Y, F X → G Y → H X Y → PROP)
    (xl: hlist F Xl) (yl: hlist G Yl) (zl: plist2 H Xl Yl) : PROP :=
  match xl, yl, zl with
  | +[], +[], _ => True
  | x +:: xl', y +:: yl', z -:: zl' => Φ _ _ x y z ∗ big_sepHL2_1 Φ xl' yl' zl'
  | _, _, _ => False
  end%I.
End big_sep.

Notation "[∗ hlist] x ∈ xl , P" := (big_sepHL (λ _ x, P%I) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  hlist]  x  ∈  xl ,  P") : bi_scope.

Notation "[∗ hlist] x ;- y ∈ xl ;- yl , P" := (big_sepHL_1 (λ _ x y, P%I) xl yl)
  (at level 200, xl, yl at level 10, x, y at level 1, right associativity,
    format "[∗  hlist]  x ;-  y  ∈  xl ;-  yl ,  P") : bi_scope.

Notation "[∗ hlist] x ;- y ; z ∈ xl ;- yl ; zl , P" :=
  (big_sepHL_2 (λ _ x y z, P%I) xl yl zl)
  (at level 200, xl, yl, zl at level 10, x, y, z at level 1, right associativity,
    format "[∗  hlist]  x ;-  y ;  z  ∈  xl ;-  yl ;  zl ,  P") : bi_scope.

Notation "[∗ hlist] x ; y ;- z ∈ xl ; yl ;- zl , P" :=
  (big_sepHL2_1 (λ _ _ x y z, P%I) xl yl zl)
  (at level 200, xl, yl, zl at level 10, x, y, z at level 1, right associativity,
    format "[∗  hlist]  x ;  y ;-  z  ∈  xl ;  yl ;-  zl ,  P") : bi_scope.

Section lemmas.
Context `{!BiAffine PROP} {A: Type}.

Lemma big_sepHL_app {F: A → Type} {Xl Yl}
      (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, F C → PROP) :
  big_sepHL Φ (xl h++ xl') ⊣⊢ big_sepHL Φ xl ∗ big_sepHL Φ xl'.
Proof. elim xl; [by rewrite/= left_id|]=>/= > ->. by rewrite assoc. Qed.

Lemma big_sepHL_1_app {F: A → Type} {G Xl Yl}
      (xl: hlist F Xl) (xl': hlist F Yl)
      (yl: plist G Xl) (yl': plist G Yl) (Φ: ∀C, F C → G C → PROP) :
  big_sepHL_1 Φ (xl h++ xl') (yl -++ yl') ⊣⊢ big_sepHL_1 Φ xl yl ∗ big_sepHL_1 Φ xl' yl'.
Proof. induction xl, yl; by [rewrite/= left_id|rewrite/= IHxl assoc]. Qed.

Global Instance into_sep_big_sepHL_app {F: A → Type} {Xl Yl}
    (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, F C → PROP) :
  IntoSep (big_sepHL Φ (xl h++ xl')) (big_sepHL Φ xl) (big_sepHL Φ xl').
Proof. by rewrite /IntoSep big_sepHL_app. Qed.
Global Instance from_sep_big_sepHL_app {F: A → Type} {Xl Yl}
  (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, F C → PROP) :
  FromSep (big_sepHL Φ (xl h++ xl')) (big_sepHL Φ xl) (big_sepHL Φ xl').
Proof. by rewrite /FromSep big_sepHL_app. Qed.

Global Instance into_sep_big_sepHL_1_app {F: A → Type} {G Xl Yl}
    (xl: hlist F Xl) (xl': hlist F Yl) (yl: plist G Xl) (yl': plist G Yl)
    (Φ: ∀C, F C → G C → PROP) :
  IntoSep (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 Φ xl yl) (big_sepHL_1 Φ xl' yl').
Proof. by rewrite /IntoSep big_sepHL_1_app. Qed.
Global Instance from_sep_big_sepHL_1_app {F: A → Type} {G Xl Yl}
    (xl: hlist F Xl) (xl': hlist F Yl) (yl: plist G Xl) (yl': plist G Yl)
    (Φ: ∀C, F C → G C → PROP) :
  FromSep (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl'))
    (big_sepHL_1 Φ xl yl) (big_sepHL_1 Φ xl' yl').
Proof. by rewrite /FromSep big_sepHL_1_app. Qed.

Global Instance frame_big_sepHL_app {F G: A → Type} {Xl Yl}
    p R Q (xl: hlist F Xl) (xl': hlist F Yl) (Φ: ∀C, F C → PROP) :
  Frame p R (big_sepHL Φ xl ∗ big_sepHL Φ xl') Q →
  Frame p R (big_sepHL Φ (xl h++ xl')) Q.
Proof. by rewrite /Frame big_sepHL_app. Qed.

Global Instance frame_big_sepHL_1_app {F G: A → Type} {Xl Yl}
    p R Q (xl: hlist F Xl) (xl': hlist F Yl) (yl: plist G Xl) (yl': plist G Yl)
    (Φ: ∀C, F C → G C → PROP) :
  Frame p R (big_sepHL_1 Φ xl yl ∗ big_sepHL_1 Φ xl' yl') Q →
  Frame p R (big_sepHL_1 Φ (xl h++ xl') (yl -++ yl')) Q.
Proof. by rewrite /Frame big_sepHL_1_app. Qed.

Lemma big_sepHL_2_big_sepN {F G H: A → Type} {Xl}
    (Φ: ∀X, F X → G X → H X → PROP) (xl: hlist F Xl) yl zl :
  big_sepHL_2 Φ xl yl zl ⊣⊢
  [∗ nat] i < length Xl, Φ _ (xl +!! i) (yl -!! i) (zl -!! i).
Proof.
  move: Φ. induction Xl; inv_hlist xl; case yl; case zl; [done|]=>/= *.
  f_equiv; [done|apply IHXl].
Qed.

Lemma big_sepHL_2_lookup {F G H: A → Type} {Xl}
    i (Φ: ∀X, F X → G X → H X → PROP) (xl: hlist F Xl) yl zl :
  big_sepHL_2 Φ xl yl zl -∗ Φ _ (xl +!! i) (yl -!! i) (zl -!! i).
Proof.
  iIntros "All". iInduction xl as [|] "IH" forall (i); [by inv_fin i|].
  move: yl zl=> [??][??]/=. iDestruct "All" as "[Φ All]".
  inv_fin i; [done|]=> ?. by iApply "IH".
Qed.
End lemmas.
