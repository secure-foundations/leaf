From iris.proofmode Require Import proofmode.
From lrust.util Require Import basic.

(* TODO : move all that to stdpp *)

(** * Utility for Vectors *)

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.

Definition vcons' {A n} (x: A) (xl': vec A n) : vec A (S n) := x ::: xl'.
Global Arguments vcons' {_ _} /.

Global Instance vcons_inj' {A n} : Inj2 (=) (=) (=) (@vcons' A n).
Proof. move=>/= ?????. by apply vcons_inj. Qed.

Lemma surjective_vcons {A n} (xl: vec A (S n)) : xl = vhd xl ::: vtl xl.
Proof. by inv_vec xl. Qed.

Lemma surjective_vcons_fun {A B n} (f: B → vec A (S n)) :
  f = vcons' ∘ (vhd ∘ f) ⊛ (vtl ∘ f).
Proof. fun_ext=>/= ?. by rewrite -surjective_vcons. Qed.

Global Instance vhd_vsingleton_iso {A} : Iso vhd (λ x: A, [#x]).
Proof. split; [|done]. fun_ext=> v. by inv_vec v. Qed.

Global Instance vhd_vtl_vcons_iso {A n} :
  Iso (λ v: vec A (S n), (vhd v, vtl v)) (uncurry vcons').
Proof. split; fun_ext; [|by case]=> v. by inv_vec v. Qed.

Global Instance vec_to_list_inj' {A n} : Inj (=) (=) (@vec_to_list A n).
Proof. move=> ??. apply vec_to_list_inj2. Qed.

(** [vzip] *)

Notation vzip := (vzip_with pair).

Lemma vzip_with_app {A B C m n} (f: A → B → C) (xl: vec _ m) (xl': vec _ n) yl yl' :
  vzip_with f (xl +++ xl') (yl +++ yl') = vzip_with f xl yl +++ vzip_with f xl' yl'.
Proof. induction xl; inv_vec yl; [done|]=>/= ??. by rewrite IHxl. Qed.

(** [vsepat] *)

Notation vsepat := Vector.splitat.

Lemma vsepat_app {A m n} (xl: _ A (m + n)) :
  xl = (vsepat m xl).1 +++ (vsepat m xl).2.
Proof.
  induction m; [done|]=>/=.
  by rewrite [vsepat _ _]surjective_pairing /= -IHm -surjective_vcons.
Qed.
Lemma vapp_ex {A m n} (xl: _ A (m + n)) : ∃yl zl, xl = yl +++ zl.
Proof. eexists _, _. apply vsepat_app. Qed.

Global Instance vapp_vsepat_iso {A} m n : Iso (uncurry vapp) (@vsepat A m n).
Proof.
  split; fun_ext.
  - move=> [xl ?]. by elim xl; [done|]=>/= ???->.
  - move=>/= ?. rewrite [vsepat _ _]surjective_pairing /=. induction m; [done|]=>/=.
    by rewrite [vsepat _ _]surjective_pairing /= IHm -surjective_vcons.
Qed.

(** [vsnoc] *)

Fixpoint vsnoc {A n} (xl: vec A n) (y: A) : vec A (S n) :=
  match xl with [#] => [#y] | x ::: xl' => x ::: vsnoc xl' y end.

Lemma vec_to_list_snoc {A n} (xl: vec A n) y : vec_to_list (vsnoc xl y) = xl ++ [y].
Proof. by elim xl; [done|]=>/= ???->. Qed.

(** [vapply] and [vfunsep] *)

Definition vapply {A B n} (fl: vec (B → A) n) (x: B) : vec A n := vmap (.$ x) fl.

Fixpoint vfunsep {A B n} : (B → vec A n) → vec (B → A) n :=
  match n with 0 => λ _, [#] | S _ => λ f, (vhd ∘ f) ::: vfunsep (vtl ∘ f) end.

Lemma vec_to_list_apply {A B n} (fl: vec (B → A) n) :
  vec_to_list ∘ vapply fl = lapply fl.
Proof. elim fl; [done|]=>/= ??? Eq. fun_ext=>/= ?. by rewrite -Eq. Qed.

Lemma vapply_lookup {A B n} (fl: vec (B → A) n) (i: fin n) :
  (.!!! i) ∘ vapply fl = fl !!! i.
Proof. by induction fl; inv_fin i. Qed.

Global Instance vapply_vfunsep_iso {A B n} : Iso (@vapply A B n) vfunsep.
Proof.
  split; fun_ext; [by elim; [done|]=>/= ???->|]. move=> f. fun_ext=>/= x.
  induction n=>/=; [|rewrite IHn /=]; move: (f x)=> xl; by inv_vec xl.
Qed.

Lemma vapply_funsep {A B n} (f: B → vec A n) : vapply (vfunsep f) = f.
Proof. by rewrite semi_iso'. Qed.

Lemma vfunsep_lookup {A B n} (f: B → vec A n) (i: fin n) :
  vfunsep f !!! i = (.!!! i) ∘ f.
Proof. by rewrite -{2}[f]vapply_funsep vapply_lookup. Qed.

(** [vinit] and [vlast] *)

Fixpoint vlast' {A n} (x: A) (yl: vec A n) : A :=
  match yl with [#] => x | y ::: yl' => vlast' y yl' end.
Definition vlast {A n} (xl: vec A (S n)) : A :=
  let '(x ::: xl') := xl in vlast' x xl'.

Fixpoint vinit' {A n} (x: A) (yl: vec A n) : vec A n :=
  match yl with [#] => [#] | y ::: yl' => x ::: vinit' y yl' end.
Definition vinit {A n} (xl: vec A (S n)) : vec A n :=
  let '(x ::: xl') := xl in vinit' x xl'.

Lemma vec_to_list_last_error {A n} (xl: vec A (S n)) :
  Some (vlast xl) = last_error xl.
Proof. inv_vec xl=>/= + xl. by elim xl=>/= *. Qed.

Lemma vec_to_list_init {A n} (xl: vec A (S n)) :
  vec_to_list (vinit xl) = removelast xl.
Proof. inv_vec xl=>/= + xl. by elim xl; [done|]=>/= ???->. Qed.

(** [vinsert] *)

Lemma vapply_insert {A B n} (fl: vec (B → A) n) i g :
  vapply (vinsert i g fl) = λ x, vinsert i (g x) (vapply fl x).
Proof.
  fun_ext=> ?. move: fl. elim i; [move=> ? fl; by inv_vec fl|]=> ?? IH fl.
  inv_vec fl=>/= ??. by rewrite IH.
Qed.

(** [vtake], [vdrop'] and [vbackmid] *)

Fixpoint vdrop' {A n} (i: fin n) : vec A n → vec A (pred (n - i)) :=
  match i with 0%fin => vtl | FS j => λ xl, vdrop' j (vtl xl) end.

Fixpoint vbackmid {A n} {i: fin n} :
    vec A i → A → vec A (pred (n - i)) → vec A n :=
  match i with
  | 0%fin => λ _ y zl, y ::: zl
  | FS j => λ xl y zl, vhd xl ::: vbackmid (vtl xl) y zl
  end.

Global Instance vbackmid_inj {A n i} : Inj3 (=) (=) (=) (=) (@vbackmid A n i).
Proof.
  elim i.
  - move=> ? xl ?? xl' ???. inv_vec xl. by inv_vec xl'=>/= /vcons_inj[->->].
  - move=> ?? IH xl ?? xl' ???. inv_vec xl=> ??.
    by inv_vec xl'=>/= ?? /vcons_inj[->/IH[->?]].
Qed.

Lemma vinsert_backmid {A n} (xl: vec A n) i y :
  vinsert i y xl = vbackmid (vtake i xl) y (vdrop' i xl).
Proof.
  move: xl. elim i; [move=> ? xl; by inv_vec xl|]=> ?? IH xl.
  inv_vec xl=>/= ??. f_equiv. apply IH.
Qed.

Lemma vapply_insert_backmid {A B n} (fl: vec (B → A) n) i g :
  vapply (vinsert i g fl) =
    vbackmid ∘ vapply (vtake i fl) ⊛ g ⊛ vapply (vdrop' i fl).
Proof.
  fun_ext. move: fl. elim i; [move=> ? fl; by inv_vec fl|]=> ?? IH fl.
  inv_vec fl=>/= ???. by rewrite IH.
Qed.

(** Iris *)

Lemma big_sepL_vlookup_acc {A n} {PROP: bi} (i: fin n) (xl: vec A n)
      (Φ: _ → _ → PROP) :
  ([∗ list] k ↦ x ∈ xl, Φ k x)%I ⊢
  Φ i (xl !!! i) ∗ (Φ i (xl !!! i) -∗ [∗ list] k ↦ x ∈ xl, Φ k x).
Proof. by apply big_sepL_lookup_acc, vlookup_lookup. Qed.

Lemma big_sepL_vlookup {A n} {PROP: bi} (i: fin n) (xl: vec A n)
    (Φ: nat → _ → PROP) `{!Absorbing (Φ i (xl !!! i))} :
  ([∗ list] k ↦ x ∈ xl, Φ k x)%I ⊢ Φ i (xl !!! i).
Proof. rewrite big_sepL_vlookup_acc. apply bi.sep_elim_l, _. Qed.

Lemma big_sepL_vinitlast {A n} {PROP: bi} (xl: vec A (S n)) (Φ: _ → _ → PROP) :
  ([∗ list] k ↦ x ∈ xl, Φ k x) ⊣⊢
  ([∗ list] k ↦ x ∈ vinit xl, Φ k x) ∗ Φ n (vlast xl).
Proof.
  inv_vec xl=>/= x xl. move: Φ x.
  elim xl; [move=> ??; by rewrite comm|]=>/= ??? IH Φ ?.
  by rewrite (IH (λ n, Φ (S n))) assoc.
Qed.

Lemma big_sepL_vtakedrop {A n} {PROP: bi} i (xl: vec A n) (Φ: _ → _ → PROP) :
  ([∗ list] k ↦ x ∈ xl, Φ k x) ⊣⊢
  ([∗ list] k ↦ x ∈ vtake i xl, Φ k x) ∗
    ([∗ list] k ↦ x ∈ vdrop i xl, Φ (i + k) x).
Proof.
  move: xl Φ. elim i. { move=> ? xl ?. inv_vec xl=>/= ??. by rewrite left_id. }
  move=> ?? IH xl ?. inv_vec xl=>/= ??. by rewrite -assoc IH.
Qed.

Lemma big_sepL_vtakemiddrop {A n} {PROP: bi} i (xl: vec A n) (Φ: _ → _ → PROP) :
  ([∗ list] k ↦ x ∈ xl, Φ k x) ⊣⊢
  ([∗ list] k ↦ x ∈ vtake i xl, Φ k x) ∗ Φ i (xl !!! i) ∗
    ([∗ list] k ↦ x ∈ vdrop' i xl, Φ (S i + k) x).
Proof.
  move: xl Φ. elim i. { move=> ? xl ?. inv_vec xl=>/= ??. by rewrite left_id. }
  move=> ?? IH xl ?. inv_vec xl=>/= ??. by rewrite -assoc IH.
Qed.

Lemma big_sepL_vbackmid {A n} {PROP: bi} (i: fin n)
    (xl: vec A i) y (zl: vec A _) (Φ: _ → _ → PROP) :
  ([∗ list] k ↦ x ∈ xl, Φ k x) ∗ Φ i y ∗ ([∗ list] k ↦ x ∈ zl, Φ (S i + k) x) ⊣⊢
  ([∗ list] k ↦ x ∈ vbackmid xl y zl, Φ k x)%I.
Proof.
  move: xl zl Φ. elim i. { move=> ? xl ??. inv_vec xl=>/=. by rewrite left_id. }
  move=>/= ?? IH xl ??. inv_vec xl=>/= ??. by rewrite -assoc IH.
Qed.
