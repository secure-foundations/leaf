From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Definition list_to_psum {A} (xl: list A) : () + (A * list A + ∅) :=
  match xl with [] => inl () | x :: xl' => (inr (inl (x, xl'))) end.
Definition psum_to_list {A} (s: () + (A * list A + ∅)) : list A :=
  match s with inl _ => [] | inr (inl (x, xl')) => x :: xl'
    | inr (inr a) => absurd a end.
Global Instance list_psum_iso {A} : Iso (@psum_to_list A) list_to_psum.
Proof. split; fun_ext; repeat case=>//. Qed.

Section list.
  Context `{!typeG Σ}.

  Definition list_map {𝔄} (ty: type 𝔄) (ty': type (listₛ 𝔄)) : type (listₛ 𝔄) :=
    <{psum_to_list: (Σ! [(); (𝔄 * listₛ 𝔄)])%ST → listₛ 𝔄}> (Σ! +[(); ty * box ty'])%T.
End list.

(* In Rust:
  enum List<T> { Nil, Cons(T, Box<List<T>>) }
*)
Notation list_ty ty := (fix_ty (list_map ty)).
Notation list_cons_ty ty := (ty * box (list_ty ty))%T.
Notation list_xsum_ty ty := (Σ! +[(); list_cons_ty ty])%T.

Section typing.
  Context `{!typeG Σ}.

  Lemma list_resolve {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (list_ty ty) (lforall Φ).
  Proof.
    move=> ?. apply fix_resolve=> ??. eapply resolve_impl; [solve_typing|]. by case.
  Qed.

  Lemma list_resolve_just {𝔄} E L (ty: type 𝔄) :
    resolve E L ty (const True) → resolve E L (list_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma list_real {𝔄 𝔅} ty (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (list_ty ty) (map f).
  Proof.
    move=> ?. apply fix_real=> ??. eapply real_eq.
    { apply mod_ty_real; [apply _|].
      apply (real_compose (𝔅:=Σ! [();(_*listₛ _)]%ST) (ℭ:=listₛ _) psum_to_list).
      solve_typing. }
    fun_ext. by case.
  Qed.

  Lemma list_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (list_ty ty) (list_ty ty') (map f).
  Proof.
    move=> ?. apply fix_subtype=> ???. eapply subtype_eq; [solve_typing|].
    fun_ext. by case.
  Qed.

  Lemma list_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (list_ty ty) (list_ty ty') (map f) (map g).
  Proof. move=> [??]. by split; apply list_subtype. Qed.
End typing.

Global Hint Resolve list_resolve | 5 : lrust_typing.
Global Hint Resolve list_resolve_just list_real list_subtype list_eqtype
  : lrust_typing.
