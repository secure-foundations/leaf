From lrust.typing Require Export type.
From lrust.typing Require Import typing lib.panic.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Definition option_to_psum {A} (o: option A) : () + (A + ∅) :=
  match o with None => inl () | Some x => (inr (inl x)) end.
Definition psum_to_option {A} (s: () + (A + ∅)) : option A :=
  match s with inl _ => None | inr (inl x) => Some x
    | inr (inr a) => absurd a end.
Global Instance option_psum_iso {A} : Iso (@psum_to_option A) option_to_psum.
Proof. split; fun_ext; case=>//; by case. Qed.

Section option.
  Context `{!typeG Σ}.

  (* Rust's Option<T> *)
  Definition option_ty {𝔄} (ty: type 𝔄) : type (optionₛ 𝔄) :=
    <{psum_to_option: (Σ! [(); 𝔄])%ST → optionₛ 𝔄}> (Σ! +[(); ty])%T.

  Lemma option_resolve {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ →
    resolve E L (option_ty ty) (λ o, match o with None => True | Some o => Φ o end).
  Proof. move=> ?. eapply resolve_impl; [solve_typing|]. by case. Qed.

  Lemma option_resolve_just {𝔄} E L (ty: type 𝔄) :
    resolve E L ty (const True) → resolve E L (option_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma option_real {𝔄 𝔅} (f: 𝔄 → 𝔅) ty E L :
    real E L ty f → real (𝔅:=optionₛ _) E L (option_ty ty) (option_map f).
  Proof.
    move=> ?. eapply real_eq.
    { apply mod_ty_real; [apply _|].
      apply (real_compose (𝔅:=Σ! [()%ST;_]) (ℭ:=optionₛ _) psum_to_option).
      solve_typing. }
    fun_ext. by case.
  Qed.

  Lemma option_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (option_ty ty) (option_ty ty') (option_map f).
  Proof. move=> ?. eapply subtype_eq; [solve_typing|]. fun_ext. by case. Qed.

  Lemma option_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g →
    eqtype E L (option_ty ty) (option_ty ty') (option_map f) (option_map g).
  Proof. move=> [??]. split; by apply option_subtype. Qed.

  (* Variant indices. *)
  Definition none := 0%nat.
  Definition some := 1%nat.

  Definition option_as_uniq : val :=
    fn: ["o"] :=
      let: "o'" := !"o" in let: "r" := new [ #2] in
    withcont: "k":
      case: !"o'" of
      [ "r" <-{Σ none} ();; jump: "k" []
      ; "r" <-{Σ some} "o'" +ₗ #1;; jump: "k" []]
    cont: "k" [] :=
      delete [ #1; "o"];; return: ["r"].

  (* Rust's Option::as_mut *)
  Lemma option_as_uniq_type {𝔄} (ty: type 𝔄) :
    typed_val option_as_uniq
      (fn<α>(∅; &uniq{α} (option_ty ty)) → option_ty (&uniq{α} ty))
      (λ (post: pred' (optionₛ (_*_))) '-[a], match a with
        | (Some a, Some a') => post (Some (a, a'))
        | (None, None) => post None
        | _ => True
        end).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[o[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
      iApply type_new; [solve_typing..|]. intro_subst_as (r).
      iApply (type_cont_norec [] (λ _, +[o ◁ box _; r ◁ box _])).
      { intro_subst. via_tr_impl.
        { iApply (type_case_uniq_inner +[_;_] -[_;_]); [solve_extract|solve_typing|].
          rewrite/= right_id. iSplitL.
          - iApply (type_sum_unit +[(); &uniq{_} _]%T 0%fin);
              [done|solve_extract|solve_typing..|].
            iApply type_jump; [solve_typing|solve_extract|solve_typing].
          - iApply (type_sum_assign +[(); &uniq{_} _]%T 1%fin);
              [done|solve_extract|solve_typing..|].
            iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
        move=>/= ??. exact id. }
      iIntros (? vl). inv_vec vl. simpl_subst.
      iApply type_delete; [solve_extract|solve_typing..|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    move=>/= ?[[[?|][?|]][]]//=. by move=> ??[=<-].
  Qed.

  Definition option_unwrap_or {𝔄} (ty: type 𝔄) : val :=
    fn: ["o"; "def"] :=
      case: !"o" of
      [ delete [ #(S ty.(ty_size)); "o"];; return: ["def"]
      ; letalloc: "r" <-{ty.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S ty.(ty_size)); "o"];; delete [ #ty.(ty_size); "def"];;
        return: ["r"]].

  (* Rust's Option::unwrap_or *)
  Lemma option_unwrap_or_type {𝔄} (ty: type 𝔄) :
    typed_val (option_unwrap_or ty) (fn(∅; option_ty ty, ty) → ty)
      (λ post '-[o; d], match o with Some a => post a | None => post d end).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[?[?[]]]. simpl_subst. via_tr_impl.
    { iApply (type_case_own +[_;_] -[inl _; inr _]); [solve_extract|].
      rewrite/= right_id. iSplitL.
      - iApply type_delete; [solve_extract|simpl; lia..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - iApply type_letalloc_n; [solve_extract|solve_typing|]. intro_subst.
        iApply (type_delete (Π! +[int;↯ _;_]%T)); [solve_extract|simpl; lia..|].
        iApply type_delete; [solve_extract|done..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    move=>/= ?[[?|][?[]]]//=.
  Qed.

  Definition option_unwrap {𝔄} (ty: type 𝔄) : val :=
    fn: ["o"] :=
      case: !"o" of
      [ let: "panic" := panic in
        letcall: "emp" := "panic" [] in case: !"emp" of []
      ; letalloc: "r" <-{ty.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S ty.(ty_size)); "o"];; return: ["r"]].

  (* Rust's Option::unwrap *)
  Lemma option_unwrap_type {𝔄} (ty: type 𝔄) :
    typed_val (option_unwrap ty) (fn(∅; option_ty ty) → ty)
      (λ post '-[o], match o with Some a => post a | None => False end).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[?[]]. simpl_subst. via_tr_impl.
    { iApply (type_case_own +[_;_] -[inl _; inr _]); [solve_extract|].
      rewrite/= right_id. iSplitL.
      - iApply type_val; [by apply panic_type|]. intro_subst.
        iApply (type_letcall ()); [solve_typing|solve_extract|solve_typing|].
        intro_subst. iApply (type_case_own +[] -[]); [solve_extract|done].
      - iApply type_letalloc_n; [solve_extract|solve_typing|]. intro_subst.
        iApply (type_delete (Π! +[int;↯ _;_]%T)); [solve_extract|simpl; lia..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    move=>/= ?[[?|][]]//=.
  Qed.
End option.

Global Hint Resolve option_resolve | 5 : lrust_typing.
Global Hint Resolve option_resolve_just option_real option_subtype option_eqtype
  : lrust_typing.
