From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing lib.option.

(* Typing "problem case #3" from:
     http://smallcultfollowing.com/babysteps/blog/2016/04/27/non-lexical-lifetimes-introduction/

  Differences with the original implementation:

   We ignore dropping.
   We have to add a Copy bound on the key type.
   We do not support panic, hence we do not support option::unwrap. We use
   unwrap_or as a replacement.
*)

Section non_lexical.
  Context `{!typeG Σ} (HashMap K V : type) `{!Copy K}
          (defaultv get_mut insert: val).

  Hypothesis defaultv_type :
    typed_val defaultv (fn(∅) → V).

  Hypothesis get_mut_type :
    typed_val get_mut (fn(∀ '(α, β), ∅; &uniq{α} HashMap, &shr{β} K) →
                       option (&uniq{α} V)).

  Hypothesis insert_type :
    typed_val insert (fn(∀ α, ∅; &uniq{α} HashMap, K, V) → option V).

  Definition get_default : val :=
    fn: ["map"; "key"] :=
      let: "get_mut" := get_mut in
      let: "map'" := !"map" in

      Newlft;;

      Newlft;;
      letalloc: "map0" <- "map'" in
      Share;;
      letalloc: "key0" <- "key" in
      letcall: "o" := "get_mut" ["map0"; "key0"]%E in
      Endlft;;
    withcont: "k":
      case: !"o" of
      [ (* None *)
        Endlft;;

        let: "insert" := insert in
        Newlft;;
        letalloc: "map0" <- "map'" in
        letalloc: "key0" <-{K.(ty_size)} !"key" in
        let: "defaultv" := defaultv in
        letcall: "default0" := "defaultv" [] in
        letcall: "old" := "insert" ["map0"; "key0"; "default0"]%E in
        Endlft;;
        delete [ #(option V).(ty_size); "old"];; (* We should drop here. *)

        Newlft;;
        letalloc: "map0" <- "map'" in
        Share;;
        letalloc: "key0" <- "key" in
        letcall: "r'" := "get_mut" ["map0"; "key0"]%E in
        Endlft;;
        let: "unwrap" := option_unwrap (&uniq{static}V) in
        letcall: "r" := "unwrap" ["r'"]%E in
        "k" ["r"];

        (* Some *)
        letalloc: "r" <-{1} !("o" +ₗ #1) in
        "k" ["r"]
      ]
    cont: "k" ["r"] :=
      delete [ #(option (&uniq{static}V)).(ty_size); "o"];;
      delete [ #1; "map"];; delete [ #K.(ty_size); "key"];; (* We should drop key here *)
      return: ["r"].

    Lemma get_default_type :
      typed_val get_default (fn(∀ m, ∅; &uniq{m} HashMap, K) → &uniq{m} V).
    Proof.
      intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
        iIntros (m ϝ ret p). inv_vec p=>map key. simpl_subst.
      iApply type_let; [iApply get_mut_type|solve_typing|].
        iIntros (get_mut'). simpl_subst.
      iApply type_deref; [solve_typing..|]. iIntros (map'). simpl_subst.
      iApply (type_newlft [m]). iIntros (κ).
      iApply (type_newlft [ϝ]). iIntros (α).
      iApply (type_letalloc_1 (&uniq{κ}_)); [solve_typing..|]. iIntros (map0). simpl_subst.
      iApply (type_share key _ α); [solve_typing..|].
      iApply (type_letalloc_1 (&shr{α}K)); [solve_typing..|]. iIntros (key0). simpl_subst.
      iApply (type_letcall (κ, α)); [solve_typing..|]. iIntros (o). simpl_subst.
      iApply type_endlft.
      iApply (type_cont [_] [ϝ ⊑ₗ []]
            (λ r, [o ◁ box (Π[uninit 1;uninit 1]); map ◁ box (uninit 1);
                   key ◁ box K; (r!!!0%fin:val) ◁ box (&uniq{m} V)])).
      { iIntros (k). simpl_subst.
        iApply type_case_own;
          [solve_typing| constructor; [|constructor; [|constructor]]; left].
        - iApply type_endlft.
          iApply type_let; [iApply insert_type|solve_typing|].
            iIntros (insert'). simpl_subst.
          iApply (type_newlft [ϝ]). iIntros (β). clear map0 key0.
          iApply (type_letalloc_1 (&uniq{β}_)); [solve_typing..|].
            iIntros (map0). simpl_subst.
          iApply (type_letalloc_n _ (box K)); [solve_typing..|]. iIntros (key0). simpl_subst.
          iApply type_let; [iApply defaultv_type|solve_typing|].
            iIntros (defaultv'). simpl_subst.
          iApply (type_letcall ()); [solve_typing..|]. iIntros (default0). simpl_subst.
          iApply (type_letcall β); [solve_typing..|]. iIntros (old). simpl_subst.
          iApply type_endlft.
          iApply type_delete; [solve_typing..|].
          iApply (type_newlft [ϝ]). iIntros (γ). clear map0 key0.
          iApply (type_letalloc_1 (&uniq{m}_)); [solve_typing..|].
            iIntros (map0). simpl_subst.
          iApply (type_share key _ γ); [solve_typing..|].
          iApply (type_letalloc_1 (&shr{γ}K)); [solve_typing..|].
            iIntros (key0). simpl_subst.
          iApply (type_letcall (m, γ)); [solve_typing..|]. iIntros (r'). simpl_subst.
          iApply type_endlft.
          iApply type_let; [iApply (option_unwrap_type (&uniq{m}V))|solve_typing|].
            iIntros (unwrap'). simpl_subst.
          iApply (type_letcall ()); [solve_typing..|]. iIntros (r). simpl_subst.
          iApply type_jump; solve_typing.
        - iApply type_equivalize_lft.
          iApply (type_letalloc_n (&uniq{m}V) (own_ptr _ (&uniq{m}V))); [solve_typing..|].
            iIntros (r). simpl_subst.
          iApply type_jump; solve_typing. }
      iIntros "!> *". inv_vec args=>r. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    Qed.
End non_lexical.
