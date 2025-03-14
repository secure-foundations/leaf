From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Notation predl_trans'_map 𝔄l 𝔅 := (predl_trans' 𝔄l 𝔅 → predl_trans' 𝔄l 𝔅).

Class MonoTrans' {𝔄l 𝔅} (tr: predl_trans' 𝔄l 𝔅) : Prop := mono_trans':
  ∀post post': pred' 𝔅, (∀b, post b → post' b) →
    ∀al, tr post al → tr post' al.

Class MonoTrans'Map {𝔄l 𝔅} (Tr: predl_trans'_map 𝔄l 𝔅) : Prop := mono_trans'_map:
  ∀tr tr': predl_trans' 𝔄l 𝔅, (∀post al, tr post al → tr' post al) →
    ∀post al, Tr tr post al → Tr tr' post al.

Definition trans'_gfp {𝔄l 𝔅} (Tr: predl_trans'_map 𝔄l 𝔅) : predl_trans' 𝔄l 𝔅 :=
  λ post al, ∃tr: predl_trans' 𝔄l 𝔅, MonoTrans' tr ∧
    (∀post' al', tr post' al' → Tr tr post' al') ∧ tr post al.
Arguments trans'_gfp : simpl never.

Lemma fp_to_trans'_gfp {𝔄l 𝔅} (Tr: predl_trans'_map 𝔄l 𝔅)
    tr `{!MonoTrans' tr} post al :
  (∀post' al', tr post' al' → Tr tr post' al') →
  tr post al → trans'_gfp Tr post al.
Proof. move=> ??. by exists tr. Qed.

Lemma trans'_gfp_unfold {𝔄l 𝔅} Tr `{Mono: !@MonoTrans'Map 𝔄l 𝔅 Tr} post al :
  trans'_gfp Tr post al → Tr (trans'_gfp Tr) post al.
Proof.
  move=> [tr[?[Imp ?]]]. eapply Mono; [|by apply Imp]=> ???. by exists tr.
Qed.

Lemma trans'_gfp_fold {𝔄l 𝔅} Tr `{Mono: !@MonoTrans'Map 𝔄l 𝔅 Tr}
    `{∀tr, MonoTrans' (Tr tr)} post al :
  Tr (trans'_gfp Tr) post al → trans'_gfp Tr post al.
Proof.
  move=> ?. exists (Tr (trans'_gfp Tr)). split; [done|]. split; [|done]=> ??.
  apply Mono=> ???. by apply trans'_gfp_unfold.
Qed.

Lemma trans'_gfp_mono {𝔄l 𝔅} (Tr: predl_trans'_map 𝔄l 𝔅) (post post': pred' _) al :
  (∀b, post b → post' b) → trans'_gfp Tr post al → trans'_gfp Tr post' al.
Proof.
  move=> ?[tr[Mono[??]]]. exists tr. do 2 (split; [done|]). by eapply Mono.
Qed.