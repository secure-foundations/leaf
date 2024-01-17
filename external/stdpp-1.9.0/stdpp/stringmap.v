(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of strings [string]. The implementation uses radix-2
search trees (uncompressed Patricia trees) as implemented in the file [pmap]
and guarantees logarithmic-time operations. *)
From stdpp Require Export fin_maps pretty.
From stdpp Require Import gmap.
From stdpp Require Import options.

Notation stringmap := (gmap string).
Notation stringset := (gset string).

(** * Generating fresh strings *)
Section stringmap.
Local Open Scope N_scope.
Let R {A} (s : string) (m : stringmap A) (n1 n2 : N) :=
  n2 < n1 ∧ is_Some (m !! (s +:+ pretty (n1 - 1))).
Lemma fresh_string_step {A} s (m : stringmap A) n x :
  m !! (s +:+ pretty n) = Some x → R s m (1 + n) n.
Proof. split; [lia|]. replace (1 + n - 1) with n by lia; eauto. Qed.
Lemma fresh_string_R_wf {A} s (m : stringmap A) : wf (R s m).
Proof.
  induction (map_wf m) as [m _ IH]. intros n1; constructor; intros n2 [Hn Hs].
  specialize (IH _ (delete_subset m (s +:+ pretty (n2 - 1)) Hs) n2).
  cut (n2 - 1 < n2); [|lia]. clear n1 Hn Hs; revert IH; generalize (n2 - 1).
  intros n1. induction 1 as [n2 _ IH]; constructor; intros n3 [??].
  apply IH; [|lia]; split; [lia|].
  by rewrite lookup_delete_ne by (intros ?; simplify_eq/=; lia).
Qed.
Definition fresh_string_go {A} (s : string) (m : stringmap A) (n : N)
    (go : ∀ n', R s m n' n → string) : string :=
  let s' := s +:+ pretty n in
  match Some_dec (m !! s') with
  | inleft (_↾Hs') => go (1 + n)%N (fresh_string_step s m n _ Hs')
  | inright _ => s'
  end.
Definition fresh_string {A} (s : string) (m : stringmap A) : string :=
  match m !! s with
  | None => s
  | Some _ =>
     Fix_F _ (fresh_string_go s m) (wf_guard 32 (fresh_string_R_wf s m) 0)
  end.
Lemma fresh_string_fresh {A} (m : stringmap A) s : m !! fresh_string s m = None.
Proof.
  unfold fresh_string. destruct (m !! s) as [a|] eqn:Hs; [clear a Hs|done].
  generalize 0 (wf_guard 32 (fresh_string_R_wf s m) 0); revert m.
  fix FIX 3; intros m n [?]; simpl; unfold fresh_string_go at 1; simpl.
  destruct (Some_dec (m !! _)) as [[??]|?]; auto.
Qed.
Definition fresh_string_of_set (s : string) (X : stringset) : string :=
  fresh_string s (mapset.mapset_car X).
Lemma fresh_string_of_set_fresh (X : stringset) s : fresh_string_of_set s X ∉ X.
Proof. apply eq_None_ne_Some, fresh_string_fresh. Qed.

Fixpoint fresh_strings_of_set
    (s : string) (n : nat) (X : stringset) : list string :=
  match n with
  | 0 => []
  | S n =>
     let x := fresh_string_of_set s X in
     x :: fresh_strings_of_set s n ({[ x ]} ∪ X)
  end%nat.
End stringmap.
