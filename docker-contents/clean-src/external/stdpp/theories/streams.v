From stdpp Require Export tactics.
From stdpp Require Import options.

Declare Scope stream_scope.
Delimit Scope stream_scope with stream.
Global Open Scope stream_scope.

CoInductive stream (A : Type) : Type := scons : A → stream A → stream A.
Global Arguments scons {_} _ _ : assert.
Infix ":.:" := scons (at level 60, right associativity) : stream_scope.
Bind Scope stream_scope with stream.

Definition shead {A} (s : stream A) : A := match s with x :.: _ => x end.
Definition stail {A} (s : stream A) : stream A := match s with _ :.: s => s end.

CoInductive stream_equiv' {A} (s1 s2 : stream A) : Prop :=
  scons_equiv' :
    shead s1 = shead s2 → stream_equiv' (stail s1) (stail s2) →
    stream_equiv' s1 s2.
Global Instance stream_equiv {A} : Equiv (stream A) := stream_equiv'.

Reserved Infix "!.!" (at level 20).
Fixpoint slookup {A} (i : nat) (s : stream A) : A :=
  match i with O => shead s | S i => stail s !.! i end
where "s !.! i" := (slookup i s).

Global Instance stream_fmap : FMap stream := λ A B f,
  cofix go s := f (shead s) :.: go (stail s).

Fixpoint stake {A} (n : nat) (s : stream A) :=
  match n with 0 => [] | S n => shead s :: stake n (stail s) end.
CoFixpoint srepeat {A} (x : A) : stream A := x :.: srepeat x.

Section stream_properties.
Context {A : Type}.
Implicit Types x y : A.
Implicit Types s t : stream A.

Lemma scons_equiv s1 s2 : shead s1 = shead s2 → stail s1 ≡ stail s2 → s1 ≡ s2.
Proof. by constructor. Qed.
Global Instance equal_equivalence : Equivalence (≡@{stream A}).
Proof.
  split.
  - now cofix FIX; intros ?; constructor.
  - now cofix FIX; intros ?? [??]; constructor.
  - cofix FIX; intros ??? [??] [??]; constructor; etrans; eauto.
Qed.
Global Instance scons_proper x : Proper ((≡) ==> (≡)) (scons x).
Proof. by constructor. Qed.
Global Instance shead_proper : Proper ((≡) ==> (=@{A})) shead.
Proof. by intros ?? [??]. Qed.
Global Instance stail_proper : Proper ((≡) ==> (≡@{stream A})) stail.
Proof. by intros ?? [??]. Qed.
Global Instance slookup_proper i : Proper ((≡@{stream A}) ==> (=)) (slookup i).
Proof. by induction i as [|i IH]; intros s1 s2 Hs; simpl; rewrite Hs. Qed.
End stream_properties.
