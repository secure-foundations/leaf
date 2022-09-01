From Coq Require Import Ascii.
From Coq Require Export String.
From stdpp Require Export list.
From stdpp Require Import countable.
From stdpp Require Import options.

(* To avoid randomly ending up with String.length because this module is
imported hereditarily somewhere. *)
Notation length := List.length.

(** * Fix scopes *)
Global Open Scope string_scope.
(* Make sure [list_scope] has priority over [string_scope], so that
   the "++" notation designates list concatenation. *)
Global Open Scope list_scope.
Infix "+:+" := String.append (at level 60, right associativity) : stdpp_scope.
Global Arguments String.append : simpl never.

(** * Decision of equality *)
Global Instance ascii_eq_dec : EqDecision ascii := ascii_dec.
Global Instance string_eq_dec : EqDecision string.
Proof. solve_decision. Defined.
Global Instance string_app_inj s1 : Inj (=) (=) (String.append s1).
Proof. intros ???. induction s1; simplify_eq/=; f_equal/=; auto. Qed.

Global Instance string_inhabited : Inhabited string := populate "".

(* Reverse *)
Fixpoint string_rev_app (s1 s2 : string) : string :=
  match s1 with
  | "" => s2
  | String a s1 => string_rev_app s1 (String a s2)
  end.
Definition string_rev (s : string) : string := string_rev_app s "".

Definition is_nat (x : ascii) : option nat :=
  match x with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | _ => None
  end%char.

(* Break a string up into lists of words, delimited by white space *)
Definition is_space (x : Ascii.ascii) : bool :=
  match x with
  | "009" | "010" | "011" | "012" | "013" | " " => true | _ => false
  end%char.

Fixpoint words_go (cur : option string) (s : string) : list string :=
  match s with
  | "" => option_list (string_rev <$> cur)
  | String a s =>
     if is_space a then option_list (string_rev <$> cur) ++ words_go None s
     else words_go (Some (from_option (String a) (String a "") cur)) s
  end.
Definition words : string → list string := words_go None.

Ltac words s :=
  match type of s with
  | list string => s
  | string => eval vm_compute in (words s)
  end.

(** * Encoding and decoding *)
(** In order to reuse or existing implementation of radix-2 search trees over
positive binary naturals [positive], we define an injection [string_to_pos]
from [string] into [positive]. *)
Fixpoint digits_to_pos (βs : list bool) : positive :=
  match βs with
  | [] => xH
  | false :: βs => (digits_to_pos βs)~0
  | true :: βs => (digits_to_pos βs)~1
  end%positive.
Definition ascii_to_digits (a : Ascii.ascii) : list bool :=
  match a with
  | Ascii.Ascii β1 β2 β3 β4 β5 β6 β7 β8 => [β1;β2;β3;β4;β5;β6;β7;β8]
  end.
Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => xH
  | String a s => string_to_pos s ++ digits_to_pos (ascii_to_digits a)
  end%positive.
Fixpoint digits_of_pos (p : positive) : list bool :=
  match p with
  | xH => []
  | p~0 => false :: digits_of_pos p
  | p~1 => true :: digits_of_pos p
  end%positive.
Fixpoint ascii_of_digits (βs : list bool) : ascii :=
  match βs with
  | [] => zero
  | β :: βs => Ascii.shift β (ascii_of_digits βs)
  end.
Fixpoint string_of_digits (βs : list bool) : string :=
  match βs with
  | β1 :: β2 :: β3 :: β4 :: β5 :: β6 :: β7 :: β8 :: βs =>
     String (ascii_of_digits [β1;β2;β3;β4;β5;β6;β7;β8]) (string_of_digits βs)
  | _ => EmptyString
  end.
Definition string_of_pos (p : positive) : string :=
  string_of_digits (digits_of_pos p).
Lemma string_of_to_pos s : string_of_pos (string_to_pos s) = s.
Proof.
  unfold string_of_pos. by induction s as [|[[][][][][][][][]]]; f_equal/=.
Qed.
Global Program Instance string_countable : Countable string := {|
  encode := string_to_pos; decode p := Some (string_of_pos p)
|}.
Solve Obligations with naive_solver eauto using string_of_to_pos with f_equal.
Lemma ascii_of_to_digits a : ascii_of_digits (ascii_to_digits a) = a.
Proof. by destruct a as [[][][][][][][][]]. Qed.
Global Instance ascii_countable : Countable ascii :=
  inj_countable' ascii_to_digits ascii_of_digits ascii_of_to_digits.
