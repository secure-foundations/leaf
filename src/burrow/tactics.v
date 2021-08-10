Tactic Notation "full_generalize" constr(t) "as" simple_intropattern(name) :=
  let EQ := fresh in
  let name1 := fresh in
  assert (exists x , x = t) as EQ by (exists t; trivial); destruct EQ as [name1];
    try (rewrite <- EQ);
    (repeat match reverse goal with  
    | [H : context[t] |- _ ] => rewrite <- EQ in H
    end); clear EQ; try (clear name); rename name1 into name.
