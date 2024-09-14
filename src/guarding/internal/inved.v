From iris.prelude Require Import options.
From iris.algebra Require Export cmra updates proofmode_classes.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base ltac_tactics tactics coq_tactics reduction.

Class InternalPInv (A : Type) := pinv : A → Prop.
Global Hint Mode InternalPInv ! : typeclass_instances.
Global Instance: Params (@pinv) 2 := {}.

Inductive InvedProtocol (P: Type) :=
  | Nah : InvedProtocol P
  | Inved : P -> InvedProtocol P.
Global Arguments Inved {_} _.
Global Arguments Nah {_}.

Global Instance inved_protocol_equiv P `{Equiv P} : Equiv (InvedProtocol P) | 0 :=
    λ x y , match x with
      | Inved a => match y with
        | Inved b => a ≡ b
        | Nah => False
      end
      | Nah => match y with
        | Inved b => False
        | Nah => True
      end
    end.
    
Global Instance inved_protocol_pcore P `{PCore P} `{Unit P} : PCore (InvedProtocol P) | 0 :=
    λ x , match x with
      | Inved a => 
        match pcore a with
          | Some t => Some (Inved t)
          | None => Some (Inved ε)
        end
      | Nah => Some Nah
    end.

Global Instance inved_protocol_valid P `{InternalPInv P} `{Op P} : Valid (InvedProtocol P) | 0 :=
   λ x , match x with
    | Inved a => ∃ b , pinv (a ⋅ b)
    | Nah => True
   end.
   
Global Instance inved_protocol_op P `{InternalPInv P} `{Op P} : Op (InvedProtocol P) | 0 :=
   λ x y , 
    match x with
      | Inved a =>
        match y with
          | Inved b => Inved (a ⋅ b)
          | Nah => Inved a
        end
      | Nah => y
    end.
   
   (*
Lemma whatever (x y z : A)
  : (x ≡ z) -> (x ⋅ y ≡ z ⋅ y).
Proof.
  intros. setoid_rewrite H. trivial.
Qed.
*)

Lemma inved_incl_to_incl {P} 
    `{Equiv P, Op P, InternalPInv P}
    (a b : P) (mle : Inved a ≼ Inved b) : a ≼ b \/ b ≡ a.
Proof.
  unfold "≼".
  unfold "≼" in mle.
  destruct mle as [z mle].
  destruct z as [|p].
  - right. unfold "≡", inved_protocol_equiv, "⋅", inved_protocol_op in mle. trivial.
  - left. exists p.
    unfold "≡", inved_protocol_equiv, "⋅", inved_protocol_op in mle. trivial.
Qed.

Lemma incl_to_inved_incl {P} 
    `{Equiv P, Op P, InternalPInv P}
    (a b : P) (mle : a ≼ b) : Inved a ≼ Inved b.
Proof.
  unfold "≼".
  unfold "≼" in mle.
  destruct mle as [z mle].
  exists (Inved z).
  unfold "≡". unfold inved_protocol_equiv. unfold "⋅". unfold inved_protocol_op. trivial.
Qed.

Global Instance inved_protocol_equivalence
    {P}
    `{Equiv P}
    {equ: Equivalence (≡@{P})}
    : Equivalence (≡@{InvedProtocol P}).
Proof.
  split.
  - unfold Reflexive. intros x. unfold "≡", inved_protocol_equiv. destruct x; trivial.
  - unfold Symmetric. intros x y. unfold "≡", inved_protocol_equiv. destruct x, y; trivial.
  - unfold Transitive. intros x y z. 
      unfold "≡", inved_protocol_equiv. destruct x, y, z; trivial.
      + contradiction.
      + intros a1 a2. setoid_rewrite a1. trivial.
Qed.

Record InternalProtocolMixin P
    `{Equiv P, PCore P, Op P, Valid P, InternalPInv P, Unit P}
    {equ: @Equivalence P (≡)}
:= {
    protocol_ra_mixin: RAMixin P;
    (*protocol_unit_valid : ✓ (ε : P);
    protocol_pcore_unit : pcore (ε : P) ≡ Some (ε : P);*)
    protocol_unit_left_id : LeftId equiv (ε : P) op;
    internal_inv_proper: Proper ((≡) ==> impl) (@pinv P _);
}.

Definition inved_protocol_ra_mixin {P}
    `{Equiv P, PCore P, Op P, InternalPInv P, Valid P, Unit P}
    {equ: @Equivalence P (≡)}
    (internal_protocol_mixin: InternalProtocolMixin P) : RAMixin (InvedProtocol P).
Proof.
  destruct internal_protocol_mixin as [protocol_ra_mixin0
    protocol_unit_left_id0 internal_inv_proper0].
  have protocol_ra_mixin1 := protocol_ra_mixin0.
  destruct protocol_ra_mixin0 as [ra_op_proper ra_core_proper ra_validN_proper ra_assoc ra_comm ra_pcore_l ra_pcore_idemp ra_pcore_mono ra_valid_op_l].
  split.
 - intro inved_prot.
    + unfold Proper, equiv, "==>".
      unfold inved_protocol_equiv.
      intros a b. destruct a; destruct b; unfold "⋅", inved_protocol_op; intro e; destruct inved_prot; trivial; try contradiction.
      eapply ra_op_proper; trivial.
 - intros x y cx e p.
    destruct x as [|p0], y as [|p1].
    + exists Nah. split; trivial.
        destruct cx; trivial. unfold pcore, inved_protocol_pcore in p. inversion p.
    + inversion e.
    + inversion e.
    + unfold "≡", inved_protocol_equiv in e.
        destruct cx as [|p2].
        * unfold pcore, inved_protocol_pcore in p.
          unfold pcore, inved_protocol_pcore.
          destruct (pcore p0) as [p2|] eqn:l0.
          { inversion p. }
          destruct (pcore p1) as [p2|] eqn:l1.
          {
            assert (p1 ≡ p0) as esym. { symmetry. trivial. }
            have t := ra_core_proper p1 p0 p2 esym l1. 
            destruct t as [cy [t0 t1]].
            rewrite t0 in l0. inversion l0.
          }
          exists Nah. split; trivial.
        * 
        have t := ra_core_proper p0 p1 p2 e.
        unfold pcore, inved_protocol_pcore in p.
        destruct (pcore p0) as [p3|] eqn:q.

        ++ assert (Some p3 = Some p2) as pe. { f_equal. inversion p. trivial. }
          have t0 := t pe. destruct t0 as [cy [t0 t1]]. exists (Inved cy). split.
          ** unfold pcore. unfold inved_protocol_pcore. rewrite t0. trivial.
          ** unfold "≡", inved_protocol_equiv. trivial.
        ++ destruct (pcore p1) as [p3|] eqn:l1.
          {
            assert (p1 ≡ p0) as esym. { symmetry. trivial. }
            have t2 := ra_core_proper p1 p0 p3 esym l1. 
            destruct t2 as [cy [t0 t1]].
            rewrite t0 in q. discriminate.
          }
          unfold pcore, inved_protocol_pcore. rewrite l1.
          exists (Inved ε). split; trivial.
          inversion p. trivial.
    
 - unfold Proper, equiv, impl, "==>". intros x y ipe. unfold "✓", inved_protocol_valid.
    destruct x as [|p]; destruct y as [|p0].
    + trivial.
    + inversion ipe.
    + inversion ipe.
    + intro h. destruct h as [b ipb]. exists b.
      unfold inved_protocol_equiv in ipe.
      eapply internal_inv_proper0. 2: { apply ipb. }
      assert (p ⋅ b ≡ b ⋅ p) as X. { eapply ra_comm. }
      assert (p0 ⋅ b ≡ b ⋅ p0) as Y. { eapply ra_comm. }
      setoid_rewrite X. setoid_rewrite Y.
      eapply ra_op_proper. trivial.
 - unfold Assoc. intros x y z. destruct x, y, z; unfold "⋅"; unfold inved_protocol_op;
    unfold "≡"; unfold inved_protocol_equiv; trivial. (*apply ra_assoc.*)
 - unfold Comm. intros x y. destruct x, y; unfold "⋅"; unfold inved_protocol_op;
    unfold "≡"; unfold inved_protocol_equiv; trivial. (*apply ra_comm.*)
 - intros x cx pc. destruct x as [|p], cx as [|p0].
    + trivial.
    + inversion pc.
    + unfold "⋅", inved_protocol_op. unfold "≡", inved_protocol_equiv. trivial.
    + unfold "⋅". unfold inved_protocol_op. unfold "≡". unfold inved_protocol_equiv.
      unfold pcore, inved_protocol_pcore in pc. destruct (pcore p) as [p1|] eqn:pp.
      * have t := ra_pcore_l p p1 pp. inversion pc. subst p0. trivial.
      * inversion pc. subst p0. apply protocol_unit_left_id0.
 - intros x cx pc. destruct x as [|p], cx as [|p0].
    + unfold pcore. unfold inved_protocol_pcore.
        unfold "≡". unfold option_equiv. apply Some_Forall2. trivial.
    + inversion pc.
    + unfold pcore. unfold inved_protocol_pcore.
        unfold "≡". unfold option_equiv. apply Some_Forall2. trivial.
    + unfold pcore, inved_protocol_pcore in pc. destruct (pcore p) as [p1|] eqn:pp; try discriminate.
      { have t := ra_pcore_idemp p p1 pp.
          inversion pc. subst p0.
          unfold pcore, inved_protocol_pcore. destruct (pcore p1) eqn:pp1.
          * unfold "≡". unfold option_equiv. apply Some_Forall2. unfold "≡".
            unfold inved_protocol_equiv. inversion t. trivial.
          * inversion t.
      }
      {
        inversion pc. subst p0. unfold pcore. unfold inved_protocol_pcore.
        destruct (pcore ε) as [p3|] eqn:pe; trivial.
        have ll := ra_pcore_l ε p3 pe.
        generalize ll. rewrite ra_comm. rewrite protocol_unit_left_id0. intro mm.
        unfold "≡", option_equiv. apply Some_Forall2. unfold "≡", inved_protocol_equiv.
        trivial.
      }
 - intros x y cx mle pc. destruct x as [|p], y as [|p0].
    + exists Nah. split; trivial. unfold "≼". exists Nah. inversion pc. subst cx. trivial.
    + unfold pcore, inved_protocol_pcore. destruct (pcore p0) as [p2|].
        * exists (Inved p2). split; trivial. unfold "≼". exists (Inved p2).
              inversion pc. subst cx. unfold "⋅", inved_protocol_op.
              unfold "≡". unfold inved_protocol_equiv. trivial.
        * exists (Inved ε). split; trivial.
              unfold "≼". exists (Inved ε).
              inversion pc. subst cx. unfold "⋅", inved_protocol_op.
              unfold "≡". unfold inved_protocol_equiv. trivial.
    + unfold "≼" in mle. destruct mle as [z mle]. unfold "≡" in mle.
        unfold inved_protocol_equiv in mle. destruct z; unfold "⋅", inved_protocol_op in mle;
            contradiction.
    + have mle2 := inved_incl_to_incl _ _ mle. destruct mle2 as [mle2|yy].
        * destruct cx as [|p1].
          ++ unfold pcore, inved_protocol_pcore. destruct (pcore p0) as [p1|].
            ** exists (Inved p1). split; trivial. unfold "≼". exists (Inved p1).
                  inversion pc. unfold "⋅", inved_protocol_op.
                  unfold "≡". unfold inved_protocol_equiv. trivial.
            ** exists (Inved ε). split; trivial. unfold "≼". exists (Inved ε).
                  inversion pc. trivial.
          ++ unfold pcore, inved_protocol_pcore in pc.
              destruct (pcore p) as [p2|] eqn:pp; try discriminate.
              { inversion pc. subst p2.
                have t := ra_pcore_mono p p0 p1 mle2 pp.
                destruct t as [cy [t1 t2]].
                exists (Inved cy).
                split.
                ** unfold pcore, inved_protocol_pcore. rewrite t1. trivial.
                ** apply incl_to_inved_incl. trivial.
              }
              { inversion pc. subst p1. unfold pcore, inved_protocol_pcore.
                destruct (pcore p0) as [p1|].
                ** exists (Inved p1). split; trivial. apply incl_to_inved_incl.
                    unfold "≼". exists p1. rewrite protocol_unit_left_id0. trivial.
                ** exists (Inved ε). split; trivial. apply incl_to_inved_incl.
                    unfold "≼". exists ε. rewrite protocol_unit_left_id0. trivial.
              }
        * destruct cx as [|p1].
          ++ unfold pcore, inved_protocol_pcore. destruct (pcore p0) as [p1|].
            ** exists (Inved p1). split; trivial. unfold "≼". exists (Inved p1).
                  inversion pc. unfold "⋅", inved_protocol_op.
                  unfold "≡". unfold inved_protocol_equiv. trivial.
            ** exists (Inved ε). split; trivial. unfold "≼". exists (Inved ε).
                  inversion pc. trivial.
          ++ symmetry in yy. unfold pcore, inved_protocol_pcore in pc.
              destruct (pcore p) as [p2|] eqn:pp; try discriminate.
             { have j := ra_core_proper p p0 p2 yy pp. destruct j as [cy [j1 j2]].
                exists (Inved cy).
                split. { unfold pcore. unfold inved_protocol_pcore. rewrite j1. trivial. }
                inversion pc. subst p1.
                unfold "≼". exists Nah. unfold "⋅". unfold inved_protocol_op.
                unfold "≡", inved_protocol_equiv. symmetry. trivial.
             }
             { inversion pc. subst p1. destruct (pcore p0) as [p1|] eqn:pp0.
                ** assert (p0 ≡ p) as yy_sym by (symmetry; trivial).
                    have j := ra_core_proper p0 p p1 yy_sym pp0. destruct j as [cy [w v]].
                    rewrite w in pp. discriminate.
                ** unfold pcore, inved_protocol_pcore. rewrite pp0.
                    exists (Inved ε). split; trivial.
                    apply incl_to_inved_incl. unfold "≼". exists ε.
                      rewrite protocol_unit_left_id0. trivial.
             }
 - intros x y.  unfold "✓". unfold inved_protocol_valid. destruct x as [|p], y as [|p0].
    + unfold "⋅", inved_protocol_op. trivial.
    + unfold "⋅", inved_protocol_op. trivial.
    + unfold "⋅", inved_protocol_op. trivial.
    + assert (Inved p ⋅ Inved p0 = Inved (p ⋅ p0)) as X by trivial. rewrite X.
      intro eb.
      destruct eb as [b eb].
      exists (p0 ⋅ b).

      eapply internal_inv_proper0. 2: { apply eb. }

      symmetry. apply ra_assoc.
Qed.

Canonical Structure inved_protocolO
    {P}
    `{Equiv P}
    {equ: Equivalence (≡@{P})}
    := discreteO (InvedProtocol P).
    
Canonical Structure inved_protocolR {P}
    `{Equiv P, PCore P, Op P, InternalPInv P, Valid P, Unit P}
    {equ: Equivalence (≡@{P})}
    (internal_protocol_mixin: InternalProtocolMixin P)
    :=
   discreteR (InvedProtocol P) (inved_protocol_ra_mixin internal_protocol_mixin). 

Global Instance inved_protocol_unit P : Unit (InvedProtocol P) := Nah.


Definition inved_protocol_ucmra_mixin {P}
    `{Equiv P, PCore P, Op P, InternalPInv P, Valid P, Unit P}
    {equ: Equivalence (≡@{P})}
    (internal_protocol_mixin: InternalProtocolMixin P) :
      @UcmraMixin (InvedProtocol P)
       (cmra_dist (inved_protocolR internal_protocol_mixin))
       (inved_protocol_equiv P)
       (inved_protocol_pcore P)
       (inved_protocol_op P)
       (inved_protocol_valid P)
       (inved_protocol_unit P).
Proof.
  destruct internal_protocol_mixin.
  split.
  - unfold ε, "✓", cmra_valid, inved_protocol_unit, inved_protocol_valid. trivial.
  - unfold LeftId, ε. intros. unfold inved_protocol_unit.
      unfold "⋅". unfold cmra_op, inved_protocol_op. trivial.
  - unfold pcore, inved_protocol_pcore, ε, inved_protocol_unit. trivial.
Qed.

Canonical Structure inved_protocolUR {P}
    `{Equiv P, PCore P, Op P, InternalPInv P, Valid P, Unit P}
    {equ: Equivalence (≡@{P})}
    (internal_protocol_mixin: InternalProtocolMixin P) : ucmra
    :=
    @Ucmra'
      (InvedProtocol P)
       (inved_protocol_equiv P)
       (cmra_dist (inved_protocolR internal_protocol_mixin))
       (inved_protocol_pcore P)
       (inved_protocol_op P)
       (inved_protocol_valid P)
       (cmra_validN (inved_protocolR internal_protocol_mixin))
       (inved_protocol_unit P)
       (cmra_ofe_mixin (inved_protocolR internal_protocol_mixin))
       (cmra_mixin (inved_protocolR internal_protocol_mixin))
      (inved_protocol_ucmra_mixin internal_protocol_mixin).
