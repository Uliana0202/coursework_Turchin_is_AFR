Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import Lia.
Import ListNotations.

Require Import Turchin_Defs.
Require Import Repetition_Is_Turchin.
Require Import Turchin_Growth.

Section Main.
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.

  Variable G : grammar letter.
  Variable G_NonShort : NonShortening letter G.

  Definition is_Turchin_AFR (f : nat -> word letter) : Prop :=
    exists i j, is_turchin_pair G f i j.

  Theorem Turchin_AFR_Complete : 
    forall (f : nat -> word letter),
    chain G f ->
    (forall n, f n <> []) -> 
    is_Turchin_AFR f.
  Proof.
    intros f Hchain Hnonil.
    apply NNPP.
    intro H_not_AFR.
    
    assert (H_bad : forall i j, i < j -> ~ is_turchin_pair G f i j).
    {
      intros i0 j0 Hlt Hpair.
      apply H_not_AFR.
      exists i0, j0.
      assumption.
    }

    pose proof (Bad_Sequence_Is_Bounded letter G Finite_Sigma Is_Finite G_NonShort f Hchain Hnonil H_bad) as [Bound H_bound_len].

    assert (H_repetition : exists i j, i < j /\ f i = f j).
    {
      apply (Bounded_Chain_Has_Repetition letter Finite_Sigma Is_Finite f Bound). 
      assumption.
    }
    
    destruct H_repetition as [i [j [Hlt Heq]]].
    
    assert (H_is_turchin : is_turchin_pair G f i j).
    {
      apply (Repetition_Is_Turchin _ G f i j).
      - assumption.
      - assumption.
      - apply Hnonil.
      - assumption.
    }
    
    apply (H_bad i j Hlt).
    assumption.
    
  Qed.

End Main.