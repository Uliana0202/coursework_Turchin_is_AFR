Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section Definitions.
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.
  
  Definition word := list letter.

  Definition rule := (letter * word)%type.

  Definition grammar := list rule.
  Variable G : grammar.

  Inductive step : word -> word -> Prop :=
    | step_intro : forall (l : letter) (rhs tail : word),
        In (l, rhs) G ->
        (* l :: tail - исходное слово  *)
        (* rhs ++ tail - новое слово *)
        step (l :: tail) (rhs ++ tail).

  Definition chain (f : nat -> word) : Prop :=
    forall n, step (f n) (f (S n)).
    
  Definition is_suffix (s l : word) : Prop :=
    exists p, l = p ++ s.

  Definition tail_preserved (f : nat -> word) (n : nat) (suffix : word) : Prop :=
    exists (l : letter) (rhs middle : word),
      In (l, rhs) G /\
      f n = l :: middle ++ suffix /\       (* до шага *)
      f (S n) = rhs ++ middle ++ suffix.   (* после шага *)

  Definition is_turchin_pair (f : nat -> word) (i j : nat) : Prop :=
    i < j /\
    exists (v v' w' : word),
      v <> [] /\
      f i = v ++ w' /\
      f j = v ++ v' ++ w' /\
      (* w' неизменна на каждом шаге от i до j-1 *)
      (forall k, i <= k < j -> tail_preserved f k w').
    
  Definition almost_full (R : word -> word -> Prop) : Prop :=
    forall (f : nat -> word),
      chain f -> 
      exists i j, i < j /\ R (f i) (f j).

End Definitions.

Arguments step {letter}.
Arguments chain {letter}.
Arguments is_suffix {letter}.
Arguments tail_preserved {letter}.
Arguments is_turchin_pair {letter}.