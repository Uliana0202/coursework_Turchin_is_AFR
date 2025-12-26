(*
rm *.vo *.vok *.vos *.glob 
coqc -Q . Turchin Turchin_Defs.v
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section Definitions.
  (* Тип для буквы *)
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  
  (* Конечность алфавита *)
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.
  
  Definition word := list letter.

  Definition rule := (letter * word)%type.

  Definition grammar := list rule.
  Variable G : grammar.

  Inductive step : word -> word -> Prop :=
    | step_intro : forall (l : letter) (rhs tail : word),
        In (l, rhs) G ->
        (* l :: tail — это исходное слово (gamma ++ omega) *)
        (* rhs ++ tail — это новое слово (omega' ++ omega) *)
        step (l :: tail) (rhs ++ tail).

  Definition chain (f : nat -> word) : Prop :=
    forall n, step (f n) (f (S n)).
    
  Definition is_suffix (s l : word) : Prop :=
    exists p, l = p ++ s.

  Definition tail_preserved (f : nat -> word) (n : nat) (suffix : word) : Prop :=
    exists (l : letter) (rhs middle : word),
      In (l, rhs) G /\
      f n = l :: middle ++ suffix /\       (* До шага *)
      f (S n) = rhs ++ middle ++ suffix.   (* После шага *)

  Definition is_turchin_pair (f : nat -> word) (i j : nat) : Prop :=
    i < j /\
    exists (phi psi theta : word),
      phi <> [] /\                          (* |v| > 0 *)
      f i = phi ++ theta /\
      f j = phi ++ psi ++ theta /\
      (* theta неизменна на каждом шаге от i до j-1 *)
      (forall k, i <= k < j -> tail_preserved f k theta).
    
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