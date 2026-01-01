Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import Lia.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Require Import Turchin_Defs.

Section Turchin_Library.
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.

  (* ВСПОМОГАТЕЛЬНЫЕ ЛЕММЫ О СПИСКАХ *)

  Lemma nth_error_seq_custom : forall len start n,
    n < len ->
    nth_error (seq start len) n = Some (start + n).
  Proof.
    induction len as [|len' IH]; intros start n Hlt.
    - lia. 
    - destruct n as [|n'].
      + simpl. f_equal. lia.
      + simpl. rewrite IH.
        * f_equal. lia.
        * lia. 
  Qed.
  
  Lemma last_In_not_nil: forall (A : Type) (l : list A) (d : A),
    l <> [] -> In (last l d) l.
  Proof.
    intros A l d H. induction l. contradiction.
    simpl. destruct l. left. reflexivity. right. apply IHl. discriminate.
  Qed.

  Lemma NoDup_nth_error_unique : forall {A : Type} (l : list A) (i j : nat) (x : A),
    NoDup l ->
    nth_error l i = Some x ->
    nth_error l j = Some x ->
    i = j.
  Proof.
    intros A l.
    induction l as [|h t IH].
    - intros i j x Hnodup Hi Hj.
      destruct i; discriminate. 
    - intros i j x Hnodup Hi Hj.
      inversion Hnodup as [|? ? Hnotin Hnodup_t]. subst.
      destruct i as [|i'], j as [|j'].
      + reflexivity.
      + simpl in Hi. injection Hi as Heq_xh. subst.
        simpl in Hj.
        apply nth_error_In in Hj.
        contradiction.
      + simpl in Hj. injection Hj as Heq_xh. subst.
        simpl in Hi.
        apply nth_error_In in Hi.
        contradiction.
      + simpl in Hi. simpl in Hj.
        f_equal. 
        eapply IH; eassumption.
  Qed.
  
  Lemma NoDup_map_injective : forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l -> NoDup (map f l).
  Proof.
    intros A B f l Hinj Hnodup.
    induction l as [|h t IH].
    - simpl. constructor.
    - simpl. inversion Hnodup as [|? ? Hnotin Hnodup_t]. subst.
      constructor.
      + intro Hin_map. apply in_map_iff in Hin_map.
        destruct Hin_map as [x [Heq Hin]].
        apply Hnotin.
        rewrite (Hinj h x).
        * assumption.
        * left; reflexivity.
        * right; assumption. 
        * symmetry; assumption.
      + apply IH.
        * intros x y Hx Hy. apply Hinj; try (right; assumption); assumption.
        * assumption.
  Qed.

  Lemma seq_NoDup : forall len start, NoDup (seq start len).
  Proof.
    induction len as [|n IH]; intros start; simpl.
    - constructor.
    - constructor.
      + intro H_in.
        assert (H_bound: forall s x, In x (seq s n) -> s <= x).
        {
          clear start IH H_in. 
          induction n as [|m IHm]; intros s x H; simpl in *.
          - contradiction.
          - destruct H as [Heq | Hin].
            * subst. lia. 
            * apply IHm in Hin. lia. 
        }
        apply H_bound in H_in.
        lia.
      + apply IH.
  Qed.

  (* СВОЙСТВА СОРТИРОВКИ *)

  Lemma sorted_snoc_max : forall (l : list nat) (x : nat),
    Sorted lt l ->
    (forall y, In y l -> y < x) ->
    Sorted lt (l ++ [x]).
  Proof.
    induction l as [| h t IH].
    - (* База *)
      simpl. intros. repeat constructor.
    - (* Шаг *)
      intros x Hsorted Hin.
      simpl.
      inversion Hsorted. subst.
      rename H1 into H_tail_sorted.
      rename H2 into H_head_rel.
      
      constructor.
      + apply IH.
        * assumption.
        * intros y Hy. apply Hin. right. assumption.
      + destruct t as [| h' t'].
        * simpl. constructor. apply Hin. left. reflexivity.
        * simpl.
          inversion H_head_rel. subst.
          constructor.
          assumption.
  Qed.

  Lemma sorted_last_max : forall (h : nat) (t : list nat) (d : nat),
    Sorted lt (h :: t) ->
    forall z, In z (h :: t) -> z <= last (h :: t) d.
  Proof.
    intros h t d Hsort z Hin.
    generalize dependent h.
    generalize dependent z.
    
    induction t as [| next_el tail' IH].
    - intros z h Hsort Hin.
      simpl in Hin. destruct Hin as [Heq | F]; [subst; simpl; apply le_n | contradiction].
    - intros z h Hsort Hin.
      inversion Hsort as [| ? ? H_tail_sorted H_head_rel]. subst.
      inversion H_head_rel. subst.
      
      simpl in Hin. destruct Hin as [Heq | Hin_tail].
      + subst z.
        simpl.
        apply Nat.lt_le_incl.
        apply Nat.le_trans with (m := next_el).
        * assumption. 
        * apply IH.
          -- assumption.
          -- left. reflexivity.
      + simpl.
        apply IH.
        * assumption.
        * assumption.
  Qed.

  Lemma Sorted_lt_implies_NoDup : forall l, Sorted lt l -> NoDup l.
  Proof.
    intros l Hsort.
    apply Sorted_StronglySorted in Hsort; [| exact Nat.lt_trans].
    induction Hsort.
    - constructor.
    - constructor.
      + intro Hin.
        rewrite Forall_forall in H.
        apply H in Hin.
        apply Nat.lt_irrefl in Hin.
        assumption.
      + assumption.
  Qed.

  (* ПРИНЦИПЫ ДИРИХЛЕ (PIGEONHOLE PRINCIPLES) *)

  (* Если в списке больше элементов, чем в алфавите, то есть повторы *)
  Lemma Pigeonhole_Finite_Sigma : forall (A : Type) (l : list A) (f_map : A -> letter),
    NoDup l ->
    length l > length Finite_Sigma ->
    exists x y, In x l /\ In y l /\ x <> y /\ f_map x = f_map y.
  Proof.
    intros A l f_map Hnodup Hlen.
    
    assert (H_logic: forall (xs : list A), NoDup xs -> 
      NoDup (map f_map xs) \/ exists x y, In x xs /\ In y xs /\ x <> y /\ f_map x = f_map y).
    {
      intros xs.
      induction xs as [|h t IH].
      - intros _. left. simpl. constructor.
      - intro Hnodup_cons.
        simpl in *.
        inversion Hnodup_cons as [|? ? Hnotin_h Hnodup_t]. subst.
        specialize (IH Hnodup_t).
        
        destruct IH as [IH_nodup | IH_exists].
        + (* В хвосте повторов нет *)
          destruct (in_dec letter_eq_dec (f_map h) (map f_map t)) as [Hin_map | Hnotin_map].
          * (* Повтор значения головы *)
            right.
            apply in_map_iff in Hin_map. 
            destruct Hin_map as [y [Heq_y Hin_y]].
            exists h, y.
            repeat split.
            -- left. reflexivity.
            -- right. assumption.
            -- intro eq. subst. contradiction.
            -- symmetry. assumption.
          * (* Повторов нет *)
            left. constructor; assumption.
        + (* Повтор в хвосте *)
          right.
          destruct IH_exists as [x [y [Hinx [Hiny [Hneq Heq]]]]].
          exists x, y.
          repeat split; try (right; assumption); assumption.
    }
  
    specialize (H_logic l Hnodup).
    destruct H_logic as [H_inj | H_found].
    - assert (H_incl: incl (map f_map l) Finite_Sigma).
      {
         intros x Hin. apply in_map_iff in Hin. destruct Hin as [a [Heq Hin_a]].
         subst. apply Is_Finite.
      }
      assert (H_le: length (map f_map l) <= length Finite_Sigma).
      { apply NoDup_incl_length; assumption. }
      
      rewrite map_length in H_le.
      lia. 
    - assumption.
  Qed.

  (* Бесконечный поток значений в конечном списке L обязательно зациклится *)
  Lemma Infinite_Pigeonhole :
    forall (L : list (word letter)) (f : nat -> word letter),
    (forall n, In (f n) L) ->
    exists i j, i < j /\ f i = f j.
  Proof.
    intros L f H_in_domain.
    apply NNPP. 
    intro H_no_repeat.
    assert (H_inj : forall i j, i <> j -> f i <> f j).
    {
      intros i j Hneq.
      destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt].
      - intro Heq_val. apply H_no_repeat. exists i, j. auto.
      - contradiction.
      - intro Heq_val. apply H_no_repeat. exists j, i. split; [assumption | symmetry; assumption].
    }
    
    set (n := S (length L)).
    set (prefix_indices := seq 0 n).
    set (prefix_values := map f prefix_indices).
    
    assert (H_nodup : NoDup prefix_values).
    {
      unfold prefix_values, prefix_indices.
      apply NoDup_map_injective.
      - intros x y Hinx Hiny Hfeq.
        destruct (Nat.eq_dec x y) as [Heq | Hneq].
        + assumption.
        + exfalso. apply (H_inj x y Hneq). assumption.
      - apply seq_NoDup.
    }
    
    assert (H_incl : incl prefix_values L).
    {
      unfold prefix_values. intros x Hin_map.
      apply in_map_iff in Hin_map.
      destruct Hin_map as [k [Heq Hin_seq]].
      subst. apply H_in_domain.
    }
    
    assert (H_len_ineq : length prefix_values <= length L).
    { apply NoDup_incl_length; assumption. }

    unfold prefix_values, prefix_indices, n in H_len_ineq.
    rewrite map_length in H_len_ineq.
    rewrite seq_length in H_len_ineq.
    lia.
  Qed.

End Turchin_Library.
