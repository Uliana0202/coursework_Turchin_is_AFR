Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import Lia.
Import ListNotations.

Require Import Turchin_Defs.

Section Repetition_Is_Turchin.
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.

  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.

  Variable G : grammar letter.

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

  Lemma NoDup_map_injective : forall {A B : Type} (f : A -> B) (l : list A),
    NoDup l ->
    (forall x y, f x = f y -> x = y) ->
    NoDup (map f l).
  Proof.
    intros A B f l Hnodup Hinj.
    induction l as [|x xs IH].
    - simpl. constructor.
    - simpl. inversion Hnodup as [|? ? Hnotin Hnodup_xs]. subst.
      constructor.
      + intro Hin. apply in_map_iff in Hin.
        destruct Hin as [y [Heq Hin_xs]].
        apply Hinj in Heq. subst.
        contradiction.
      + apply IH. assumption.
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
  
  Lemma Length_NoDup_Incl_Manual : forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> 
    incl l1 l2 -> 
    length l1 <= length l2.
  Proof.
    intros A l1.
    induction l1 as [|x xs IH].
    - (* База *)
      intros l2 _ _. simpl. lia.
    - (* Шаг *)
      intros l2 Hnodup Hincl.
      simpl.
      inversion Hnodup as [|? ? Hnotin Hnodup_xs]. subst.
      
      assert (Hin_x : In x l2).
      { apply Hincl. left. reflexivity. }
      
      apply in_split in Hin_x.
      destruct Hin_x as [l2a [l2b Heq_l2]]. subst.
      
      rewrite app_length. simpl. rewrite Nat.add_succ_r.
      apply Le.le_n_S.
      
      rewrite <- app_length.
      
      apply IH.
      + assumption.
      + intros z Hz_in_xs.
        assert (Hz_neq_x : z <> x).
        { intro. subst. contradiction. }
        
        assert (Hz_in_full : In z (l2a ++ x :: l2b)).
        { apply Hincl. right. assumption. }
        
        apply in_app_or in Hz_in_full.
        apply in_or_app.
        
        destruct Hz_in_full as [Hleft | Hright].
        * (* z в левой части *)
          left. assumption.
        * (* z в правой части *)
          simpl in Hright.
          destruct Hright as [Heq | Hin_l2b].
          -- (* z = x *)
             symmetry in Heq. contradiction.
          -- (* z в l2b *)
             right. assumption.
  Qed.

  (* ПРИНЦИП ДИРИХЛЕ (PIGEONHOLE PRINCIPLE)*)
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
      - apply seq_NoDup.
      - intros x y Hfeq.
        destruct (Nat.eq_dec x y) as [Heq | Hneq].
        + assumption.
        + exfalso. apply (H_inj x y Hneq). assumption.
    }
    
    assert (H_incl : incl prefix_values L).
    {
      unfold prefix_values. intros x Hin_map.
      apply in_map_iff in Hin_map.
      destruct Hin_map as [k [Heq Hin_seq]].
      subst. apply H_in_domain.
    }
    
    assert (H_len_ineq : length prefix_values <= length L).
    {
      apply Length_NoDup_Incl_Manual.
      - assumption. 
      - assumption. 
    }

    unfold prefix_values, prefix_indices, n in H_len_ineq.
    rewrite map_length in H_len_ineq.
    rewrite seq_length in H_len_ineq.
    lia.
  Qed.

  (* ГЕНЕРАТОРЫ СЛОВ *)
  Fixpoint generate_words_of_length (n : nat) : list (word letter) :=
    match n with
    | 0 => [ [] ] 
    | S k => 
      let prev_words := generate_words_of_length k in
      flat_map (fun w => map (fun a => a :: w) Finite_Sigma) prev_words
    end.
    
  Fixpoint generate_words_upto_length (n : nat) : list (word letter) :=
    match n with
    | 0 => [ [] ]
    | S k => generate_words_of_length (S k) ++ generate_words_upto_length k
    end.

  Lemma generate_words_complete : 
    forall (w : word letter), In w (generate_words_of_length (length w)).
  Proof.
    intros w.
    induction w as [|a w' IH].
    - simpl. left. reflexivity.
    - simpl. apply in_flat_map. exists w'. split.
      + assumption.
      + apply in_map_iff. exists a. split.
        * reflexivity.
        * apply Is_Finite.
  Qed.

  Lemma generate_upto_complete : 
    forall (w : word letter) (n : nat), 
    length w <= n -> 
    In w (generate_words_upto_length n).
  Proof.
    intros w n Hlen.
    induction n as [| k IH].
    - (* n = 0 *)
      inversion Hlen. destruct w.
      + simpl. left. reflexivity.
      + simpl in H0. discriminate.
    - (* n = S k *)
      simpl. apply in_app_iff.

      destruct (Nat.eq_dec (length w) (S k)) as [Heq | Hneq].
      + (* Длина равна S k *)
        left.
        pose proof (generate_words_complete w) as H_compl.
        rewrite Heq in H_compl.
        exact H_compl.
      + (* Длина не равна S k, значит <= k *)
        right. apply IH.
        lia. 
  Qed.

  Lemma Bounded_Chain_Has_Repetition : 
    forall (f : nat -> word letter) (Bound : nat),
    (forall n, length (f n) <= Bound) -> 
    exists i j, i < j /\ f i = f j.
  Proof.
    intros f Bound H_bounded.
    set (All_Possible_Words := generate_words_upto_length Bound).
    apply Infinite_Pigeonhole with (L := All_Possible_Words).
    intro n.
    unfold All_Possible_Words.
    apply generate_upto_complete.
    apply H_bounded.
  Qed.

  Lemma suffix_nil : 
    forall l : word letter, is_suffix [] l.
  Proof.
    intros l. 
    exists l. 
    rewrite app_nil_r. 
    reflexivity.
  Qed.

  (* ЕСТЬ ПОВТОРЕНИЕ -> ОТНОШЕНИЕ ТУРЧИНА *)
  Lemma Repetition_Is_Turchin : 
    forall (f : nat -> word letter) (i j : nat),
    chain G f ->
    i < j ->
    f i <> [] ->    
    f i = f j ->    
    is_turchin_pair G f i j.
  Proof.
    intros f i j Hchain Hlt Hnot_nil Heq.
    unfold is_turchin_pair.
    split. assumption.

    exists (f i), [], [].
    
    repeat split.
    + assumption.
    + rewrite app_nil_r. reflexivity.
    + rewrite Heq. simpl. rewrite app_nil_r. reflexivity.
    + unfold tail_preserved. intros k Hk_range.
      specialize (Hchain k).
      inversion Hchain as [lhs rhs tail Hin Hfk Hfsk]; subst.
      exists lhs, rhs, tail.
      repeat split. 
      * assumption.
      * rewrite app_nil_r. reflexivity.
      * rewrite app_nil_r. simpl. reflexivity.
  Qed.
End Repetition_Is_Turchin.