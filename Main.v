Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import Lia.
Import ListNotations.

Require Import Turchin_Defs.
Require Import Turchin_Lib.
Require Import Turchin_Growth.

Section Main_Proof.
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  Variable G : grammar letter.
  
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.

  (* ГЕНЕРАТОРЫ СЛОВ *)

  (* Генерация всех слов длины n *)
  Fixpoint generate_words_of_length (n : nat) : list (word letter) :=
    match n with
    | 0 => [ [] ] 
    | S k => 
      let prev_words := generate_words_of_length k in
      flat_map (fun w => map (fun a => a :: w) Finite_Sigma) prev_words
    end.
    
  (* Генерация всех слов длины <= n *)
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

  (* ЕСТЬ ПОВТОРЕНИЕ -> ОТНОШЕНИЕ ТУРЧИНА *)

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
    intros l. exists l. rewrite app_nil_r. reflexivity.
  Qed.

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

   (* BAD SEQUENCE -> BOUNDED *)

  Definition IsBadSequence (f : nat -> word letter) : Prop :=
    forall i j, i < j -> ~ is_turchin_pair G f i j.

  (* Если последовательность плохая, в ней нет повторов *)
  Lemma Bad_Implies_Unique : 
    forall f, 
    chain G f ->
    IsBadSequence f -> 
    (forall n, f n <> []) -> 
    forall i j, i < j -> f i <> f j.
  Proof.
    intros f Hchain Hbad Hne i j Hlt Heq.
    apply Hbad with (i := i) (j := j).
    - assumption.
    - apply Repetition_Is_Turchin.
      + assumption.
      + assumption.
      + apply Hne.
      + assumption.
  Qed.

  (* Если последовательность плохая, она ограничена. *)
  Theorem Bad_Sequence_Is_Bounded :
      forall f,
      chain G f ->
      (forall n, f n <> []) ->
      IsBadSequence f ->
      exists Bound, forall n, length (f n) <= Bound.
  Proof.
    intros f Hchain Hnonil Hbad.
    (* Докажем от противного *)
    apply NNPP. intro Hunbounded_neg.
    
    assert (Hunbounded: forall B, exists n, length (f n) > B).
    {
      intros B.
      apply not_all_not_ex. intro H_all_le.
      apply Hunbounded_neg.
      exists B. intros n.
      apply not_gt. apply H_all_le.
    }
  
    (* В плохой последовательности все элементы уникальны *)
    assert (H_inj: forall i j, i < j -> f i <> f j).
    { apply Bad_Implies_Unique; assumption. }
  
    (* Длина стремится к бесконечности *)
    assert (H_limit_inf: forall N, exists i, forall j, j > i -> length (f j) > N).
    {
      intros N.
      (* От противного: длина последовательности не стремится к бесконечности *)
      apply NNPP. intro H_not_lim.

      (* Длина слов бесконечно часто оказывается <= N *)
      assert (H_infinite_small: forall i, exists j, j > i /\ length (f j) <= N).
      {
        intro i.
        apply not_ex_all_not with (n:=i) in H_not_lim.
        apply NNPP. intro H_contra. apply H_not_lim.
        intros j Hgt.
        destruct (le_gt_dec (length (f j)) N).
        - exfalso. apply H_contra. exists j. split; assumption.
        - assumption.
      }
  
      (* Множество слов ограниченной длины конечно *)
      set (Universe := generate_words_upto_length N).
      set (Card := length Universe).
       
      (* Шагов бесконечно много*)
      (* Строим список индексов, которые отображаются в Universe, с длиной > |Universe| *)
      assert (H_indices_gen: forall k, exists L_idx, length L_idx = k /\ NoDup L_idx /\ 
              forall x, In x L_idx -> length (f x) <= N).
      {
        intros k. induction k.
        - exists []. repeat split; try constructor. intros x H. inversion H.
        - destruct IHk as [L [Hlen [Hnodup Hprop]]].
          set (max_idx := fold_right max 0 L).
          destruct (H_infinite_small max_idx) as [next_j [Hgt Hlen_le]].
           
          exists (next_j :: L).
          repeat split.
          + simpl. rewrite Hlen. reflexivity.
          + constructor.
            * intro Hin.
              assert (H_le_max: next_j <= max_idx).
              {
                unfold max_idx. clear -Hin. induction L. inversion Hin.
                simpl. destruct Hin. subst. apply Nat.le_max_l.
                transitivity (fold_right max 0 L). apply IHL. assumption. apply Nat.le_max_r.
              }
              lia.
            * assumption.
          + intros x Hin. destruct Hin as [Heq | Hin].
            * subst. assumption.
            * apply Hprop. assumption.
      }
       
      destruct (H_indices_gen (S Card)) as [L_idx [Hlen_idx [Hnodup_idx H_vals_le]]].
       
      set (ValList := map f L_idx).
       
      (* Все значения ValList лежат в Universe *)
      assert (H_incl: incl ValList Universe).
      {
        intros w Hin. apply in_map_iff in Hin. destruct Hin as [idx [Heq Hin_idx]].
        subst w. unfold Universe. apply generate_upto_complete. 
        apply H_vals_le. assumption.
      }
       
      (* Неизбежен повтор *)
      (* |ValList| > |Universe|, но ValList включен в Universe и NoDup  -> противоречие *)
      assert (H_collision: ~ NoDup ValList).
      {
        intro H_nodup_vals.
        assert (H_le: length ValList <= length Universe).
        { apply NoDup_incl_length; assumption. }
         
        unfold ValList in *. rewrite map_length in H_le.
        unfold Card in Hlen_idx. rewrite Hlen_idx in H_le.
        lia. 
      }
       
      apply H_collision.
      unfold ValList.
      apply NoDup_map_injective.
      - intros x y Hx Hy Heq_f.
        destruct (lt_eq_lt_dec x y) as [[Hlt|Heq]|Hgt].
        + apply (H_inj x y Hlt) in Heq_f. contradiction.
        + assumption.
        + symmetry in Heq_f. apply (H_inj y x Hgt) in Heq_f. contradiction.
      - assumption.
    }
    
    destruct (Growth_Implies_Turchin_Pair letter letter_eq_dec G Finite_Sigma Is_Finite f Hchain Hnonil H_limit_inf) as [i [j Hpair]].
    
    (* Нашли пару, а последовательность плохая -> противоречие *)
    apply (Hbad i j).
    - unfold is_turchin_pair in Hpair. tauto.
    - assumption.
  Qed.

  (* ОСНОВНАЯ ТЕОРЕМА *)

  Definition Relation_is_AFR (Rel : (nat -> word letter) -> nat -> nat -> Prop) : Prop :=
    forall (f : nat -> word letter),
    chain G f ->                 
    (forall n, f n <> []) ->     
    exists i j, i < j /\ Rel f i j.

  Theorem Turchin_is_AFR : Relation_is_AFR (is_turchin_pair G).
  Proof.
    unfold Relation_is_AFR.
    intros f Hchain Hnonil.
    
    apply NNPP.
    intro H_not_found.
  
    (* Если нет пар Турчина, то это плохая последовательность *)
    assert (H_bad : IsBadSequence f).
    {
      intros i j Hlt Hpair.
      apply H_not_found.
      exists i, j.
      unfold is_turchin_pair. 
      auto. 
    }

    (* Если последовательность плохая, то она ограничена *)
    pose proof (Bad_Sequence_Is_Bounded f Hchain Hnonil H_bad) as [Bound H_bound_len].

    (* Если последовательность ограничена, то есть повторы *)
    destruct (Bounded_Chain_Has_Repetition f Bound H_bound_len) as [i [j [Hlt Heq]]].

    (* Повторение влечет пару Турчина *)
    assert (H_is_turchin : is_turchin_pair G f i j).
    {
      apply Repetition_Is_Turchin.
      - assumption. 
      - assumption.
      - apply Hnonil.
      - assumption.
    }

    (* Противоречие *)
    apply (H_bad i j Hlt).
    assumption.
  Qed.

End Main_Proof.