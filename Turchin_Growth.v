Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import Lia.
Import ListNotations.

Require Import Turchin_Defs.
Require Import Repetition_Is_Turchin.

Section Growth_Proof.

  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  Variable G : grammar letter.
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.

  (** ПОКА ТАК :( *)
  Definition NonShortening (G : grammar letter) : Prop :=
    forall lhs rhs, In (lhs, rhs) G -> length rhs >= 1.
   

  Variable G_NonShort : NonShortening G.
  
  (* СТАБИЛЬНОСТЬ СУФФИКСА *)
  Lemma step_preserves_tail :
    forall w1 w2 l suffix,
    step G w1 w2 ->
    w1 = l :: suffix ->
    exists rhs, w2 = rhs ++ suffix.
  Proof.
    intros w1 w2 l suffix Hstep Hdecomp.
    inversion Hstep as [l0 rhs tail Hin Hw1 Hw2].
    subst.
    injection Hw1 as Hl_eq Htail_eq.
    subst.
    exists rhs.
    reflexivity.
  Qed.

  (* НЕОГРАНИЧЕННЫЙ РОСТ *)
  Definition is_low_water_mark (f : nat -> word letter) (k : nat) : Prop :=
    forall t, t >= k -> length (f t) >= length (f k).

  Lemma exists_min_in_set : 
    forall (P : nat -> Prop),
    (exists n, P n) ->
    exists m, P m /\ (forall n, P n -> m <= n).
  Proof.
    intros P [n0 Hn0].
    pose proof (classic (exists m, P m /\ forall n, P n -> m <= n)) as H_class.
    destruct H_class as [H_yes | H_no].
    - assumption.
    - exfalso.
      apply H_no.
      induction n0 using lt_wf_ind.
      destruct (classic (exists k, P k /\ k < n0)).
      + destruct H0 as [k [Pk Hk_lt]].
        apply (H k Hk_lt Pk).
      + exists n0. split. assumption.
        intros k Pk.
        apply not_ex_all_not with (n:=k) in H0.
        apply NNPP; intro H_ge. destruct H0. split; try assumption.
        lia.
  Qed.

  (* Если последовательность растет неограниченно, LWM существуют сколь угодно далеко. *)
  Lemma exists_LWM :
    forall f, chain G f ->
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    forall start_idx, exists k, k >= start_idx /\ is_low_water_mark f k.
  Proof.
    intros f Hchain Hgrow start_idx.
    (* Рассмотрим множество длин хвоста последовательности *)
    set (S_lengths := fun len => exists t, t >= start_idx /\ length (f t) = len).

    assert (H_non_empty: exists len, S_lengths len). (* Оно не пусто *)
    { exists (length (f start_idx)). exists start_idx. split; [lia | reflexivity]. }
    
    (* Найдем минимум m этого множества *)
    destruct (exists_min_in_set S_lengths H_non_empty) as [min_len [H_in_S H_is_min]].
    destruct H_in_S as [k [H_ge_start H_len_k]].
    
    (*  Индекс k, на котором достигается минимум - это LWM *)
    exists k. split.
    - assumption.
    - unfold is_low_water_mark. intros t H_ge_k.
      (* t >= k >= start_idx, значит длина f t тоже в множестве S *)
      assert (H_in_S_t: S_lengths (length (f t))).
      { exists t. split; [lia | reflexivity]. }
      specialize (H_is_min (length (f t)) H_in_S_t).
      rewrite H_len_k.
      assumption.
  Qed.

  (* Если k — LWM, и f(k) = l :: suffix, то suffix сохраняется навсегда. *)
  Lemma preserves_suffix_forever :
    forall f k l suffix,
    chain G f ->
    is_low_water_mark f k ->
    f k = l :: suffix ->
    forall t, t >= k -> exists prefix, f t = prefix ++ suffix.
  Proof.
    intros f k l suffix Hchain Hlwm Hdecomp t Hge.
    remember (t - k) as delta.
    replace t with (k + delta) by lia.
    clear t Hge Heqdelta.
    induction delta.
    - exists [l]. rewrite Nat.add_0_r. rewrite Hdecomp. reflexivity.
    - destruct IHdelta as [p_prev H_prev].
      rewrite Nat.add_succ_r.
      specialize (Hchain (k + delta)).
      
      (* f(k+delta) не пустое *)
      assert (H_non_empty: f (k + delta) <> []).
      {
         pose proof (Hlwm (k + delta) (le_plus_l k delta)).
         rewrite Hdecomp in H. simpl in H.
         intro Heq. rewrite Heq in H. simpl in H. lia.
      }
      
      destruct (f (k + delta)) as [| h t_prev] eqn:Hstructure; [contradiction|].
      (* Получили f(k+delta) = h :: t_prev *)
      (* И из гипотезы f(k+delta) = p_prev ++ suffix *)

      apply step_preserves_tail with (l := h) (suffix := t_prev) in Hchain; [| reflexivity].
      destruct Hchain as [rhs H_next_eq].
      
      (* Докажем, что suffix является суффиксом t_prev *)
      assert (H_suffix_in_tprev : exists mid, t_prev = mid ++ suffix).
      {
         destruct p_prev as [| x xs].
         - (* p_prev = []: тогда h :: t_prev = suffix. *)
           simpl in H_prev.
           
           (* Доказываем противоречие через длины *)
           exfalso.
           pose proof (Hlwm (k + delta) (le_plus_l k delta)) as Hlen.
           rewrite Hstructure in Hlen. 
           rewrite Hdecomp in Hlen.
           rewrite H_prev in Hlen.
           simpl in Hlen.
           lia.
           
         - (* p_prev = x :: xs (не пустой) *)
           simpl in H_prev.
           injection H_prev as Hhead Htail.
           exists xs. (* mid - это хвост p_prev *)
           assumption.
      }
      
      destruct H_suffix_in_tprev as [mid H_mid].
      rewrite H_mid in H_next_eq.
      exists (rhs ++ mid).
      rewrite H_next_eq.
      rewrite app_assoc.
      reflexivity.
  Qed.

  (* РОСТ -> ПАРА ТУРЧИНА *)

  Lemma monotone_growth : forall f, chain G f -> (forall n, length (f n) <= length (f (S n))).
  Proof.
    intros f Hchain n.
    specialize (Hchain n).
    inversion Hchain as [l rhs tail Hin Hfn HfSn].
    simpl.
    rewrite app_length.
    apply G_NonShort in Hin.
    lia.
  Qed.

  Lemma le_trans_induction_bases : forall (f : nat -> nat) (start end_ : nat),
    start <= end_ ->
    (forall n, f n <= f (S n)) ->
    f start <= f end_.
  Proof.
    intros f s e Hle Hstep.
    induction e.
    - assert (s = 0) by lia. subst. apply le_n.
    - destruct (le_lt_dec s e).
      + apply le_trans with (m := f e).
        * apply IHe. assumption.
        * apply Hstep.
      + assert (s = S e) by lia. subst. apply le_n.
  Qed.


  Theorem Growth_Implies_Turchin_Pair :
    forall f,
    chain G f ->
    (forall n, f n <> []) ->
    (* неограниченный рост *)
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    exists i j, is_turchin_pair G f i j.
  Proof.
    intros f Hchain Hnonempty Hunbounded.

    (* Определим критическую длину M *)
    set (M := 1).

    (* Найдем LWM (k), где длина слова уже > M *)
    destruct (Hunbounded M) as [start_idx H_growth_start].
    pose proof (exists_LWM f Hchain Hunbounded (S start_idx)) as [k [Hk_ge H_is_LWM]].
    
    assert (H_len_k_gt_M : length (f k) > M).
    { apply H_growth_start. lia. }

    set (HeadK := firstn M (f k)).
    set (StableSuffix := skipn M (f k)).
    
    assert (H_decomp_k : f k = HeadK ++ StableSuffix).
    { unfold HeadK, StableSuffix. symmetry. apply firstn_skipn. }
    
    (* Разложим f(k): firstn 1 - это голова (список из 1 буквы), skipn 1 - хвост *)
    assert (H_headK_struct : exists l, HeadK = [l]).
    {
      assert (L: length HeadK = 1). { unfold HeadK, M. apply firstn_length_le. lia. }
      destruct HeadK as [| l0 tail0].
      - inversion L.
      - destruct tail0.
        + exists l0. reflexivity.
        + inversion L.
    }
    destruct H_headK_struct as [head_k H_headK_eq].

    (* Докажем, что StableSuffix сохраняется навсегда для t >= k *)
    assert (H_stable : forall t, t >= k -> exists p, f t = p ++ StableSuffix).
    {
      intros t Ht.
      rewrite H_headK_eq in H_decomp_k.
      apply preserves_suffix_forever with (k := k) (l := head_k); assumption.
    }

    (* Последовательность uолов длины M *)
    set (Heads := fun (delta : nat) => firstn M (f (k + delta))).
    
    (* Множество всех слов длины 1 - это просто буквы *)
    set (AllWordsM := generate_words_of_length letter Finite_Sigma M).
    
    (* Принцип Дирихле *)
    destruct (Infinite_Pigeonhole letter AllWordsM Heads) as [d1 [d2 [Hlt_d H_eq_heads]]].
    - intro delta. unfold Heads, AllWordsM, M.
      set (w := firstn 1 (f (k + delta))).
      assert (H_len : 1 = length w).
      {
         unfold w. 
         symmetry. 
         apply firstn_length_le.
         (* Докажем 1 <= length (f (k+delta)), используя LWM *)
         transitivity (length (f k)).
         * lia.
         * apply H_is_LWM. lia.
      }
      rewrite H_len.
      apply generate_words_complete.
      apply Is_Finite.

   -  set (i := k + d1).
      set (j := k + d2).
      exists i, j.
    
      assert (H_idx_lt : i < j) by lia.

      assert (H_monotonic : forall n, length (f n) <= length (f (S n))).
      { apply monotone_growth. assumption. }
    
      (* Конструируем части слова для отношения Турчина *)
      (* f i = v ++ w' *)
      (* f j = v ++ v' ++ w' *)
      
      set (v := firstn M (f i)).
      set (w' := skipn M (f i)).
      
      (* v' - середина *)
      set (v' := firstn (length (f j) - length v - length w') (skipn M (f j))).
      unfold is_turchin_pair.
      split.
      { assumption. }
      
      exists v, v', w'.
      repeat split.
      
      (* v <> [] *)
      {
         unfold v, M.
         destruct (f i) as [| l_v t_v] eqn:Hfi.
         
         - (* f i = [] *)
           exfalso.
           apply (Hnonempty i). 
           assumption.
           
         - (* f i = l :: t. Тогда v = [l] *)
           simpl. 
           discriminate.
      }

      (* f(i) *)
      { unfold v, w'. symmetry. apply firstn_skipn. }
      
      (* f(j) *)
      {
         (* Докажем, что w' сохраняется в f j *)
         assert (H_w'_preserved : exists p, f j = p ++ w').
         {
            destruct (f i) as [| l_i tail_i] eqn:Hfi.
            { exfalso. apply (Hnonempty i); auto. }
            
            unfold w', M.
            simpl. 
            
            (* Применяем лемму preserves_suffix_forever для tail_i *)
            apply preserves_suffix_forever with (k:=i) (l:=l_i) (suffix:=tail_i).
            - assumption.
            - unfold is_low_water_mark. intros t0 Hge.
              apply le_trans_induction_bases with (f:=fun n => length (f n)); try assumption.
            - assumption.
            - lia. 
         }

         destruct H_w'_preserved as [p_j H_fj_eq].

         assert (L_pj_ge_M : length p_j >= M).
         {
             unfold M.
             assert (Lj : length (f j) = length p_j + length w').
             { rewrite H_fj_eq, app_length. reflexivity. }
             
             assert (Li : length (f i) = M + length w').
             {
                unfold w'.
                rewrite <- (firstn_skipn M (f i)) at 1.
                rewrite app_length.
                f_equal.
                apply firstn_length_le.
                transitivity (length (f k)).
                - unfold M in *. lia.
                - apply H_is_LWM. lia.
             }
             
             assert (Hgrow: length (f j) >= length (f i)).
             { 
                apply le_trans_induction_bases with (f:=fun n => length (f n)).
                - lia.
                - exact H_monotonic.
             }
             
             unfold M in *. 
             lia.
         }
         
         (*  Докажем, что p_j начинается с v *)
         assert (H_head_j : firstn M p_j = v).
         { 
           assert (H_heads_eq: firstn M (f j) = v).
           { unfold v, i, j. unfold Heads in H_eq_heads. symmetry. apply H_eq_heads. }
           
           rewrite H_fj_eq in H_heads_eq.
           rewrite firstn_app in H_heads_eq.
           replace (M - length p_j) with 0 in H_heads_eq by lia.
           rewrite app_nil_r in H_heads_eq.
           assumption.
         }
         
         rewrite H_fj_eq. 
         
         rewrite <- (firstn_skipn M p_j) at 1.
         rewrite H_head_j.
         
         rewrite app_assoc. 
         f_equal. 
         
         (* Раскроем v' и упростим *)
         unfold v'.
         rewrite H_fj_eq.
         
         rewrite skipn_app.
         assert (H_diff_zero: M - length p_j = 0) by (unfold M in *; lia).
         rewrite H_diff_zero.
         simpl.
         f_equal.
         
         (* Чтобы упростить skipn M p_j при M=1, нужно разобрать p_j *)
         destruct p_j as [| h_pj t_pj].
         { unfold M in L_pj_ge_M. simpl in L_pj_ge_M. lia. }
         
         unfold M in *. 
         
         (* length v = 1 избавит от match в цели *)
         assert (Len_v : length v = 1).
         {
            unfold v. rewrite firstn_length_le; [reflexivity|].
            transitivity (length (f k)); [lia | apply H_is_LWM; lia].
         }
         
         rewrite Len_v.
         simpl.
         
         rewrite app_length.
         replace (length t_pj + length w' - 0 - length w') with (length t_pj) by lia.
         
         rewrite firstn_app.
         rewrite firstn_all.
         replace (length t_pj - length t_pj) with 0 by lia.
         simpl.
         rewrite app_nil_r.
         
         reflexivity.
      }

      (* Хвост сохраняется *)
      {
         intros step H_step_range.
         unfold tail_preserved.
         
         (* Разбираем структуру f i *)
         destruct (f i) as [| li ti] eqn:Hfi.
         { exfalso. apply (Hnonempty i); auto. }
         
         (* Разложение для f step *)
         assert (H_step_decomp : exists p, f step = p ++ w').
         {
             unfold w', M.
             simpl.
             apply preserves_suffix_forever with (k:=i) (l:=li) (suffix:=ti).
             - assumption.
             
             - unfold is_low_water_mark. intros t0 Hge.
               apply le_trans_induction_bases with (f:=fun n => length(f n)); [lia | exact H_monotonic].
               
             - exact Hfi.
             - lia.
         }
         destruct H_step_decomp as [p_step H_step_eq].
         
         (* Разбираем шаг грамматики *)
         specialize (Hchain step).
         inversion Hchain as [l0 rhs0 tail0 Hin Hfstep Hfnext].
         
         (*  Докажем, что p_step не пустой *)
         destruct p_step as [| h_p t_p].
         { 
           exfalso.
           assert (L: length (f step) >= length (f i)). 
           { apply le_trans_induction_bases with (f:=fun n => length(f n)); [lia | exact H_monotonic]. }
           
           rewrite H_step_eq in L. simpl in L.
           rewrite Hfi in L. unfold w', M in L. simpl in L.
           lia. 
         }
         
         exists l0, rhs0, t_p.
         repeat split; try assumption.
         
         - (* Равенство для f step *)
           rewrite Hfstep. rewrite H_step_eq.
           rewrite H_step_eq in Hfstep.
           injection Hfstep as Hl0 Htail0.
           subst.
           reflexivity.
           
         - (* Равенство для f (S step) *)
           rewrite Hfnext.
           f_equal.
           rewrite H_step_eq in Hfstep.
           injection Hfstep as _ Hres.
           rewrite <- Hres.
           symmetry. 
           exact Hfnext. 
      }
  Qed.
  
  (* BAD SEQUENCE -> BOUNDED *)

  Definition IsBadSequence (f : nat -> word letter) : Prop :=
    forall i j, i < j -> ~ is_turchin_pair G f i j.

  (* Если последовательность плохая, она ограничена. *)
  Theorem Bad_Sequence_Is_Bounded :
    forall f,
    chain G f ->
    (forall n, f n <> []) ->
    IsBadSequence f ->
    exists Bound, forall n, length (f n) <= Bound.
  Proof.
    intros f Hchain Hnonil Hbad.
    (* Доказажем от противного *)
    apply NNPP.
    intro H_not_bounded.
    
    (* Докажем монотонность роста длины *)
    assert (H_mono_step : forall n, length (f n) <= length (f (S n))).
    {
      apply monotone_growth.
      assumption.
    }

    (* Преобразуем отрицание Bounded в условие неограниченного роста *)
    
    (* Докажем посылку для теоремы Growth -> Turchin Pair *)
    assert (H_growth_condition: forall N, exists i, forall j, j > i -> length (f j) > N).
    {
       intro N.
       destruct (classic (exists i, length (f i) > N)) as [H_exists | H_not_exists].
       - (* существует i, где длина > N *)
         destruct H_exists as [i H_gt].
         exists i.
         intros j H_j_gt_i.
         (* j > i, тогда |f j| >= |f i| > N *)
         assert (H_ge: length (f i) <= length (f j)).
         { 
           apply (le_trans_induction_bases (fun n => length (f n)) i j).
           - lia.
           - exact H_mono_step.
         }
         lia.
       - (* не существует такого i, тогда противоречие H_not_bounded*)
         exfalso.
         apply H_not_bounded.
         exists N.
         intro n.
         apply not_ex_all_not with (n:=n) in H_not_exists.
         lia.
    }
    
    (* Применяем теорему Growth -> Turchin Pair*)
    pose proof (Growth_Implies_Turchin_Pair f Hchain Hnonil H_growth_condition) as [i [j Hpair]].
    
    (* Противоречие с определением BadSequence *)
    unfold IsBadSequence in Hbad.
    apply (Hbad i j).
    - unfold is_turchin_pair in Hpair. lia.
    - assumption.
  Qed.

End Growth_Proof.


