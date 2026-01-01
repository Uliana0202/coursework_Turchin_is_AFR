Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import Lia.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Require Import Turchin_Defs.
Require Import Turchin_Lib.

Section Growth_Proof.
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  Variable G : grammar letter.
  
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.

  (* СВОЙСТВА ШАГА И LOW WATER MARK (LWM) *)

  (* Стабильность суффикса на одном шаге *)
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

  (* LWM: такой индекс k, что длина слова никогда больше не падает ниже |f(k)| *)
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

  (* Если последовательность растет неограниченно, LWM существуют сколь угодно далеко *)
  Lemma exists_LWM :
    forall f, chain G f ->
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    forall start_idx, exists k, k >= start_idx /\ is_low_water_mark f k.
  Proof.
    intros f Hchain Hgrow start_idx.
    set (S_lengths := fun len => exists t, t >= start_idx /\ length (f t) = len).

    assert (H_non_empty: exists len, S_lengths len). 
    { exists (length (f start_idx)). exists start_idx. split; [lia | reflexivity]. }
    
    destruct (exists_min_in_set S_lengths H_non_empty) as [min_len [H_in_S H_is_min]].
    destruct H_in_S as [k [H_ge_start H_len_k]].
    
    exists k. split.
    - assumption.
    - unfold is_low_water_mark. intros t H_ge_k.
      assert (H_in_S_t: S_lengths (length (f t))).
      { exists t. split; [lia | reflexivity]. }
      specialize (H_is_min (length (f t)) H_in_S_t).
      rewrite H_len_k.
      assumption.
  Qed.

  (* СОХРАНЕНИЕ СУФФИКСА *)

  (* Если k — LWM, и f(k) = l :: suffix, то suffix сохраняется навсегда *)
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
      
      assert (H_non_empty: f (k + delta) <> []).
      {
         pose proof (Hlwm (k + delta) (Nat.le_add_r k delta)).
         rewrite Hdecomp in H. simpl in H.
         intro Heq. rewrite Heq in H. simpl in H. lia.
      }
      
      destruct (f (k + delta)) as [| h t_prev] eqn:Hstructure; [contradiction|].

      apply step_preserves_tail with (l := h) (suffix := t_prev) in Hchain; [| reflexivity].
      destruct Hchain as [rhs H_next_eq].
      
      assert (H_suffix_in_tprev : exists mid, t_prev = mid ++ suffix).
      {
         destruct p_prev as [| x xs].
         - simpl in H_prev.
           exfalso.
           pose proof (Hlwm (k + delta) (Nat.le_add_r k delta)) as Hlen.
           rewrite Hstructure in Hlen. 
           rewrite Hdecomp in Hlen.
           rewrite H_prev in Hlen.
           simpl in Hlen.
           lia.
         - simpl in H_prev.
           injection H_prev as Hhead Htail.
           exists xs. assumption.
      }
      
      destruct H_suffix_in_tprev as [mid H_mid].
      rewrite H_mid in H_next_eq.
      exists (rhs ++ mid).
      rewrite H_next_eq.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma LWM_implies_trace_preservation : 
    forall f k l suffix,
    chain G f ->
    is_low_water_mark f k ->
    f k = l :: suffix ->
    forall t, t >= k -> tail_preserved G f t suffix.
  Proof.
    intros f k l suffix Hchain Hlwm Hdecomp t Hge.
    unfold tail_preserved.

    pose proof (preserves_suffix_forever f k l suffix Hchain Hlwm Hdecomp t Hge) as [p Hp].
    
    assert (p <> []).
    {
      intro Hnil. subst p. simpl in Hp.
      pose proof (Hlwm t Hge) as Hlen.
      rewrite Hdecomp in Hlen. rewrite Hp in Hlen. simpl in Hlen. lia.
    }
    
    destruct p as [| h mid]; [contradiction|].
    rewrite Hp.
    
    specialize (Hchain t).
    inversion Hchain as [l0 rhs tail Hin Hft Hfst].
    rewrite Hp in Hft.
    injection Hft as Hl0 Htail. subst l0 tail.
    
    exists h, rhs, mid.
    repeat split; try assumption.
  Qed.

  (* Существование следующего LWM с строго большей длиной *)
  Lemma exists_next_growing_LWM :
    forall f k,
    chain G f ->
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    is_low_water_mark f k ->
    exists k', k' > k /\ length (f k') > length (f k) /\ is_low_water_mark f k'.
  Proof.
    intros f k Hchain Hunbounded Hlwm.
    destruct (Hunbounded (length (f k))) as [i H_large].
    set (start := S (max k i)).
    destruct (exists_LWM f Hchain Hunbounded start) as [k' [Hge_start Hlwm']].
    
    exists k'.
    repeat split.
    - unfold start in Hge_start. lia.
    - apply H_large. unfold start in Hge_start. lia.
    - assumption.
  Qed.

  (* РОСТ -> ПАРА ТУРЧИНА *)

  Theorem Growth_Implies_Turchin_Pair :
    forall f,
    chain G f ->
    (forall n, f n <> []) ->
    (* неограниченный рост *)
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    exists i j, is_turchin_pair G f i j.
  Proof.
    intros f Hchain Hnonempty Hunbounded.

    (* Строим список LWM индексов *)
    assert (H_seq_exists: forall n, exists (L : list nat), 
      length L = n /\
      Sorted lt L /\
      NoDup L /\
      (forall x, In x L -> is_low_water_mark f x) /\
      (forall x y, In x L -> In y L -> x < y -> length (f x) < length (f y))).
    {
      intro n. induction n.
      - exists []. repeat split; try constructor; try contradiction.
      - destruct IHn as [L [Hlen [Hsorted [Hnodup [HLwm HGrow]]]]].
        
        assert (exists k_prev, (L = [] \/ k_prev = last L 0) /\ (L <> [] -> is_low_water_mark f k_prev)).
        {
          destruct L as [| h t]. 
          - (* L = [] *)
            exists 0. split; [left; reflexivity | contradiction].
          - (* L = h :: t *)
            exists (last (h :: t) 0). 
            split; [right; reflexivity | ].
            intro H_not_nil. 
            apply HLwm.
            apply last_In_not_nil.
            discriminate. 
        }

        destruct H as [k_prev [Hprev_def Hprev_LWM]].

        assert (exists k_next, (L=[] -> is_low_water_mark f k_next) /\ 
                               (L<>[] -> k_next > k_prev /\ length (f k_next) > length (f k_prev) /\ is_low_water_mark f k_next)).
        {
           destruct L.
           - destruct (exists_LWM f Hchain Hunbounded 0) as [k0 [_ Hk0]].
             exists k0. split; [intros _; exact Hk0 | contradiction].
           - specialize (Hprev_LWM ltac:(discriminate)).
             destruct (exists_next_growing_LWM f k_prev Hchain Hunbounded Hprev_LWM) as [kn [Hkn_gt [Hkn_len Hkn_lwm]]].
             exists kn. split; [tauto | ]. 
             intros _. repeat split; assumption.
        }
        destruct H as [k_next [Hbase Hstep]].
        
        (* Строим новый список: L ++ [k_next] *)
        exists (L ++ [k_next]).

        assert (H_new_sorted: Sorted lt (L ++ [k_next])).
        {
          apply sorted_snoc_max.
          - assumption. 
          - intros y Hy.
            destruct L as [| h t].
            -- inversion Hy.
            -- specialize (Hstep ltac:(discriminate)). destruct Hstep as [H_next_gt_prev _].
               destruct Hprev_def as [? | H_last_eq]; [discriminate | rewrite H_last_eq in H_next_gt_prev].
               assert (H_y_le_last: y <= last (h::t) 0).
               { apply sorted_last_max; assumption. }
               lia.
        }

        repeat split.
        
        + (* Длина *) 
          rewrite app_length, Hlen. simpl. lia.
        + (* Сортировка *) 
          exact H_new_sorted.
        + (* NoDup *) 
          apply Sorted_lt_implies_NoDup; assumption.

        + (* LWM *)
          intros x Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq|F]].
          * apply HLwm; assumption.
          * subst. destruct L; [apply Hbase; reflexivity | apply Hstep; discriminate].
          * contradiction.

        + (* Рост длин *)
          intros x y Hx Hy Hlt_xy.
          apply in_app_or in Hx; apply in_app_or in Hy.
          destruct Hx as [Hx|Hx], Hy as [Hy|Hy].
          * apply HGrow; assumption.
          * destruct Hy as [Heq | F]; [subst y | contradiction].
            destruct L as [| h t] eqn:E_L; [inversion Hx |].
            specialize (Hstep ltac:(discriminate)). destruct Hstep as [H_next_gt_prev [H_len_grow _]].
            
            (* Доказываем |f x| <= |f k_prev| *)
            assert (H_len_x_le_prev: length (f x) <= length (f k_prev)).
            {
               destruct Hprev_def as [? | H_last_eq]; [discriminate | rewrite H_last_eq].
               destruct (Nat.eq_dec x (last (h::t) 0)).
               - (* x = last *)
                 subst. apply le_n.
               - (* x < last *)
                 apply Nat.lt_le_incl.
                 apply HGrow.
                 + assumption.
                 + apply last_In_not_nil.
                   discriminate.
                 + assert (x <= last (h::t) 0) by (apply sorted_last_max; assumption).
                   lia.
            }
            lia.
          * destruct Hx as [Heq | F]; [subst x | contradiction].
            destruct L as [| h t].
            -- inversion Hy.
            -- specialize (Hstep ltac:(discriminate)). destruct Hstep as [H_next_gt_prev _].
               destruct Hprev_def as [? | H_last_eq]; [discriminate | rewrite H_last_eq in H_next_gt_prev].
               assert (y <= last (h::t) 0) by (apply sorted_last_max; assumption).
               lia. 
          * destruct Hx; destruct Hy; subst; try contradiction. lia.
    }

    (* Применяем принцип Дирихле (список L с длиной |Sigma|+1) *)
    destruct (H_seq_exists (S (length Finite_Sigma))) as [L [Hlen [Hsorted [Hnodup [HLwm HGrow]]]]].
    
    destruct Finite_Sigma as [|d0 rest] eqn:E_Sigma.
    { 
      simpl in Hlen. destruct L as [|k L']; [discriminate|].
      specialize (Hnonempty k).
      remember (f k) as word_k eqn:Heq_word.
      destruct word_k as [|bad_char rest_w].
      - subst. contradiction. 
      - pose proof (Is_Finite bad_char) as Hin_sigma. inversion Hin_sigma.
    }
    set (get_head_safe := fun k => match f k with | [] => d0 | h::_ => h end).
    
    assert (H_collision: exists k1 k2, In k1 L /\ In k2 L /\ k1 <> k2 /\ get_head_safe k1 = get_head_safe k2).
    {
      rewrite <- E_Sigma in Is_Finite.
      rewrite <- E_Sigma in Hlen.
      apply (@Pigeonhole_Finite_Sigma letter letter_eq_dec Finite_Sigma Is_Finite nat L get_head_safe).
      - assumption.
      - rewrite Hlen. lia.
    }
    
    destruct H_collision as [ka [kb [Hina [Hinb [Hneq H_head_eq]]]]].
    
    (* Упорядочиваем пару *)
    assert (H_found_pair: exists k1 k2, In k1 L /\ In k2 L /\ k1 < k2 /\ get_head_safe k1 = get_head_safe k2).
    {
       destruct (lt_eq_lt_dec ka kb) as [[Hlt | Heq] | Hgt].
       - exists ka, kb. repeat split; assumption.
       - contradiction. 
       - exists kb, ka. repeat split; try assumption. symmetry. assumption.
    }
    
    destruct H_found_pair as [k1 [k2 [Hin_k1 [Hin_k2 [Hlt Hhead_eq_safe]]]]].
    
    (* Строим пару Турчина *)
    exists k1, k2.
    unfold is_turchin_pair.
    split; [assumption |].
    
    pose proof (Hnonempty k1) as Hne1.
    pose proof (Hnonempty k2) as Hne2.
    destruct (f k1) as [| h1 t1] eqn:E1; [contradiction|].
    destruct (f k2) as [| h2 t2] eqn:E2; [contradiction|].
    
    unfold get_head_safe in Hhead_eq_safe.
    rewrite E1, E2 in Hhead_eq_safe.
    subst h2. 
    
    exists [h1]. (* v *)
    
    (* Докажем сохранение хвоста t1 *)
    assert (H_decomposition: exists v_mid, t2 = v_mid ++ t1).
    { 
      assert (H_ge: k2 >= k1) by lia.
      pose proof (LWM_implies_trace_preservation f k1 h1 t1 Hchain (HLwm k1 Hin_k1) E1 k2 H_ge) as H_pres.
      unfold tail_preserved in H_pres.
      destruct H_pres as [l_tmp [rhs_tmp [mid [_ [H_fk2_struct _]]]]].
      rewrite E2 in H_fk2_struct.
      injection H_fk2_struct as H_tmp_head_eq H_tail_eq.
      exists mid. assumption. 
    }
    destruct H_decomposition as [v_mid H_mid].
    
    exists v_mid, t1.
    
    repeat split.
    - intro Hnil. discriminate.
    - rewrite H_mid. simpl. reflexivity.
    - intros k Hk_range.
      assert (H_ge: k >= k1) by lia.
      apply (LWM_implies_trace_preservation f k1 h1 t1 Hchain (HLwm k1 Hin_k1) E1).
      assumption.
  Qed.

End Growth_Proof.