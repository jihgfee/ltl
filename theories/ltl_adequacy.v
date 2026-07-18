From iris.bi Require Import fixpoint_mono.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From ltl Require Import ltl ltl_now.

Section after.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Fixpoint after (n: nat) (t: trace S L) : (trace S L):=
    match n,t with
    | 0,_ => t
    | _,⟨ ⟩ => ⟨ ⟩
    | Datatypes.S n, ⟨ s ⟩ => ⟨ ⟩
    | Datatypes.S n, (s -[ ℓ ]-> xs) => after n (Some xs)
    end.

  Lemma after_nil n : after n ⟨⟩ = ⟨⟩.
  Proof. by destruct n. Qed.

  Lemma after_singleton n s : after (Datatypes.S n) ⟨ s ⟩ = ⟨⟩.
  Proof. done. Qed.

  Lemma after_cons n s l (tr : trace_aux S L) : after (Datatypes.S n) (s -[ l ]-> tr) =  after n (Some tr).
  Proof. done. Qed.

  Lemma after_sum_comm n m (tr : trace S L) :
    after n (after m tr) = after m (after n tr).
  Proof.
    revert tr m. induction n; intros tr m.
    { done. }
    revert n tr IHn.
    induction m; intros n tr IHn.
    { done. }
    destruct tr as [[|s l t]|]; [done| |done].
    rewrite after_cons.
    rewrite -IHn.
    rewrite IHm; [|done].
    destruct t.
    + simpl. rewrite !after_nil. done.
    + simpl. done.
  Qed.

  Lemma after_sum n m (tr : trace S L) :
    after (n+m) tr = after n (after m tr).
  Proof.
    revert tr m.
    induction n; intros tr m; [done|].
    replace (Datatypes.S n + m) with (n + (Datatypes.S m)) by lia.
    rewrite IHn.
    replace (Datatypes.S n) with (n + 1) by lia.
    rewrite IHn.
    f_equiv.
    destruct tr as [[]|].
    - destruct m; done.
    - rewrite after_cons. rewrite after_sum_comm. done.
    - simpl. destruct m; done.
  Qed.

  Lemma trace_wf_after n tr : trace_maximal Rel tr → trace_maximal Rel (after n tr).
  Proof.
    intros wf.
    revert tr wf.
    induction n; intros tr wf.
    { done. }
    replace (Datatypes.S n) with (n+1) by lia.
    rewrite after_sum.
    apply IHn.
    destruct tr as [[]|].
    - constructor.
    - simpl. inversion wf; simplify_eq. done.
    - simpl. constructor.
  Qed.

  Definition wf_after : nat → wf_trace S L Rel → wf_trace S L Rel :=
    λ n tr, Trace (after n (tr_car tr)) (trace_wf_after n (tr_car tr) (tr_wf tr)).

  Lemma wf_after_0 tr : wf_after 0 tr = tr.
  Proof. by destruct tr. Qed.

  Lemma wf_trace_eq (tr1 tr2 : wf_trace S L Rel) :
    tr_car tr1 = tr_car tr2 → tr1 = tr2.
  Proof. intros. destruct tr1, tr2. simpl in *. simplify_eq. done. Qed.

  Lemma wf_after_sum n m tr : wf_after (n+m) tr = wf_after n (wf_after m tr).
  Proof. apply wf_trace_eq. by apply after_sum. Qed.

End after.

Section ltl_adequacy.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.
  Notation tProp := (tProp S L Rel).

  Import tProp.

  Lemma ltl_adequate (P Q : tProp) :
    (P ⊢ Q)%I → ∀ tr, P tr → Q tr.
  Proof. intros. apply H. done. Qed.

  Lemma ltl_next_adequate (P : tProp) tr :
    (○ P)%I tr ≡ P (wf_after 1 tr).
  Proof. rewrite ltl_next_unseal. done. Qed.

  Lemma ltl_always_adequate (P : tProp) tr :
    (□ P)%I tr ≡ ∀ n, P (wf_after n tr).
  Proof.
    rewrite bi_intuitionistically_unseal'. rewrite ltl_always_unseal.
    rewrite /ltl_always_def. unseal.
    split.
    - intros.
      specialize (H n). simpl in *.
      revert P tr H.
      induction n; intros P tr H.
      { simpl in *. rewrite wf_after_0. done. }
      simpl in *. rewrite ltl_next_adequate in H.
      apply IHn in H.
      rewrite -wf_after_sum in H.
      replace (Datatypes.S n) with (n + 1) by lia. done.
    - intros H n.
      specialize (H n).
      revert tr P H.
      induction n; intros tr P H.
      { simpl in *. rewrite wf_after_0 in H. done. }
      apply ltl_next_iter_S.
      apply IHn.
      rewrite ltl_next_adequate.
      rewrite -wf_after_sum.
      done.
  Qed.


  Lemma ltl_eventually_next_equiv (P : tProp) :
    (◊ P)%I ≡ (∃ n : nat, ltl_next_iter n P)%I.
  Proof.
    iSplit.
    - 
      iApply ltl_eventually_ind.
      { iIntros "HP". iExists 0. done. }
      iIntros "[HP IH]".
      rewrite ltl_next_exists.
      iDestruct "IH" as (n) "IH".
      iExists (Datatypes.S n).
      simpl.
      iIntros "!>".
      done.
    - iDestruct 1 as (x) "H".
      iInduction x as [|n Hn].
      { iModUnIntro. done. }
      iApply ltl_next_eventually.
      simpl. iModIntro.
      by iApply "Hn".
  Qed.

  (* TODO: Clean up this proof *)
  Lemma ltl_eventually_adequate_1 (P : tProp) tr :
    (∃ n, P (wf_after n tr)) → (◊ P)%I tr.
  Proof. 
    intros H.
    apply ltl_eventually_next_equiv.
    destruct H as [n Hn].
    unseal. exists n.
    revert tr P Hn.
    induction n; intros tr P Hn.
    { rewrite wf_after_0 in Hn. simpl. done. }
    apply ltl_next_iter_S. apply IHn.
    rewrite ltl_next_adequate.
    rewrite -wf_after_sum. done.
  Qed.

  Lemma ltl_eventually_adequate_2 (P : tProp) :
    (◊ P)%I ⊢ ∃ n : nat, ltl_next_iter n P.
  Proof.
    iApply ltl_eventually_ind.
    { iIntros "HP". iExists 0. done. }
    iIntros "[HP IH]".
    rewrite ltl_next_exists.
    iDestruct "IH" as (n) "IH".
    iExists (Datatypes.S n).
    simpl.
    iIntros "!>".
    done.
  Qed.

  Lemma ltl_eventually_adequate (P : tProp) tr :
    (◊ P)%I tr ≡ ∃ n, P (wf_after n tr).
  Proof.
    split; [|apply ltl_eventually_adequate_1].
    intros.
    apply ltl_eventually_adequate_2 in H.
    revert H. unseal. intros H. destruct H as [n Hn].
    revert tr Hn.
    induction n; intros tr Hn.
    { exists 0. by rewrite wf_after_0. }
    simpl in *.
    rewrite ltl_next_adequate in Hn.
    apply IHn in Hn.
    destruct Hn as [m Hn].
    exists (Datatypes.S m).
    replace (Datatypes.S m) with (m + 1) by lia.
    rewrite wf_after_sum. done.
  Qed.

  Lemma ltl_now_adequate P (tr : wf_trace S L Rel) :
    (↓ P)%I tr ≡ P $ head_trace (tr_car tr).
  Proof.
    rewrite ltl_now_unseal. split.
    - intros. inversion H; simplify_eq; done.
    - intros. destruct tr as [[[]|]]; by econstructor.
  Qed.

  Lemma ltl_now_f_adequate {A} f (x : A) (tr : wf_trace S L Rel) :
    (↓fs f x)%I tr ≡ (f <$> (fst <$> head_trace (tr_car tr)) = Some x).
  Proof.
    rewrite /ltl_now_state_f. rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[[]|]]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[[]|]]; inversion H; simplify_eq; try eauto; try done.
  Qed.

  Lemma ltl_now_label_f_adequate {A} f (x : A) (tr : wf_trace S L Rel) :
    (↓fl f x)%I tr ≡ (f <$> mjoin (snd <$> head_trace (tr_car tr)) = Some x).
  Proof.
    rewrite /ltl_now_label_f. rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[[]|]]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[[]|]]; inversion H; simplify_eq; try eauto; try done.
  Qed.

End ltl_adequacy.
