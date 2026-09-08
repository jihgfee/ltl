From ltl Require Import ltl ltl_fixpoints ltl_now ltl_adequacy.

Module fair_coin_example.

  Definition state := bool.
  Definition label := bool.

  Inductive steps : state → label → state → Prop :=
    | steps_succ b : steps b b (negb b)
    | steps_fail b : steps b (negb b) b.

  Notation tProp := (tProp state label steps).

  Lemma step :
    ∀ b, ↓s b ⊢
         (↓l b ∧ ○ ↓s (negb b)) ∨
         (↓l (negb b) ∧ ○ ↓s b) : tProp.
  Proof.
    iIntros (i) "Hs".
    iDestruct (trace_steps with "Hs")
      as (l s' Hrel) "[Hl Hs']".
    { eexists _, _. constructor. }
    inversion Hrel; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma step_succ :
    ∀ b, (↓s b ∧ ↓l b)%I ⊢ ○ ↓s (negb b) : tProp.
  Proof.
    iIntros (b) "[Hs Hl]".
    iDestruct (step with "Hs") as "[[_ $]|(Hl'&Hs)]".
    iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
    by destruct b.
  Qed.

  Lemma eventual_step b :
    □ (∀ b, ◊ ↓l b) ∧ ↓s b ⊢ ◊ (↓s b ∧ ↓l b) : tProp.
  Proof.
    iIntros "[#Hfair Hs]". iRevert "Hs".
    iDestruct ("Hfair" $! b) as "-#Hl".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [Hl|[Hl IH]] Hs".
    { iModIntro. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (step with "Hs") as "[[Hl' Hs]|[Hl' Hs]]".
    { iModIntro. iFrame. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    iApply "IH". iFrame.
  Qed.

  Lemma eventual_response b :
    □ (∀ b, ◊ ↓l b) ⊢ ↓s b → ○ ◊ ↓s (negb b) : tProp.
  Proof.
    iIntros "#Hfair Hs".
    iDestruct (eventual_step with "[$Hfair $Hs]") as "Hsl".
    iMod "Hsl" as "[Hs Hl]".
    iDestruct (step_succ with "[$Hs $Hl]") as "Hs".
    iModIntro. iModIntro. done.
  Qed.

  Theorem theorem :
    □ (∀ b, ◊ ↓l b) ⊢ ◊ ↓s true → ○ ◊ ↓s false : tProp.
  Proof.
    iIntros "#Hfair". iIntros ">H". iRevert "H".
    iApply (eventual_response with "Hfair").
  Qed.

  Theorem theorem_meta
    (tr : wf_trace state label steps) :
    (∀ n b, ∃ m, mjoin (snd <$> (wf_head (wf_after m (wf_after n tr)))) = Some b) →
    (∃ n, (fst <$> wf_head (wf_after n tr)) = Some true) →
    ∃ n, fst <$> wf_head (wf_after n (wf_tail tr)) = Some false.
  Proof.
    pose proof theorem.
    revert H.
    adequacy_unseal.
    setoid_rewrite option_fmap_id.
    naive_solver.
  Qed.

End fair_coin_example.

Module fair_coin_increment_example.

  Definition state : Set := nat * bool.
  Definition label : Set := bool.
  Inductive steps : state → label → state → Prop :=
  | my_step_succ i b : steps (i,b) b (i+1,negb b)
  | my_step_fail i b : steps (i,b) (negb b) (i,b).

  Notation tProp := (tProp state label steps).

  Axiom fair : ∀ (b:bool), ⊢ ◊ ↓l b : tProp.

  Lemma step_b b i :
    ↓s (i,b) ⊢ ↓l b ∧ ○ ↓s (i+1,negb b) ∨ ↓l (negb b) ∧ ○ (↓s (i,b)) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s Hsteps) "[Hl Hs]";
      [by eexists _, _; constructor|].
    inversion Hsteps; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma eventually_incr i b :
    ↓s (i,b) ⊢ ◊ ↓s (i+1,negb b) : tProp.
  Proof.
    iIntros "Hs".
    iAssert (↓s (i,b) ∪ ↓s (i+1,negb b))%I with "[Hs]" as "H"; last first.
    { by iApply (ltl_until_mono_strong with "[] [] H"); eauto. }
    iRevert "Hs".
    iDestruct (fair b) as "-#Hfair".
    iApply (ltl_eventually_ind_strong with "[] Hfair").
    iIntros "!> [Hl|H]".
    { iIntros "Hs".
      iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (step_b with "Hs") as "[Hs|Hs]"; last first.
      { iDestruct "Hs" as "[Hs Hs'']".
        iDestruct (ltl_now_false with "Hl Hs") as "[]".
        destruct b; intros [[[] []]|] HP HQ; by naive_solver. }
      iDestruct "Hs" as "[_ Hs'']".
      iApply ltl_until_intro_next. iFrame.
      iModIntro. iApply ltl_until_intro_now. done. }
    iDestruct "H" as "[Hl IH]".
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs2]".
    iDestruct (step_b with "Hs") as "[[Hl' Hs']|[Hl' Hs']]".
    { iApply ltl_until_intro_next. iFrame. iModIntro.
      iApply ltl_until_intro_now. by iApply (ltl_now_mono with "Hs'"). }
    iApply ltl_until_intro_next. iFrame. iModIntro. by iApply "IH".
  Qed.

  Lemma eventually_n n :
    ↓fs fst 0 ⊢ ◊ ↓fs fst n : tProp.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. }
    iInduction j as [|j IHj] forall (n i H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H".
      by iApply ltl_eventually_intro_now. }
    iIntros "Hi".
    iDestruct (ltl_now_prod_fst with "Hi") as (b) "Hs".
    iDestruct (eventually_incr with "Hs") as "H'".
    iApply (ltl_eventually_ind_strong with "[] H'").
    iIntros "!> [H|(H3&H2)]".
    { iApply "IHj".
      { instantiate (1:=i+1). rewrite -H1. iPureIntro. lia. }
      { iPureIntro. lia. }
      iDestruct "H" as "[$ _]". }
    by iApply ltl_next_eventually.
  Qed.

  Theorem eventually_n_meta
    (tr : wf_trace state label steps) i :
    fst <$> (fst <$> wf_head tr) = Some 0 →
    ∃ n, fst <$> (fst <$> wf_head (wf_after n tr)) = Some i.
  Proof.
    pose proof (eventually_n i).
    revert H. adequacy_unseal. naive_solver.
  Qed.

End fair_coin_increment_example.
