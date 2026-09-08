From ltl Require Import ltl ltl_fixpoints ltl_now.

Import tProp.

Section fair_sched.
  Context (label : Set).
  Context (f : nat → label).

  Notation state := nat.

  Inductive steps : state → label → state → Prop :=
  | my_step_succ i : steps i (f i) (i+1)
  | my_step_fail i j : f i ≠ j → steps i j i.

  Notation tProp := (tProp state label steps).

  Axiom advanced_fair : ∀ i, ⊢ ◊ ↓l i : tProp.

  Lemma step i :
    ↓s i ⊢ ∃ l, ↓l l ∧
                ((⌜f i = l⌝ ∧ ○ ↓s (i+1)) ∨
                (⌜f i ≠ l⌝ ∧ ○ (↓s i))) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]";
      [by eexists _, _; constructor|].
    inversion Hsteps'; simplify_eq.
    - iExists (f i). iFrame. iLeft. iFrame. done. 
    - iExists l. iFrame. iRight. iFrame. done.
  Qed.

  Lemma eventually_incr i :
    ↓s i ⊢ ◊ ↓s (i+1) : tProp.
  Proof.
    iIntros "Hs".
    iAssert (↓s i ∪ ↓s (i+1))%I with "[Hs]" as "H"; last first.
    { by iApply (ltl_until_mono_strong with "[] [] H"); eauto. }
    iRevert "Hs".
    iDestruct (advanced_fair (f i)) as "-#Hfair".
    iApply (ltl_eventually_ind_strong with "[] Hfair").
    iIntros "!> [Hl|H]".
    { iIntros "Hs".
      iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (step with "Hs") as (l) "[Hl' Hstep]". 
      iDestruct "Hstep" as "[[%Heq Hstep]|[%Hneq Hstep]]"; last first.
      { iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %<-. done. }
      iApply ltl_until_intro_next. iFrame.
      iModIntro. iApply ltl_until_intro_now. done. }
    iDestruct "H" as "[Hl IH]".
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs2]".
    iDestruct (step with "Hs") as  (l) "[Hl' Hstep]".
    iDestruct "Hstep" as "[[%Heq Hstep]|[%Hneq Hstep]]". 
    { iApply ltl_until_intro_next. iFrame. iModIntro.
      iApply ltl_until_intro_now. iFrame. }
    iApply ltl_until_intro_next. iFrame. iModIntro. by iApply "IH".
  Qed.

  Lemma eventually_n n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. }
    iInduction j as [|j IHj] forall (n i H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H".
      by iApply ltl_eventually_intro_now. }
    iIntros "Hi".
    iDestruct (eventually_incr with "Hi") as "H'".
    iApply (ltl_eventually_ind_strong with "[] H'").
    iIntros "!> [H|(H3&H2)]".
    { iApply "IHj".
      { instantiate (1:=i+1). rewrite -H1. iPureIntro. lia. }
      { iPureIntro. lia. }
      iFrame. }
    by iApply ltl_next_eventually.
  Qed.

End fair_sched.

Module fair_coin.

  Definition state : Set := nat.
  Definition label : Set := bool.
  Definition f := Nat.even.

  Notation tProp := (tProp state label (steps label f)).

  Lemma eventually_n_coin n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof. apply eventually_n. Qed.

End fair_coin.

Module fair_inf.

  Definition state : Set := nat.
  Definition label : Set := nat.
  Definition f := (id : nat → nat).

  Notation tProp := (tProp state label (steps label f)).

  Lemma eventually_n_inf n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof. apply eventually_n. Qed.

End fair_inf.
