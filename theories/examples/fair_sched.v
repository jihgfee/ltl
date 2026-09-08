From ltl Require Import ltl ltl_fixpoints ltl_now classical ltl_adequacy.

Import tProp.

Section fair_sched.
  Context (state : Set).
  Context (next : state → state).
  Context (f : state → nat).
  Context (label : Set).
  Context (g : state → label).
  Context (Hg : ∀ s i, f s = i → f (next s) = S i).

  Inductive steps : state → label → state → Prop :=
  | my_step_succ s : steps s (g s) (next s)
  | my_step_fail s j : g s ≠ j → steps s j s.

  Notation tProp := (tProp state label steps).

  Axiom advanced_fair : ∀ i, ⊢ ◊ ↓l i : tProp.

  Lemma step (s:state) :
    ↓s s ⊢ ∃ (l:label), ↓l l ∧
                ((⌜g s = l⌝ ∧ ○ ↓s (next s)) ∨
                 (⌜g s ≠ l⌝ ∧ ○ (↓s s))) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]";
      [by eexists _, _; constructor|].
    inversion Hsteps'; simplify_eq.
    - iExists (g s). iFrame. iLeft. iFrame. done. 
    - iExists l. iFrame. iRight. iFrame. done.
  Qed.

  Lemma eventually_incr s :
    ↓s s ⊢ ◊ ↓s (next s) : tProp.
  Proof.
    iIntros "Hs".
    iAssert (↓s s ∪ ↓s (next s))%I with "[Hs]" as "H"; last first.
    { by iApply (ltl_until_mono_strong with "[] [] H"); eauto. }
    iRevert "Hs".
    iDestruct (advanced_fair (g s)) as "-#Hfair".
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
    ↓fs f 0 ⊢ ◊ ↓fs f n : tProp.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. }
    iInduction j as [|j IHj] forall (n i H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H".
      by iApply ltl_eventually_intro_now. }
    iIntros "Hi".
    iDestruct (ltl_now_state_f_frame with "Hi") as (s Hs) "Hs".
    iDestruct (eventually_incr with "Hs") as "H'".
    iApply (ltl_eventually_ind_strong with "[] H'").
    iIntros "!> [H|(H3&H2)]".
    { iApply "IHj".
      { instantiate (1:=i+1). rewrite -H1. iPureIntro. lia. }
      { iPureIntro. lia. }
      iApply ltl_now_state_f_frame. iExists _.
      iFrame. 
      iPureIntro. erewrite Hg; [|done]. lia. }
    by iApply ltl_next_eventually.
  Qed.

End fair_sched.

Module incr.

  Definition state : Set := nat.
  Definition label : Set := ().
  Definition f (_:state) := ().
  Definition g : nat → nat := id.
  Definition next := S.

  Notation tProp := (tProp state label (steps state next label f)).

  Lemma eventually_n_coin n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof.
    apply eventually_n. 
    naive_solver.
  Qed.
  
End incr.

Module fair_coin.

  Definition state : Set := nat.
  Definition label : Set := bool.
  Definition f := Nat.even.
  Definition g : nat → nat := id.
  Definition next := S.

  Notation tProp := (tProp state label (steps state next label f)).

  Lemma eventually_n_coin n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof.
    apply eventually_n. 
    naive_solver.
  Qed.

End fair_coin.

Module fair_inf.

  Definition state : Set := nat.
  Definition label : Set := nat.
  Definition f : state → label := id.
  Definition g : state → state := id.
  Definition next := S.

  Notation tProp := (tProp state label (steps state next label f)).

  Lemma eventually_n_inf n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof.
    apply eventually_n. 
    naive_solver.
  Qed.

End fair_inf.
