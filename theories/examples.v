From iris.proofmode Require Import proofmode.
From ltl Require Import ltl.

Section examples.
  Context {S L : Type}.

  Notation ltl_prop := (ltl_prop S L).

  Import ltl_prop.

  Lemma foo (P Q : ltl_prop) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    iIntros (HPQ) "HP".
    iAssert (□ ◊ (P ∧ Q))%I with "[-]" as "[_ $]".
    iApply (ltl_always_intro with "HP").
    { iIntros "HP". iDestruct (HPQ with "HP") as "HPQ".
      iApply ltl_eventually_next.
      by rewrite -ltl_eventually_next_comm. }
    iIntros "[HP _]".
    rewrite -ltl_eventually_next_comm.
    iModEv with "HP".
    rewrite ltl_eventually_next_comm. by iApply HPQ.
  Qed.

  Lemma bar (P Q : ltl_prop) :
    □ P ∧ ◊ (P → ○ ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[HP HPQ]". iCombine "HPQ HP" as "HPQ".
    iModEv with "HPQ" as "[HPQ >HP]".
    iApply ltl_next_eventually.
    by iApply ("HPQ" with "HP").
  Qed.

  Lemma baz (P Q : ltl_prop) :
    (□ (P ∧ Q)) ∧ ○ P ∧ Q ⊢ □ Q.
  Proof. iIntros "[[HP HQ] [HP' HQ']]". iIntros "!>". by iMod "HQ". Qed.

  Lemma ltl_always_intro_alt (P Q R : ltl_prop) :
    (P ⊢ □ R) → (P ⊢ Q) → (□ R ∧ Q ⊢ (○ Q)) → (P ⊢ (□ Q)).
  Proof.
    intros HPR HPQ IHQ.
    iIntros "HP".
    iAssert (□ (ltl_and (□ R) Q))%I with "[HP]" as "H"; last first.
    { iDestruct "H" as "[H1 H2]". done. }
    iApply (ltl_always_intro with "HP").
    - iIntros "#HP".
      iDestruct (HPR with "HP") as "HR".
      iDestruct (HPQ with "HP") as "HQ".
      iSplit; done.
    - iIntros "[#HR HQ]". iDestruct (IHQ with "[$HR $HQ]") as "H".
      iCombine "H" "HR" as "H".
      iModNext with "H" as "[HQ HR]".
      iFrame.
  Qed.

  Lemma ltl_always_introI (P : ltl_prop) :
     ⊢ P → (□ (P → (○ P))) → □ P.
  Proof.
    iIntros "HP HQ".
    iApply (ltl_always_intro_alt (P ∧ □ (P → ○ P)) _ (P → ○ P)).
    { iIntros "[_ $]". }
    { iIntros "[$ _]". }
    { iIntros "[H1 H2]".
      rewrite ltl_always_elim. by iApply "H1". }
    iFrame.
  Qed.

  Lemma running_example (P : ltl_prop) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[HP1 HP2]".
    iAssert (□ (P ∨ (○P)))%I with "[HP1 HP2]" as "H".
    { iApply (ltl_always_introI with "[HP2]").
      { by iLeft. }
      iIntros "!> [HP|HP]".
      + rewrite ltl_always_elim. iDestruct ("HP1" with "HP") as "HP".
        iModNext with "HP" as "$".
      + iModNext with "HP" as "$". }
    iIntros "!>".
    rewrite ltl_always_elim.
    iDestruct "H" as "[H|H]".
    - by iApply ltl_eventually_intro.
    - iApply ltl_next_eventually.
      iModNext with "H".
      by iApply ltl_eventually_intro.
  Qed.

  Lemma ltl_always_eventually_intro (P : ltl_prop) :
    □ (P → ○◊ P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[HP1 HP2]".
    iApply (ltl_always_introI with "[HP2]").
    { by iApply ltl_eventually_intro. }
    iIntros "!> HP". iApply ltl_eventually_next_comm.
    iCombine "HP" "HP1" as "HP".
    iModEv with "HP" as "[HP >HP1]".
    iDestruct ("HP1" with "HP") as "HP".
    by iApply ltl_eventually_next_comm.
  Qed.

  Lemma running_example_alt (P : ltl_prop) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[HP1 HP2]".
    iApply ltl_always_eventually_intro. iFrame.
    iIntros "!> HP". rewrite ltl_always_elim.
    iDestruct ("HP1" with "HP") as "HP".
    iModNext with "HP".
    iApply ltl_eventually_next_intro.
    done.
  Qed.

  Lemma ltl_until_example (P Q : ltl_prop) :
    P ∪ Q ∧ (¬ □ P) ⊢ ◊ Q.
  Proof.
    rewrite ltl_not_always_eventually_not.
    iIntros "[H1 H2]".
    iCombine "H1 H2" as "H".
    rewrite ltl_until_eventually.
    iModEv with "H" as "[[H _]|[H _]]".
    - by iApply ltl_eventually_intro.
    - rewrite ltl_until_eventually. done.
  Qed.

End examples.
