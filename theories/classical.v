From ltl Require Import ltl.
From Stdlib.Logic Require Import ClassicalFacts.

Axiom excluded_middle : ∀ P, P ∨ ¬ P.

Section classical.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (* OBS: Needed to unseal definitions *)
  Import tProp.

  Lemma ltl_excluded_middle (P : tProp) :
    ⊢ P ∨ ¬ P.
  Proof.
    econstructor. intros.
    pose proof (excluded_middle (P tr)).
    unseal. done.
  Qed.
    
  Lemma ltl_until_foo (P Q : tProp) :
    P ∪ Q ⊢ (P ∧ ¬ Q) ∪ Q.
  Proof.
    iDestruct (ltl_excluded_middle Q) as "[HQ|HQ]".
    { iIntros "H". 
      iEval (rewrite ltl_until_unfold).
      iLeft. done. }
    iIntros "H". iRevert "HQ".    
    iApply (ltl_until_ind with "[] H").
    iIntros "!> [HQ|(HP&HPQ&IH)] HQ'".
    { by rewrite -ltl_until_intro_now. }
    iEval (rewrite ltl_until_unfold).
    iRight.
    iFrame "HP". iFrame.
    iModIntro.
    iDestruct (ltl_excluded_middle Q) as "[HQ|HQ]".
    { iEval (rewrite ltl_until_unfold). iLeft. done. }
    by iApply "IH".
  Qed.

End classical.
