From Stdlib.Logic Require Import ClassicalFacts.
From ltl Require Import ltl ltl_fixpoints.

Axiom excluded_middle : ∀ P, P ∨ ¬ P.

Axiom choice :
  ∀ A B (R : A → B → Prop), (∀ x, ∃ y, R x y) → {f : A → B | ∀ x, R x (f x)}.

Definition epsilon {A : Type} {P : A → Prop} (Hex : ∃ x, P x) : A :=
  proj1_sig (choice unit A (λ _ x, P x) (λ _, Hex)) tt.

Lemma make_decision P : Decision P.
Proof.
  assert (∃ x : Decision P, True) as Hdecex.
  { destruct (excluded_middle P) as [HP|HnP].
    - exists (left HP); done.
    - exists (right HnP); done. }
  apply epsilon in Hdecex; done.
Qed.

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
    
  Lemma ltl_until_not_until (P Q : tProp) :
    P ∪ Q ⊢ (P ∧ ¬ Q) ∪ Q.
  Proof.
    iDestruct (ltl_excluded_middle Q) as "[HQ|HQ]".
    { iIntros "H". 
      iEval (rewrite ltl_until_unfold).
      iLeft. done. }
    iIntros "H". iRevert "HQ".    
    iApply (ltl_until_ind_strong with "[] H").
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
