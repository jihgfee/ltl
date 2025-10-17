From iris.proofmode Require Import proofmode.
From ltl Require Import ltl_no_em_alt_next.

Section examples.
  Context {S L : Type}.

  Notation ltl_prop := (ltl_prop S L).

  Import ltl_prop.

  Lemma ltl_always_introI (P : ltl_prop) :
     ⊢ P → (□ (P → (○ P))) → □ P.
  Proof. iIntros "HP HQ". iApply (ltl_always_intro with "HQ HP"). Qed.

  Lemma foo (P Q : ltl_prop) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    iIntros (HPQ) "HP".
    iAssert (□ ◊ (P ∧ Q))%I with "[-]" as "[_ $]".
    iApply (ltl_always_introI with "[HP]").
    { iDestruct (HPQ with "HP") as "HP".
      by rewrite ltl_next_eventually. }
    iIntros "!> [HP _]".
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

  Lemma running_example (P : ltl_prop) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[HP1 HP2]".
    iAssert (□ (P ∨ (○P)))%I with "[HP1 HP2]" as "H".
    { iApply (ltl_always_introI with "[HP2]").
      { by iLeft. }
      iIntros "!> [HP|HP]".
      + rewrite ltl_always_elim. iDestruct ("HP1" with "HP") as "HP".
        iIntros "!>". by iRight.
      + iIntros "!>". by iLeft. }
    iIntros "!>".
    rewrite ltl_always_elim.
    iDestruct "H" as "[H|H]".
    - by iApply ltl_eventually_intro.
    - iApply ltl_next_eventually.
      iIntros "!>".
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
    iIntros "!>".
    iApply ltl_eventually_next_intro.
    done.
  Qed.

  Lemma ltl_until_example (P Q : ltl_prop) :
    P ∪ Q ∧ (¬ □ P) ⊢ ◊ Q.
  Proof. rewrite -ltl_until_eventually. apply bi.and_elim_l. Qed.

  (* Lemma foo' {X} (P Q R : X → ltl_prop) : *)
  (*   ○ (∃ x, P x) ∧ □ ○ ∀ x, (P x → □ Q x) ∧ ◊ ○ ∀ x, (Q x  → R x) ⊢ ∀ x, ○ ◊ R x. *)
  (* Proof. *)
  (*   iIntros "(HP & HPQ & HQR)". iIntros "!>". *)
  (*   iMod "HPQ". iDestruct ("HPQ" with "HP") as "HQ". *)
  (*   iCombine "HQR" "HQ" as "H". iModEv with "H" as "[HQR HQ]". *)
  (*   iApply ltl_eventually_intro. iApply "HQR". by iMod "HQ". *)
  (* Qed. *)

  Lemma bar' (P Q R : Prop) : 
    P ∧ (P -> Q) -> Q.
  Proof.
    intros [HP HPQ].
    apply HPQ.
    apply HP.
  Qed.

  Lemma bar'' (P Q R : ltl_prop) : 
    P ∧ (P → ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[HP HPQ]".
    iDestruct ("HPQ" with "HP") as "HQ".
    iApply "HQ".
  Qed.  

  Lemma foo' (P Q R : ltl_prop) :
    ○ P ∧ □ ○ (P → □ Q) ∧ ◊ ○ (Q → R) ⊢ ○ ◊ R.
  Proof.
    iIntros "(HP & HPQ & HQR)".
    iModIntro.
    iMod "HPQ". iDestruct ("HPQ" with "HP") as "HQ".
    iCombine "HQR" "HQ" as "H". iModEv with "H" as "[HQR HQ]".
    iApply ltl_eventually_intro. iApply "HQR". by iMod "HQ".
  Qed.

  Lemma foo'' (P Q R : nat → ltl_prop) :
    ○ (∃ n, P n) ∧ □ ○ (∀ n, P n → ∃ m, □ Q m) ∧
    ◊ ○ (∀ m, Q m → ∃ k, R k) ⊢ ○ ◊ ∃ k, R k.
  Proof.
    iIntros "(HP & HPQ & HQR)".
    iModIntro. iDestruct "HP" as (n) "HP".
    iMod "HPQ". iDestruct ("HPQ" with "HP") as (m) "HQ".
    iCombine "HQR" "HQ" as "H". iModEv with "H" as "[HQR HQ]".
    iApply ltl_eventually_intro. iApply "HQR". by iMod "HQ".
  Qed.

End examples.

Notation "↓s Φ" := (↓ (λ osl, match osl with
                              | Some (s,l) => Φ (Some s)
                              | None => Φ None
                              end))%I (at level 20, right associativity) : bi_scope. 

Notation "↓l Φ" := (↓ (λ osl, match osl with
                              | Some (s,Some l) => Φ (Some l)
                              | Some (s,None) => Φ None
                              | None => Φ None
                              end))%I (at level 20, right associativity) : bi_scope. 

Section simple_ex.

  Definition state := nat.
  Definition label := unit.

  (* Inductive steps : state -> label -> state -> Prop := *)
  (*   my_step i : steps i () (i+1). *)

  (* Proven for this model *)
  Axiom step : ∀ i, (↓s (λ os, os = Some i)) ⊢ (○ (↓s (λ os, os = Some (i+1)))):ltl_prop state label.

  Lemma my_property (n:nat) : 
    ↓s (λ os, os = Some 0) ⊢ (◊ ↓s (λ os, os = Some n)):ltl_prop nat unit.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. } 
    revert n i H1 H2. induction j; intros n i H1 H2.
    { simplify_eq. rewrite right_id. iApply ltl_eventually_intro. }
    iIntros "H".
    iDestruct (step with "H") as "H".
    iApply ltl_next_eventually. iModIntro.
    iDestruct (IHj with "H") as "H".
    { instantiate (1:=n). rewrite -H1. lia. }
    { lia. }
    done.
  Qed.

End simple_ex.

Section advanced_ex.

  Definition state' : Set := nat * bool.
  Definition label' : Set := bool.

  Axiom fair :
    ∀ (b:bool), ⊢ (◊ (↓l (λ ol, ol = Some b))):ltl_prop state' label'.

  (* Proven for this model *)
  Axiom step_b :
    ∀ b i, (↓s (λ os, os = Some (i,b))) ⊢
         ((↓l (λ ol, ol = Some b)) ∧ ○ (↓s (λ os, os = Some (i+1,negb b)))) ∨
           ((↓l (λ ol, ol = Some (negb b)) ∧ ○ (↓s (λ os, os = Some (i,b))))).

  Lemma my_property'' i b :
    ↓s (λ os, os = Some (i,b)) ⊢
    ↓s (λ os, os = Some (i,b)) ∪ ↓s (λ os, os = Some (i+1,negb b)) : ltl_prop state' label'.
  Proof.
    iIntros "H".    
    iDestruct (fair b) as "H1".
    iRevert "H".
    iApply (ltl_until_ind with "H1").
    { iIntros "H1 H2".
       iDestruct (step_b with "H2") as "#[H3|H3]"; last first.
       { iDestruct "H3" as "[H3 H3']".
         iDestruct (ltl_now_false with "H1 H3") as "[]".         
         destruct b; intros [[? []]|] HP HQ; by naive_solver. }
       iDestruct "H3" as "[_ H3']".
       iApply ltl_until_next_intro. iFrame.
       iModIntro. iApply ltl_until_intro. done. }
    iIntros "[H1 [H2 _]] #H3".
    iDestruct (step_b with "H3") as "-#[H3'|H3']".
    { iApply ltl_until_next_intro.
      iFrame "#".
      iDestruct "H3'" as "[H' H'']".
      iModIntro.
      iApply ltl_until_intro.
      iApply (ltl_now_mono with "H''"). done. }
    iDestruct "H3'" as "[H' H'']".
    iApply ltl_until_next_intro.
    iFrame "#".
    iModIntro.
    iApply "H2".
    done.
  Qed.

  Lemma my_property' n b :
    ↓s (λ os, os = Some (0,b)) ⊢ ∃ b, (◊ ↓s (λ os, os = Some (n,b))):ltl_prop state' label'.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. } 
    revert n i b H1 H2. induction j; intros n i b H1 H2.
    { simplify_eq. rewrite right_id. iIntros "H". iExists b. iApply ltl_eventually_intro. done. }
    iIntros "H".
    iDestruct (my_property'' with "H") as "H".
    iApply (ltl_until_ind with "H").
    { iIntros "H".
      iDestruct (IHj with "H") as "H".
      { instantiate (1:=n). rewrite -H1. lia. }
      { lia. }
      done. }
    iIntros "(H1&H2&H3)".
    clear IHj.
    rewrite ltl_next_exists.
    iDestruct "H2" as (b') "H2".
    iExists b'.
    iApply ltl_next_eventually. iModIntro.
    done.
  Qed.

End advanced_ex.
