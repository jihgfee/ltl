From ltl Require Import ltl.

Section examples.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Import tProp.

  Lemma propositional_primer (P Q R : tProp) : ⊢ (P → Q) → (Q → R) → P → R.
  Proof. iIntros "HPQ HQR HP". iDestruct ("HPQ" with "HP") as "HQ". iApply "HQR". done. Qed.

  Lemma globally_primer (P Q : tProp) : ⊢ □ (P → Q) → □ P → Q → □ Q.
  Proof. iIntros "#HPQ #HP HQ". iModIntro. iApply "HPQ". done. Qed.

  Lemma next_primer (P Q R : tProp) : ⊢ □ ○ (P → Q) → ○ P → Q → ○ R → ○ Q.
  Proof. iIntros "#HPQ HP HQ HR". iModIntro. iApply "HPQ". done. Qed.

  Lemma eventually_primer (P Q R : tProp) : ⊢ □ (P → ◊ Q) → ◊ ○ P → ◊ ○ R →  ○ ◊ Q.
  Proof. iIntros "#HPQ HP HR". iMod "HP". iModIntro. iApply "HPQ". done. Qed.

  Lemma until_primer (P Q R : tProp) :
    ⊢ □ (R → P ∪ Q) → (○ P ∪ ○ R) → ◊ ○ R → ○ (P ∪ Q).
  Proof. iIntros "#HPQ HP HR". iMod "HP". iModIntro. iApply "HPQ". done. Qed.

  Lemma until_primer' (P P' Q R : tProp) :
    ⊢ □ (R → P' ∪ Q) → □ (P → P') → (○ P ∪ ○ R) → ◊ ○ R → ○ (P' ∪ Q).
  Proof.
    iIntros "#HPQ #HP' HP HR".
    iDestruct (ltl_until_mono _ (○ P') _ (○ R) with "[] [] HP") as "HP".
    { iIntros "!>HP!>". by iApply "HP'". }
    { eauto. }
    iMod "HP". iModIntro. by iApply "HPQ".
  Qed.

  Lemma running_example (P Q : tProp) : ⊢ □ (P → ○ ◊ Q) → ◊ P → ○ ◊ Q.
  Proof. iIntros "#HPQ HP". iMod "HP". by iApply "HPQ". Qed.

  Lemma running_example_extended (P Q R : tProp) :
    ⊢ □ (P → ○ ◊ Q) → □ (Q → ○ ◊ R) → ◊ P → ○ ○ ◊ R.
  Proof.
    iIntros "#HPQ #HQR HP". iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
    iModIntro. iMod "HQ". by iApply "HQR".
  Qed.

  Lemma ltl_always_introI (P : tProp) :
     ⊢ P → (□ (P → (○ P))) → □ P.
  Proof. iIntros "HP #HQ". iApply (ltl_always_intro with "HQ HP"). Qed.

  Lemma foo (P Q : tProp) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    iIntros (HPQ) "HP".
    iAssert (□ ◊ (P ∧ Q))%I with "[-]" as "[_ $]".
    iApply (ltl_always_introI with "[HP]").
    { iDestruct (HPQ with "HP") as "HP".
      by rewrite ltl_next_eventually. }
    iIntros "!> [HP _]".
    rewrite -ltl_eventually_next_comm.
    iMod "HP".
    rewrite ltl_eventually_next_comm. by iApply HPQ.
  Qed.

  Lemma bar (P Q : tProp) :
    □ P ∧ ◊ (P → ○ ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[#HP HPQ]". 
    iMod "HPQ" as "HPQ".
    iApply ltl_next_eventually.
    by iApply ("HPQ" with "HP").
  Qed.

  Lemma baz (P Q : tProp) :
    (□ (P ∧ Q)) ∧ ○ P ∧ Q ⊢ □ Q.
  Proof. iIntros "[[#HP #HQ] [HP' HQ']]". iIntros "!>". by iApply "HQ". Qed.

  Lemma motivating_example (P : tProp) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iAssert (□ (P ∨ (○P)))%I with "[HP1 HP2]" as "#H".
    { iApply (ltl_always_introI with "[HP2]").
      { by iLeft. }
      iIntros "!> [HP|HP]".
      + iDestruct ("HP1" with "HP") as "HP".
        iIntros "!>". by iRight.
      + iIntros "!>". by iLeft. }
    iIntros "!>".
    iDestruct "H" as "[H|H]".
    - by iApply ltl_eventually_intro_now.
    - iApply ltl_next_eventually.
      iIntros "!>".
      by iApply ltl_eventually_intro_now.
  Qed.

  Lemma ltl_always_eventually_intro (P : tProp) :
    □ (P → ○◊ P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iApply (ltl_always_introI with "[HP2]").
    { by iApply ltl_eventually_intro_now. }
    iIntros "!> HP". iApply ltl_eventually_next_comm.
    iMod "HP".
    iDestruct ("HP1" with "HP") as "HP".
    by iApply ltl_eventually_next_comm.
  Qed.

  Lemma running_example_alt (P : tProp) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iApply ltl_always_eventually_intro. iFrame.
    iIntros "!> HP". 
    iDestruct ("HP1" with "HP") as "HP".
    iIntros "!>".
    iApply ltl_eventually_intro_next.
    done.
  Qed.

  Lemma ltl_until_example (P Q : tProp) :
    P ∪ Q ∧ (¬ □ P) ⊢ ◊ Q.
  Proof. rewrite -ltl_until_eventually. apply bi.and_elim_l. Qed.

  Lemma bar' (P Q R : Prop) : 
    P ∧ (P -> Q) -> Q.
  Proof.
    intros [HP HPQ].
    apply HPQ.
    apply HP.
  Qed.

  Lemma bar'' (P Q R : tProp) : 
    P ∧ (P → ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[HP HPQ]".
    iDestruct ("HPQ" with "HP") as "HQ".
    iApply "HQ".
  Qed.  

  Lemma foo' (P Q R : tProp) :
    ○ P ∧ □ ○ (P → □ Q) ∧ ◊ ○ (Q → R) ⊢ ○ ◊ R.
  Proof.
    iIntros "(HP & #HPQ & HQR)".
    iModIntro.
    iDestruct ("HPQ" with "HP") as "#HQ".
    iMod "HQR".
    iDestruct ("HQR" with "HQ") as "HR".
    by iModUnIntro.
  Qed.

  Lemma foo'' (P Q R : nat → tProp) :
    ○ (∃ n, P n) ∧ □ ○ (∀ n, P n → ∃ m, □ Q m) ∧
    ◊ ○ (∀ m, Q m → ∃ k, R k) ⊢ ○ ◊ ∃ k, R k.
  Proof.
    iIntros "(HP & #HPQ & HQR)".
    iModIntro. iDestruct "HP" as (n) "HP".
    iDestruct ("HPQ" with "HP") as (m) "#HQ".
    iMod "HQR". iModUnIntro. by iApply "HQR".
  Qed.

End examples.

Notation "↓s Φ" := (↓ (λ osl, (match osl with
                              | Some (s,l) => Φ (Some s)
                              | None => Φ None
                              end):Prop))%I (at level 20, right associativity) : bi_scope. 

Notation "↓l Φ" := (↓ (λ osl, (match osl with
                              | Some (s,Some l) => Φ (Some l)
                              | Some (s,None) => Φ None
                              | None => Φ None
                              end):Prop))%I (at level 20, right associativity) : bi_scope. 


(* TODO! *)
Import tProp.

Inductive empty : SProp := .

Class LTL (S L : Type) (Rel : S → L → S → Prop) :=
  mkFoo
  {
    Rel_dec :: ∀ s l s', Decision (Rel s l s');
  }.

Definition reducible {S L} `{LTL S L} (s : S) :=
  ∃ (l:L) (s':S), Rel s l s'.

Lemma trace_steps {S L} `{HRel: LTL S L Rel} s :
  reducible s →
  (↓s (λ os, os = Some s)) ⊢
  ∃ (l:L) (s':S), ⌜Rel s l s'⌝ ∧
    ((↓l (λ ol, ol = Some l)) ∧ ○ (↓s (λ os, os = Some s'))) : tProp S L Rel.
Proof.
  intros (l&s'&Hsteps).
  constructor.
  intros [[tr|] tr_wf]; last first.
  { unseal. rewrite ltl_now_unseal.
    intros Hnow. inversion Hnow. simplify_eq. }
  unseal. rewrite ltl_now_unseal.
  intros Hnow. inversion Hnow; simplify_eq.
  { exfalso. apply empty_ind. inversion tr_wf. subst. specialize (H0 l s'). done. }
  clear Hsteps.
  assert (∃ c', head_trace (Some tr0) = Some c' ∧ Rel s l0 c') as Hwf.
  { destruct tr0.
    { exists s0. split; [done|].
      destruct (decide (Rel s l0 s0)); [done|].
      exfalso. apply empty_ind. inversion tr_wf. simplify_eq.
      simpl in *. simplify_eq. done. }
    exists s0. split; [done|].
    destruct (decide (Rel s l0 s0)); [done|].
    exfalso. apply empty_ind. inversion tr_wf. simplify_eq.
    simpl in *. simplify_eq. done. }
  destruct Hwf as (s''&Hhead&Hrel).
  destruct tr0; simpl in *; simplify_eq.
  - eexists l0, s''. econstructor; [done|].
    econstructor.
    + econstructor. done. 
    + rewrite ltl_next_unseal. econstructor. econstructor. done. 
  - eexists l0, s''. econstructor; [done|].
    econstructor.
    + econstructor. done. 
    + rewrite ltl_next_unseal. econstructor. econstructor. done. 
      Unshelve. all: by inversion tr_wf.
Qed.

Section simple_ex.
  Definition state := nat.
  Definition label := unit.
  Inductive steps : state → label → state → Prop :=
    | my_step i : steps i () (i+1).

  Notation tProp := (tProp state label steps).

  Instance simple_foo : LTL state label steps.
  Proof. 
    constructor. intros.
    destruct (decide (s' = s + 1)).
    - subst. constructor 1. destruct l. constructor.
    - constructor 2. intros H. inversion H. subst. done.
  Qed.

  (* TODO: Why is this needed for [unseal]? *)
  Import tProp.

  Lemma step i : ↓s (λ os, os = Some i) ⊢ ○ (↓s (λ os, os = Some (i+1))) : tProp.
  Proof.
    iIntros "H".
    assert (∃ l s', steps i l s') as Hsteps.
    { eexists _, _. constructor. }
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]"; [done|].
    clear Hsteps.
    inversion Hsteps'; simplify_eq.
    iFrame. 
  Qed.

  Lemma my_property (n:nat) : ↓s (λ os, os = Some 0) ⊢ (◊ ↓s (λ os, os = Some n)):tProp.
  Proof.   
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. } 
    iInduction j as [|j IH] forall (i H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H". by iModUnIntro. }
    iIntros "H".
    iDestruct (step with "H") as "H".
    iApply ltl_next_eventually. iModIntro.
    iDestruct ("IH" with "[] [] H") as "H".
    { subst. iPureIntro. lia. }
    { iPureIntro. lia. }
    done.
  Qed.

End simple_ex.

Section advanced_ex.

  Definition state' : Set := nat * bool.
  Definition label' : Set := bool.
  Inductive steps' : state' → label' → state' → Prop :=
  | my_step_succ i b : steps' (i,b) b (i+1,negb b)
  | my_step_fail i b : steps' (i,b) (negb b) (i,b).

  Instance advanced_foo : LTL state' label' steps'.
  Proof. 
    constructor. intros.
    destruct s as [i b].
    destruct (decide (b=l)); subst.
    - destruct (decide (s' = (i + 1, negb l))).
      + subst. constructor 1. constructor.
      + constructor 2. intros H. inversion H; subst. done. by destruct l.
    - destruct (decide (s' = (i, b))).      
      + subst. constructor 1. destruct b, l; [naive_solver|..|naive_solver]; constructor.
      + constructor 2. intros H. inversion H; subst. done. done. 
  Qed.

  Axiom fair :
    ∀ (b:bool), ⊢ (◊ (↓l (λ ol, ol = Some b))):tProp state' label' steps'.

  (* TODO: Why is this needed for [unseal]? *)
  Import tProp.

  Lemma step_b b i :
    (↓s (λ os, os = Some (i,b))) ⊢
    ((↓l (λ ol, ol = Some b)) ∧ ○ (↓s (λ os, os = Some (i+1,negb b)))) ∨
      ((↓l (λ ol, ol = Some (negb b)) ∧ ○ (↓s (λ os, os = Some (i,b))))):tProp state' label' steps'.
  Proof.
    iIntros "H".
    assert (∃ l s', steps' (i,b) l s') as Hsteps.
    { eexists _, _. constructor. }
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]"; [done|].
    clear Hsteps.
    inversion Hsteps'; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  (* TODO: Find a better way of handling this *)
  Lemma ltl_dup {S L Rel} (P : tProp S L Rel) : P ⊢ P ∧ P.
  Proof. iIntros "H". iFrame. Qed.

  Lemma my_property'' i b :
    ↓s (λ os, os = Some (i,b)) ⊢
    ↓s (λ os, os = Some (i,b)) ∪ ↓s (λ os, os = Some (i+1,negb b)) : tProp state' label' steps'.
  Proof.
    iDestruct (fair b) as "Hfair".
    iApply (ltl_eventually_ind with "[] Hfair").
    iIntros "!> [Hl|H]".
    { iIntros "Hs".
      iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (step_b with "Hs") as "[Hs|Hs]"; last first.
      { iDestruct "Hs" as "[Hs Hs'']".
        iDestruct (ltl_now_false with "Hl Hs") as "[]".
        destruct b; intros [[? []]|] HP HQ; by naive_solver. }
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

  Lemma my_property' n b :
    ↓s (λ os, os = Some (0,b)) ⊢ ∃ b, (◊ ↓s (λ os, os = Some (n,b))):tProp state' label' steps'.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. }
    iInduction j as [|j IHj] forall (n i b H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H". iExists b. iApply ltl_eventually_intro_now. done. }
    iIntros "H".
    iDestruct (my_property'' with "H") as "H'".
    iApply (ltl_until_ind with "[] H'").
    iIntros "!> [H|(H1&H3&H2)]".
    { iDestruct ("IHj" with "[] [] H") as "H".
      { instantiate (1:=n). rewrite -H1. iPureIntro. lia. }
      { iPureIntro. lia. }
      done. }
    rewrite ltl_next_exists.
    iDestruct "H2" as (b') "H2".
    iExists b'.
    iApply ltl_next_eventually. iModIntro.
    done.
  Qed.

End advanced_ex.
