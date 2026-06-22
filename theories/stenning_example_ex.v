From ltl Require Import ltl classical examples.

Section foo.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_now_state st : tProp :=
    (↓ (λ osl, (match osl with
                              | Some (s,_) => s = st
                              | _ => False
                              end):Prop))%I.

  Notation "↓s st" := (ltl_now_state st) (at level 20, right associativity) : bi_scope.

  Definition ltl_now_label lbl : tProp :=
    (↓ (λ osl, (match osl with
                | Some (s,Some l) => l = lbl
                | _ => False
                end):Prop))%I.

  Notation "↓l lbl" := (ltl_now_label lbl)%I (at level 20, right associativity) : bi_scope.

  Import tProp.

  Lemma ltl_now_state_agree (x y : S) :
    ⊢ ↓s x → ↓s y → ⌜x = y⌝ : tProp.
  Proof.
    constructor.
    rewrite /ltl_now_state ltl_now_unseal.
    unseal.
    intros tr _ H2 H3. inversion H2; inversion H3; simplify_eq; try done.
  Qed.

  Lemma ltl_now_lbl_agree (x y : L) :
    ⊢ ↓l x → ↓l y → ⌜x = y⌝ : tProp.
  Proof.
    constructor.
    rewrite /ltl_now_label ltl_now_unseal.
    unseal.
    intros tr _ H2 H3. inversion H2; inversion H3; simplify_eq; try done.
  Qed.

End foo.

Arguments ltl_now_state {_ _ _} _ : simpl never.
Arguments ltl_now_label {_ _ _} _ : simpl never.

Notation "↓s st" := (ltl_now_state st) (at level 20, right associativity) : bi_scope.

Notation "↓l lbl" := (ltl_now_label lbl)%I (at level 20, right associativity) : bi_scope.

Import tProp.

Lemma trace_steps' {S L} `{HRel: LTL S L Rel} s :
  reducible s →
  ↓s s ⊢ ∃ (l:L) (s':S), ⌜Rel s l s'⌝ ∧ ↓l l ∧ ○ ↓s s' : tProp S L Rel.
Proof.
  intros (l&s'&Hsteps).
  constructor.
  intros [[tr|] tr_wf]; last first.
  { unseal. rewrite /ltl_now_state ltl_now_unseal.
    intros Hnow. inversion Hnow. done. }
  unseal. rewrite /ltl_now_state ltl_now_unseal.
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
    + rewrite /ltl_now_label ltl_now_unseal. econstructor. done. 
    + rewrite ltl_next_unseal. econstructor. econstructor. done. 
  - eexists l0, s''. econstructor; [done|].
    econstructor.
    + rewrite /ltl_now_label ltl_now_unseal. econstructor. done. 
    + rewrite ltl_next_unseal. econstructor. econstructor. done. 
      Unshelve. all: by inversion tr_wf.
Qed.

Lemma trace_steps {S L Rel} `{HRel: LTL S L Rel} s l :
  reducible s →
  ↓s s ∧ ↓l l ⊢ ∃ (s':S), ⌜Rel s l s'⌝ ∧ ○ ↓s s' : tProp S L Rel.
Proof.
  iIntros (Hred) "[Hs Hl]".
  iDestruct (trace_steps' with "Hs") as (l' s' HRel') "[Hl' Hs']"; [done|].
  iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %->. iExists _. iFrame. done.
Qed.

Section stenning_ex.

  Inductive actor := A | B.

  Inductive stenning_A_state :=
  | ASending
  | AReceiving.

  Inductive stenning_B_state :=
  | BSending
  | BReceiving.

  Definition stenning_state : Set := (stenning_A_state * nat) * (stenning_B_state * nat).

  Definition Message : Set := actor * nat * actor.
  Inductive stenning_action : Set := Send (m:Message) | Recv (b:actor) (o:option Message).
  Definition stenning_label : Set := actor * stenning_action.
  Definition saA : actor := A.
  Definition saB : actor := B.
  Definition Arole : actor := A.
  Definition Brole : actor := B.

  Definition mAB n : Message := (saA, n, saB).
  Definition mBA n : Message := (saB, n, saA).

  Inductive stenning_trans :
    stenning_state → stenning_label → stenning_state → Prop :=
  | A_Send n stB :
    stenning_trans ((ASending, n), stB)
      (Arole, Send $ mAB n)
      ((AReceiving, n), stB)
  | A_RecvFail n stB omsg :
    omsg ≠ Some $ mBA n →
    stenning_trans ((AReceiving, n), stB)
      (Arole, Recv saA omsg)
      ((ASending, n), stB)
  | A_RecvSucc n stB omsg :
    omsg = Some $ mBA n →
    stenning_trans ((AReceiving, n), stB)
      (Arole, Recv saA omsg)
      ((ASending, (S n)), stB)
  | B_Send stA n :
    stenning_trans (stA, (BSending, n))
      (Brole, Send (mBA (n)))
      (stA, (BReceiving, n))
  | B_RecvFailEmpty stA n omsg:
    omsg = None →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BReceiving, n))
  | B_RecvFail stA n m omsg:
    omsg = Some $ m →
    m ≠ mAB (S n) →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BSending, n))
  | B_RecvSucc stA n omsg :
    omsg = Some $ mAB (S n) →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BSending, (S n)))
  .

  Notation tProp := (tProp stenning_state stenning_label stenning_trans).

  Instance stenning_state_inhabited : Inhabited stenning_state := populate ((ASending, 0), (BSending, 0)).

  Instance stenning_label_inhabited : Inhabited stenning_label := populate (A, Recv A None).

  Definition ltl_now_state_A st : tProp :=
    ∃ sB, ↓s (st,sB).
  Notation "↓sA st" := (ltl_now_state_A st) (at level 20, right associativity) : bi_scope.

  Definition ltl_now_state_B st : tProp :=
    ∃ sA, ↓s (sA,st).
  Notation "↓sB st" := (ltl_now_state_B st) (at level 20, right associativity) : bi_scope.

  Definition ltl_now_label_label lbl : tProp :=
    (∃ a, ↓l (lbl,a)).
  Notation "↓ll lbl" := (ltl_now_label_label lbl) (at level 20, right associativity) : bi_scope.

  Instance stenning_ltl : LTL stenning_state stenning_label stenning_trans.
  Proof. constructor. intros. apply make_decision. Qed.

  Axiom fair_sched : ∀ (b:actor), ⊢ (◊ ↓ll b):tProp.

  (* OBS: Needs assumption that no rogue messages are received *)
  Axiom fair_net :
    ∀ (saA:actor) (Φ: nat → Prop) (saB:actor),
    ⊢
    (□ ◊ (∃ (m:nat), ⌜Φ m⌝ ∧ ↓l (saA, Send (saA, m, saB))))
    →
    (□ ◊ ∃ om, ↓l (saB, Recv saB om))
    →
    ◊ (∃ (m:nat), ⌜Φ m⌝ ∧ ↓l (saB, Recv saB (Some (saA, m, saB))))
    : tProp.

  Lemma stenning_ASending_A i :
    ↓sA (ASending,i) ∧ ↓ll A ⊢ ↓l (A, Send (mAB i)) ∧ ○ ↓sA (AReceiving,i) : tProp.
  Proof.
    iIntros "[Hs HA]".
    iDestruct "Hs" as (stB) "Hs". 
    iDestruct "HA" as (l) "HA".
    iDestruct (ltl_dup with "HA") as "[HA HA']".
    iDestruct (trace_steps with "[Hs HA]") as  (s' Hsteps') "Hs'".
    { eexists _,_. econstructor. }
    { iFrame. }
    inversion Hsteps'; simplify_eq.
    iFrame. iModIntro.
    iExists _. done.
  Qed.

  Lemma stenning_AReceiving_A i :
    ↓sA (AReceiving,i) ∧ ↓ll A ⊢
    ∃ omsg, 
      (⌜omsg ≠ Some $ mBA i⌝ ∧ ↓l (A,Recv saA omsg) ∧ ○ ↓sA (ASending, i)) ∨
      (⌜omsg = Some $ mBA i⌝ ∧ ↓l (A,Recv saA omsg) ∧ ○ ↓sA (ASending, S i)).
  Proof.
    iIntros "[Hs HA]".
    iDestruct "Hs" as (stB) "Hs". 
    iDestruct "HA" as (l) "HA".
    iDestruct (ltl_dup with "HA") as "[HA HA']".
    iDestruct (trace_steps with "[$Hs $HA]") as  (s' Hsteps') "Hs'".
    { eexists (_,Recv _ None),_. econstructor. eauto. }
    inversion Hsteps'; simplify_eq.
    - iExists omsg. iLeft. iFrame. iSplit; [eauto|]. iModIntro. iExists _. iFrame.
    - iExists (Some (mBA i)). iRight. iFrame. iSplit; [eauto|]. iModIntro. iExists _. iFrame.
  Qed.

  Lemma stenning_reducible s :
    reducible s.
  Proof.
    destruct s as [[[] i] [[] j]].
    - eexists _, _. econstructor.
    - eexists _, _. econstructor.
    - eexists (_,Recv _ None),_. econstructor. eauto.
    - eexists (_,Recv _ None),_. econstructor. eauto.
  Qed.

  Lemma stenning_A_B stA :
    ↓sA stA ∧ ↓ll B ⊢ ○ ↓sA stA.
  Proof.
    iIntros "[Hs HA]".
    iDestruct "Hs" as (stB) "Hs". 
    iDestruct "HA" as (l) "HA".
    iDestruct (ltl_dup with "HA") as "[HA HA']".
    iDestruct (trace_steps with "[$Hs $HA]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq.
    - iModIntro. iExists _. iFrame.
    - iModIntro. iExists _. iFrame.
    - iModIntro. iExists _. iFrame.
    - iModIntro. iExists _. iFrame.
  Qed.

  Lemma stenning_BReceiving_B i :
    ↓sB (BReceiving,i) ∧ ↓ll B ⊢
    ∃ omsg, 
      (⌜omsg = None⌝ ∧ ↓l (B,Recv saB omsg) ∧ ○ ↓sB (BReceiving, i)) ∨
      (∃ m, ⌜omsg = Some m⌝ ∧ ⌜m ≠ mAB (S i)⌝ ∧ ↓l (B,Recv saB omsg) ∧ ○ ↓sB (BSending, i)) ∨
      (⌜omsg = Some $ mAB (S i)⌝ ∧ ↓l (B,Recv saB omsg) ∧ ○ ↓sB (BSending, S i)).
  Proof.
    iIntros "[Hs Hl]".
    iDestruct "Hs" as (stA) "Hs". 
    iDestruct "Hl" as (l) "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (trace_steps with "[$Hs $Hl]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq.
    - iExists None. iLeft. iFrame. iSplit; [eauto|]. iModIntro. iExists _. iFrame.
    - iExists _. iRight. iLeft. iExists _. iFrame. iSplit; [eauto|]. iSplit; [eauto|].
      iModIntro. iExists _. iFrame.
    - iExists _. iRight. iRight. iFrame. iSplit; [eauto|]. iModIntro. iExists _. iFrame.
  Qed.

  Lemma stenning_BSending_B i :
    ↓sB (BSending,i) ∧ ↓ll B ⊢ ↓l (B, Send (mBA i)) ∧ ○ ↓sB (BReceiving,i) : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct "Hs" as (stA) "Hs". 
    iDestruct "Hl" as (l) "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (trace_steps with "[$Hs $Hl]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq.
    iFrame. iModIntro. iExists _. iFrame.
  Qed.    

  Lemma stenning_B_A stB :
    ↓sB stB ∧ ↓ll A ⊢ ○ ↓sB stB.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct "Hs" as (stA) "Hs". 
    iDestruct "Hl" as (l) "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (trace_steps with "[$Hs $Hl]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq.
    - iModIntro. iExists _. iFrame.
    - iModIntro. iExists _. iFrame.
    - iModIntro. iExists _. iFrame.
  Qed.

  (* TODO: Remove *)
  Lemma stenning_baz a b :
    ↓l (a,b) ⊢ ↓ll a.
  Proof. iIntros "H". iExists _. iFrame. Qed.

  Lemma ltl_dup (P : tProp) : P ⊢ P ∧ P.
  Proof. iIntros "H". iFrame. Qed.

  Lemma stenning_split stA stB :
    ↓s (stA, stB) ⊢ ↓sA stA ∧ ↓sB stB.
  Proof. iIntros "H". iSplit; iFrame. Qed.

  Lemma ltl_now_A_agree x y :
    ⊢ ↓sA x → ↓sA y → ⌜x = y⌝.
  Proof.
    rewrite /ltl_now_state_A.
    iDestruct 1 as (?) "H1".
    iDestruct 1 as (?) "H2".
    iDestruct (ltl_now_state_agree with "H1 H2") as %Heq. simplify_eq.
    done.
  Qed.

  Lemma ltl_now_B_agree x y :
    ⊢ ↓sB x → ↓sB y → ⌜x = y⌝.
  Proof.
    rewrite /ltl_now_state_A.
    iDestruct 1 as (?) "H1".
    iDestruct 1 as (?) "H2".
    iDestruct (ltl_now_state_agree with "H1 H2") as %Heq. simplify_eq.
    done.
  Qed.

  (* OBS: Does not hold, as trace might be terminated *)
  Lemma ltl_st : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ∃ s, ↓s s : tProp.
  Proof.
    econstructor. unseal. rewrite /ltl_now_state /ltl_now_label.
    rewrite ltl_now_unseal. intros.
    destruct tr. destruct tr_car.
    - destruct t; exists s; eauto.
      + econstructor. done.
      + econstructor. done.
    - eexists inhabitant. econstructor. apply empty_ind.
      destruct H.
      + destruct H. inversion H. done.
      + destruct H. inversion H. done.
  Qed.

  Lemma ltl_lbl : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ∃ l, ↓l l : tProp.
  Proof.
    econstructor. unseal. rewrite /ltl_now_state /ltl_now_label.
    rewrite ltl_now_unseal. intros.
    destruct H; [|done].
    destruct tr. destruct tr_car.
    - destruct t.
      + exfalso. apply empty_ind. inversion tr_wf. simplify_eq.
        exfalso. destruct s as [[[]] []]; eapply H1; econstructor.
        instantiate (1:=None). eauto.
      + inversion H. inversion H0. simplify_eq. econstructor. econstructor. done.
    - eexists inhabitant. econstructor. apply empty_ind. inversion H.
      inversion H0. done.
  Qed.

  Lemma stenning_A : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ∃ stA, ↓sA stA : tProp.
  Proof.
    iIntros "Hs". iDestruct (ltl_st with "Hs") as ([]) "Hs".
    iExists _, _. iFrame.
  Qed.

  Lemma stenning_B : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ∃ stB, ↓sB stB : tProp.
  Proof.
    iIntros "Hs". iDestruct (ltl_st with "Hs") as ([]) "Hs".
    iExists _, _. iFrame.
  Qed.

  Lemma stenning_A_or_B :
    (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ↓ll A ∨ ↓ll B.
  Proof.
    iIntros "H".
    iDestruct (ltl_lbl with "H") as ([[]]) "H". 
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma stenning_A_send i :
    ↓sA ((ASending, i)) ⊢ ◊ (↓sA ((ASending, i)) ∧ ↓l (saA, Send (mAB i))) : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (fair_sched A) as "H".
    iRevert "Hs".
    iApply (ltl_eventually_ind with "[] H").
    iIntros "!> [H1|H2]".
    { iIntros "H'". iDestruct "H1" as "HA".
      iDestruct (ltl_dup with "H'") as "[H' H'']".
      iDestruct (stenning_ASending_A with "[$H' $HA]") as "[Hs Hl]".
      iModUnIntro. iFrame. }
    iDestruct "H2" as "[H1 H2]".
    iIntros "H'".
    iDestruct (ltl_dup with "H'") as "[H' H'']".
    iDestruct (ltl_dup with "H''") as "[H'' H''']".
    iDestruct (stenning_A_or_B with "[H''']") as "[HA|HB]".
    { iLeft. iDestruct "H'''" as (?) "H'". iExists _.  iFrame. }
    { iDestruct (stenning_ASending_A with "[$H' $HA]") as "[Hs Hl]".
      iModUnIntro. iFrame. }
    iDestruct (stenning_A_B with "[$H' $HB]") as "Hs".
    iEval (rewrite -ltl_next_eventually). 
    iModIntro.    
    by iApply ("H2").
  Qed.

  Lemma stenning_disjoint_A stA : 
    ↓sA stA ⊢ ◊ (↓sA stA ∧ ↓ll A).
  Proof.
    iDestruct (fair_sched A) as "Hl".
    iApply (ltl_eventually_ind with "[] Hl").
    iIntros "!> [H|[H IH]] Hs".
    { iModUnIntro. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".    
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct "Hs'" as (?) "Hs'". iExists _. iFrame. }
    { iModUnIntro. iFrame. }
    iDestruct (stenning_A_B with "[$Hs $HB]") as "Hs".
    iEval (rewrite -ltl_next_eventually). iModIntro.
    by iApply "IH".
  Qed.

  Lemma stenning_disjoint_B stB : 
    ↓sB stB ⊢ ◊ (↓sB stB ∧ ↓ll B).
  Proof.
    iDestruct (fair_sched B) as "Hl".
    iApply (ltl_eventually_ind with "[] Hl").
    iIntros "!> [H|[H IH]] Hs".
    { iModUnIntro. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".    
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct "Hs'" as (?) "Hs'". iExists _. iFrame. }
    - iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
      iEval (rewrite -ltl_next_eventually). iModIntro.
      by iApply "IH".
    - iModUnIntro. iFrame. 
  Qed.

  Lemma stenning_2_succ i :
    ↓sA (AReceiving, i) ∧
    ↓l (saA, Recv saA (Some $ mBA i))
    ⊢ ○ ↓sA (ASending, S i)
    : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (stenning_AReceiving_A with "[$Hs $Hl]") as (m) "[H|H]".
    { iDestruct "H" as (Heq) "[Hl Hs]".
      iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'. simplify_eq. }
    iDestruct "H" as (->) "[Hl Hs]".
    iFrame.
  Qed.

  Lemma stenning_A_eventually_advance i :
    ↓sA (ASending, i) ∧
    ◊ ↓l (saA, Recv saA (Some $ mBA i))
    ⊢ ◊ ↓sA (ASending, S i)
    : tProp.
  Proof.
    assert (∃ stA, ASending = stA) as [stA Heq].
    { eauto. }
    rewrite {1}Heq. clear Heq.
    iIntros "[Hs Hl]". iRevert (stA) "Hs".
    iApply (ltl_eventually_ind with "[] Hl").
    iIntros "!> [Hl|H]"; iIntros (stA) "Hs".
    { destruct stA.
      - rewrite -ltl_eventually_next.
        iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
        iDestruct (stenning_ASending_A with "[$Hs $Hl]") as "[Hl Hs]".
        iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'. simplify_eq.
      - rewrite -ltl_next_eventually. iDestruct (stenning_2_succ with "[$Hl $Hs]") as "Hs".
        iModIntro. iMod (stenning_disjoint_A with "Hs") as "[Hs Hl]".
        iModUnIntro. iFrame. }
    iDestruct "H" as "[H' IH]".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. } 
    2: { iDestruct (stenning_A_B with "[$Hs $HB]") as "Hs".
      iEval (rewrite -ltl_next_eventually).
      iModIntro. by iApply "IH". }
    destruct stA.
    - iDestruct (stenning_ASending_A with "[$Hs $HA]") as "[Hl Hs]".
      iEval (rewrite -ltl_next_eventually).
      iModIntro.
      by iApply "IH".
    - iDestruct (stenning_AReceiving_A with "[$Hs $HA]")
        as (m) "[[%Hm [Hl Hs]]|[%Hm [Hl Hs]]]".
      + iEval (rewrite -ltl_next_eventually).
        iModIntro.
        iDestruct ("IH" with "Hs") as ">Hs".
        iModUnIntro. done.
      + iEval (rewrite -ltl_next_eventually).
        iModIntro. iModUnIntro. done.
  Qed. 

  Lemma stenning_A_always_send i :
    (□ ¬ ↓sA (ASending, S i)) ∧ 
    ↓sA (ASending, i) ⊢ □ ◊ (↓sA (ASending, i) ∧ ↓l (saA, Send (mAB i))) : tProp.
  Proof.
    iIntros "[#Hm Hs]".
    iMod (stenning_A_send with "Hs") as "[Hs Hl]".
    iApply (ltl_always_intro with "[] [Hs Hl]"); last first.
    { iModUnIntro. iFrame. }
    iIntros "!> >[Hs Hl]".
    iDestruct (stenning_ASending_A with "[$Hs Hl]") as "[Hl' Hs]".
    { by iApply stenning_baz. }
    iModIntro.
    iDestruct (stenning_disjoint_A with "Hs") as ">[Hs Hl]".
    iDestruct (stenning_AReceiving_A with "[$Hs $Hl]") as (m') "[(%Hm&Hl'&Hs)|(%Hm&Hl'&Hs)]".
    { rewrite -ltl_next_eventually. iModIntro. by iApply stenning_A_send. }
    subst.
    iExFalso.
    iApply ltl_false_next. iModIntro.
    iApply "Hm". done.
  Qed.

  Lemma stenning_A_try_recv i :
    ↓sA ((ASending, i)) ⊢ ◊ ∃ om : option Message, ↓sA ((AReceiving, i)) ∧ ↓l (saA, Recv saA om)
    : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (stenning_A_send with "Hs") as ">[Hs Hl]".
    iDestruct (stenning_ASending_A with "[$Hs Hl]") as "[Hl Hs]".
    { by iApply stenning_baz. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    iDestruct (fair_sched A) as "H".
    iRevert "Hs".
    iApply (ltl_eventually_ind with "[] H").
    iIntros "!> [Hl|[_ IH]] Hs".
    { iDestruct (ltl_dup with "Hs") as "[Hs Hs']".      
      iDestruct (stenning_AReceiving_A with "[$Hs $Hl]") as (m) "[(?&?&?)|(?&?&?)]".
      - iModUnIntro. iExists m. iFrame.
      - iModUnIntro. iExists m. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. } 
    - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (stenning_AReceiving_A with "[$Hs $HA]") as (m) "[(?&?&?)|(?&?&?)]".
      + iModUnIntro. iExists m. iFrame.
      + iModUnIntro. iExists m. iFrame.
    - iDestruct (stenning_A_B with "[$Hs $HB]") as "H'".
      iEval (rewrite -ltl_next_eventually). iModIntro. by iApply "IH".
  Qed.

  Lemma ltl_always_eventually_intro (P Q : tProp) :
    ⊢ □ (P → ◊ Q) → □ (Q → ○ ◊ P) → P → □ ◊ Q.
  Proof.
    iIntros "#HPQ #HQP HP". iDestruct ("HPQ" with "HP") as "HQ".
    iApply ltl_always_intro; [|done].
    iIntros "!>". iIntros ">HQ".
    iDestruct ("HQP" with "HQ") as "HP".
    iModIntro. iMod "HP". iApply "HPQ". done.
  Qed.

  Lemma stenning_A_always_try_recv i :
    (□ ¬ ↓sA (ASending, S i)) ∧ ↓sA (ASending, i)
    ⊢ □ ◊ ∃ om : option Message, ↓sA ((AReceiving, i)) ∧ ↓l (saA, Recv saA om)
    : tProp.
  Proof. 
    iIntros "[#Hm Hs]".
    iMod (stenning_A_try_recv with "Hs") as "[%m [Hs Hl]]".
    iApply (ltl_always_intro with "[] [Hs Hl]"); last first.
    { iModUnIntro. iFrame. }
    iIntros "!> >[%m' [Hs Hl]]".
    iDestruct (stenning_AReceiving_A with "[$Hs Hl]") as (m'') "[H1|H2]".
    { by iApply stenning_baz. }
    - iDestruct "H1" as (?) "[Hl Hs]".
      iModIntro.
      iMod (stenning_A_try_recv with "Hs") as "[%m''' [Hs Hl]]".
      iExists _. iFrame.
    - iDestruct "H2" as (->) "[Hl Hs]".
      iModIntro. iExFalso. iApply "Hm". done.
  Qed.

  Axiom stenning_safety_inv :
    ⊢ ∃ i stA stB, ↓sA (stA,S i) ∧ (↓sB (stB,S i) ∨ ↓sB (stB,i)).

  Lemma stenning_B_always_try_recv :
    (□ ◊ ∃ l, ↓l l)
    ⊢ □ ◊ ∃ m, ↓l (saB, Recv saB m) : tProp.
  Proof.
    iIntros "#Hl !>". iMod "Hl".
    iDestruct (stenning_B with "[$Hl]") as (stB) "Hs".
    iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
    destruct stB as [[|] i].
    - iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
      iEval (rewrite -ltl_next_eventually). iModIntro.
      iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
      iDestruct (stenning_BReceiving_B with "[$Hs $Hl]")
        as (m) "[(?&?&?)|[(%m'&?&?&?&?)|(?&?&?)]]".
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
    - iDestruct (stenning_BReceiving_B with "[$Hs $Hl]")
        as (m) "[(?&?&?)|[(%m'&?&?&?&?)|(?&?&?)]]".
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
  Qed.

  Lemma stenning_B_recv i :
    □ ◊ ↓l (saA, Send (mAB i)) ⊢
    ◊ ↓l (saB, Recv saB $ Some (mAB i)) : tProp.
  Proof.
    iIntros "#H".
    iDestruct (stenning_B_always_try_recv with "[H]") as "#HB".
    { iModIntro. iMod "H". iModUnIntro. iExists _. iFrame. }
    iDestruct (fair_net _ (λ m, m = i) with "[H] HB") as "H'".
    { iModIntro. iMod "H". iModUnIntro. iExists i. iFrame. eauto. }
    iMod "H'" as (m ->) "H''".
    iModUnIntro. done.
  Qed.

  Lemma stenning_B_send i :
    ⊢
    □ (∃ stA, ↓sA (stA,i)) →
    □ ◊ ↓l (saB, Recv saB $ Some (mAB i)) →
    □ ◊ ↓l (saB, Send (mBA i))
    : tProp.
  Proof.
    iIntros "#Hst #Hrecv". iModIntro.
    iAssert (∃ stA : stenning_A_state, ↓sA (stA, i))%I as "Hst'"; [by done|].
    iDestruct "Hst'" as (stA) "Hst'".
    iDestruct (stenning_safety_inv) as (j stA' stB) "[HstA HstB]".
    iDestruct (ltl_now_A_agree with "Hst' HstA") as %Heq.
    simplify_eq. iClear "Hst' HstA".
    iDestruct "HstB" as "[Hs|Hs]".
    - 
      iDestruct (ltl_until_foo with "Hrecv") as "Hrecv'".
      rewrite left_id.
      iRevert "Hs". iRevert (stB).
      iApply (ltl_until_ind with "[] Hrecv'").
      iIntros "!> [Hl|(Hl&H&IH)]"; iIntros (stB) "Hs".
      { destruct stB.
        { iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
          iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
          iModUnIntro. done. }
        iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
        iDestruct (stenning_BReceiving_B with "[$Hs Hl]") as "H".
        { by iApply stenning_baz. }
        iDestruct "H" as (m) "[H|[H|H]]".
        + iDestruct "H" as (->) "[Hl Hs]".
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
          simplify_eq.
        + iDestruct "H" as (m' ->) "[%Heq [Hl Hs]]".
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'.
          simplify_eq.
          iEval (rewrite -ltl_next_eventually). iModIntro.
          iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
          iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
          iModUnIntro. done.          
        + iDestruct "H" as (->) "[Hl Hs]".
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'.
          simplify_eq. lia. }
      destruct stB.
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BSending_B with "[$Hs $HB]") as "[Hl' Hs]".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BReceiving_B with "[$Hs $HB]") as (m) "[Hs|[Hs|Hs]]".
          -- iDestruct "Hs" as "(?&?&Hs)". 
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as (m') "(?&?&?&Hs)". 
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as (->) "(?&Hs)".
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             iDestruct "Hst" as (?) "Hst".
             iDestruct (stenning_safety_inv) as (i stA'' stB') "[HstA HstB]".
             iDestruct "HstB" as "[H1|H2]".
             ++ iDestruct (ltl_now_A_agree with "Hst HstA") as %Heq.
                simplify_eq.
                iDestruct (ltl_now_B_agree with "Hs H1") as %Heq.
                simplify_eq.
                lia.
             ++ iDestruct (ltl_now_A_agree with "Hst HstA") as %Heq.
                simplify_eq.
                iDestruct (ltl_now_B_agree with "Hs H2") as %Heq.
                simplify_eq.
                lia.
    - iDestruct (ltl_until_foo with "Hrecv") as "Hrecv'".
      rewrite left_id.
      iRevert "Hs". iRevert (stB).
      iApply (ltl_until_ind with "[] Hrecv'").
      iIntros "!> [Hl|(Hl&H&IH)]"; iIntros (stB) "Hs".
      { destruct stB.
        - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
          iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
          iDestruct (stenning_BSending_B with "[$Hs Hl]") as "[Hl Hs]".
          { by iApply stenning_baz. }
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
          simplify_eq.
        - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
          iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
          iDestruct (stenning_BReceiving_B with "[$Hs Hl]") as "H".
          { by iApply stenning_baz. }
          iDestruct "H" as (m) "[H|[H|H]]".
          + iDestruct "H" as (->) "[Hl Hs]".
            iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
            simplify_eq.
          + iDestruct "H" as (m' ->) "[%Heq [Hl Hs]]".
            iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'.
            simplify_eq.
          + iDestruct "H" as (->) "[Hl Hs]".
            iEval (rewrite -ltl_next_eventually). iModIntro.
            iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
            iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
            iModUnIntro. done. }
      destruct stB.
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BSending_B with "[$Hs $HB]") as "[Hl' Hs]".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BReceiving_B with "[$Hs $HB]") as (m) "[Hs|[Hs|Hs]]".
          -- iDestruct "Hs" as "(?&?&Hs)". 
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as (m') "(?&?&?&Hs)". 
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as(->)  "(?&Hs)".
             rewrite /saB. iExFalso. iApply "Hl". done. 
  Qed.

  Lemma stenning_A_foo i :
    ⊢ □ (¬ ↓sA (ASending, S i)) → ↓sA (ASending, i) →  □ ∃ stA', ↓sA (stA', i).
  Proof.
    iIntros "#Hm Hs".
    iApply ltl_always_intro; last first.
    { iExists _. done. }
    iIntros "!> [%stA' Hs]".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct "Hs'" as (?) "Hs'". iFrame. }
    2: { iDestruct (stenning_A_B with "[$Hs $HB]") as "H".
      iModIntro. iExists _. iFrame. }
    destruct stA'.
    - iDestruct (stenning_ASending_A with "[$Hs $HA]") as "[Hl Hs]".
      iModIntro. iExists _. done.
    - iDestruct (stenning_AReceiving_A with "[$Hs $HA]") as (m) "[H|H]".
      + iDestruct "H" as "(?&?&?)". iModIntro. iFrame.
      + iDestruct "H" as "(?&?&?)".
        iModIntro. iExFalso. iApply "Hm". done. 
  Qed.

  Lemma stenning_A_advances i :
    ↓sA ((ASending, i)) ⊢ ◊ ↓sA ((ASending, S i)) : tProp.
  Proof.
    iIntros "HA".
    iAssert (◊ ↓sA (ASending, S i) ∨ □ ¬ ↓sA (ASending, S i))%I as "[$|#Hm]".
    { iDestruct (ltl_excluded_middle (◊ ↓sA (ASending, S i))) as "[H|H]".
      { by iLeft. }
      iRight. by iApply ltl_not_eventually_always_not. }
    iDestruct (ltl_dup with "HA") as "[HA1 HA2]".
    iDestruct (ltl_dup with "HA2") as "[HA2 HA3]".
    iDestruct (fair_net _ (λ m, m = i) A with "[HA1] [HA2]") as "Hfair"; last first.
    { 
      iApply (stenning_A_eventually_advance with "[$HA3 Hfair]").
      iMod "Hfair". iModUnIntro. iDestruct "Hfair" as (m ->) "Hfair". done. }
    { iDestruct (stenning_A_always_try_recv with "[$Hm $HA2]") as "#H".
      iIntros "!>". iMod "H" as (m) "[_ H]". iModUnIntro. eauto. }
    { iDestruct (stenning_A_always_send with "[$Hm $HA1]") as "#H".
      iDestruct (stenning_B_recv with "[H]") as "H'".
      { iModIntro. iMod "H". iModUnIntro. iDestruct "H" as "[_ $]". }
      iDestruct (stenning_B_send with "[Hm HA1] H'") as "#H''".
      { by iApply stenning_A_foo. }
      iIntros "!>". iMod "H''". iModUnIntro. iFrame. done. }
  Qed.

  Theorem stenning_live i :
    ↓sA (ASending, 0) ⊢ ◊ (↓sA (ASending, i)) : tProp.
  Proof.
    iIntros "H".
    rewrite -ltl_eventually_idemp.
    iDestruct (stenning_A_send with "H") as ">[Hs Hl]".
    iModUnIntro.
    iStopProof.
    induction i.
    { rewrite -ltl_eventually_intro_now. iIntros "[$ _]". }
    iIntros "[Hs Hl]".
    iDestruct (IHi with "[$Hs $Hl]") as ">Hs".
    iDestruct (stenning_A_advances with "Hs") as ">Hs".
    iModUnIntro.
    iFrame.
  Qed.

  Theorem stenning_live_label i :
    ↓sA (ASending, 0) ⊢ ◊ (↓l (saA, Send (mAB i))) : tProp.
  Proof.
    iIntros "H".
    iDestruct (stenning_live i with "H") as ">H".
    iDestruct (stenning_A_send with "H") as ">[_ Hl]".
    iModUnIntro. done.
  Qed.

End stenning_ex.
