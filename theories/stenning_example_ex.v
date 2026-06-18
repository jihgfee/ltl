From ltl Require Import ltl classical.

Section foo.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_now_state st : tProp :=
    (↓ (λ osl, (match osl with
                              | Some (s,_) => s = st
                              | _ => False
                              end):Prop))%I.

  Definition ltl_now_label lbl : tProp :=
    (↓ (λ osl, (match osl with
                | Some (s,Some l) => l = lbl
                | _ => False
                end):Prop))%I.

End foo.

Arguments ltl_now_state {_ _ _} _ : simpl never.
Arguments ltl_now_label {_ _ _} _ : simpl never.

Notation "↓s st" := (ltl_now_state st) (at level 20, right associativity) : bi_scope.

Notation "↓l lbl" := (ltl_now_label lbl)%I (at level 20, right associativity) : bi_scope.

(* Notation "↓s st" := (↓ (λ osl, (match osl with *)
(*                               | Some (s,_) => s = st *)
(*                               | _ => False *)
(*                               end):Prop))%I (at level 20, right associativity) : bi_scope.  *)

(* Notation "↓l lbl" := (↓ (λ osl, (match osl with *)
(*                               | Some (s,Some l) => l = lbl *)
(*                               | _ => False *)
(*                               end):Prop))%I (at level 20, right associativity) : bi_scope.  *)

(* Notation "↓s Φ" := (↓ (λ osl, (match osl with *)
(*                               | Some (s,l) => Φ (Some s) *)
(*                               | None => Φ None *)
(*                               end):Prop))%I (at level 20, right associativity) : bi_scope.  *)

(* Notation "↓l Φ" := (↓ (λ osl, (match osl with *)
(*                               | Some (s,Some l) => Φ (Some l) *)
(*                               | Some (s,None) => Φ None *)
(*                               | None => Φ None *)
(*                               end):Prop))%I (at level 20, right associativity) : bi_scope.  *)

Import tProp.

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
      ((ASending, (1+n)), stB)
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
    m ≠ mAB n →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BSending, n))
  | B_RecvSucc stA n omsg :
    omsg = Some $ mAB (1+n) →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BSending, (1+n)))
  .

  Notation tProp := (tProp stenning_state stenning_label stenning_trans).

  Definition ltl_now_state_A st : tProp :=
    (↓ (λ osl, (match osl with
                              | Some (s,_) => s.1 = st
                              | _ => False
                              end):Prop))%I.
  Notation "↓sA st" := (ltl_now_state_A st) (at level 20, right associativity) : bi_scope.


  Definition ltl_now_state_B st : tProp :=
    (↓ (λ osl, (match osl with
                              | Some (s,_) => s.2 = st
                              | _ => False
                              end):Prop))%I.
  Notation "↓sB st" := (ltl_now_state_B st) (at level 20, right associativity) : bi_scope.

  Definition ltl_now_label_label lbl : tProp :=
    (↓ (λ osl, (match osl with
                              | Some (_,l) => option_map fst l = Some lbl
                              | _ => False
                              end):Prop))%I.
  Notation "↓sA st" := (ltl_now_state_A st) (at level 20, right associativity) : bi_scope.
  Notation "↓ll lbl" := (ltl_now_label_label lbl) (at level 20, right associativity) : bi_scope.

  Axiom fair_sched :
    ∀ (b:actor), ⊢ (◊ ↓ll b):tProp.

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


  (* Needs that state is correct one *)
  Lemma stenning_2 i :
    ↓l (saA, Recv saA (Some $ mBA i))
    ⊢ ○ ↓sA (ASending, S i)
    : tProp.
  Proof. Admitted.

  Lemma stenning_ASending_A i :
    ↓sA (ASending,i) ∧ ↓ll A ⊢ ↓l (A, Send (mAB i)) ∧ ○ ↓sA (AReceiving,i) : tProp.
  Proof. Admitted.

  Lemma stenning_AReceiving_A i :
    ↓sA (AReceiving,i) ∧ ↓ll A ⊢
    ∃ omsg, 
      (⌜omsg ≠ Some $ mBA i⌝ ∧ ↓l (A,Recv saA omsg) ∧ ○ ↓sA (ASending, i)) ∨
      (⌜omsg = Some $ mBA i⌝ ∧ ↓l (A,Recv saA omsg) ∧ ○ ↓sA (ASending, S i)).
  Proof. Admitted.

  Lemma stenning_A_B stA :
    ↓sA stA ∧ ↓ll B ⊢ ○ ↓sA stA.
  Proof. Admitted.

  Lemma stenning_BReceiving_B i :
    ↓sB (BReceiving,i) ∧ ↓ll B ⊢
    ∃ omsg, 
      (⌜omsg = None⌝ ∧ ↓l (B,Recv saB omsg) ∧ ○ ↓sB (BReceiving, i)) ∨
      (∃ m, ⌜omsg = Some m⌝ ∧ ⌜m ≠ mAB (S i)⌝ ∧ ↓l (B,Recv saB omsg) ∧ ○ ↓sB (BSending, i)) ∨
      (⌜omsg = Some $ mAB (S i)⌝ ∧ ↓l (B,Recv saB omsg) ∧ ○ ↓sB (BSending, S i)).
  Proof. Admitted.

  Lemma stenning_BSending_B i :
    ↓sB (BSending,i) ∧ ↓ll B ⊢ ↓l (B, Send (mBA i)) ∧ ○ ↓sB (BReceiving,i) : tProp.
  Proof. Admitted.

  Lemma stenning_B_A stB :
    ↓sB stB ∧ ↓ll A ⊢ ○ ↓sB stB.
  Proof. Admitted.

  Lemma stenning_A_or_B :
    ⊢ ↓ll A ∨ ↓ll B.
  Proof. Admitted.

  Lemma stenning_baz a b :
    ↓l (a,b) ⊢ ↓ll a.
  Proof. Admitted.

  Lemma ltl_dup (P : tProp) : P ⊢ P ∧ P.
  Proof. iIntros "H". iFrame. Qed.

  Lemma stenning_split stA stB :
    ↓s (stA, stB) ⊢ ↓sA stA ∧ ↓sB stB.
  Proof. Admitted.


  Lemma ltl_now_agree x y :
    ⊢ ↓sA x → ↓sA y → ⌜x = y⌝.
  Proof. Admitted.

  Lemma ltl_now_B_agree x y :
    ⊢ ↓sB x → ↓sB y → ⌜x = y⌝.
  Proof. Admitted.

  Lemma ltl_now_lbl_agree (x y : stenning_label) :
    ⊢ ↓l x → ↓l y → ⌜x = y⌝ : tProp.
  Proof. Admitted.    

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
    iDestruct stenning_A_or_B as "[HA|HB]".
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
    iDestruct stenning_A_or_B as "[HA|HB]".
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
    iDestruct stenning_A_or_B as "[HA|HB]"; last first.
    { iModUnIntro. iFrame. }
    iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
    iEval (rewrite -ltl_next_eventually). iModIntro.
    by iApply "IH".
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
    iDestruct (stenning_A_or_B) as "[HA'|HB]".
    - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (stenning_AReceiving_A with "[$Hs $HA']") as (m) "[(?&?&?)|(?&?&?)]".
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

  Lemma stenning_B : ⊢ ∃ stB, ↓sB stB : tProp.
  Proof. Admitted.
  
  Lemma stenning_B_always_try_recv :
    ⊢ □ ◊ ∃ m, ↓l (saB, Recv saB m) : tProp.
  Proof.
    iIntros "!>".
    iDestruct stenning_B as (stB) "Hs".
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
    iDestruct stenning_B_always_try_recv as "#HB".
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
    iDestruct (ltl_now_agree with "Hst' HstA") as %Heq.
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
      + iDestruct stenning_A_or_B as "[HA|HB]".
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BSending_B with "[$Hs $HB]") as "[Hl' Hs]".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
      + iDestruct stenning_A_or_B as "[HA|HB]".
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
             ++ iDestruct (ltl_now_agree with "Hst HstA") as %Heq.
                simplify_eq.
                iDestruct (ltl_now_B_agree with "Hs H1") as %Heq.
                simplify_eq.
                lia.
             ++ iDestruct (ltl_now_agree with "Hst HstA") as %Heq.
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
      + iDestruct stenning_A_or_B as "[HA|HB]".
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BSending_B with "[$Hs $HB]") as "[Hl' Hs]".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
      + iDestruct stenning_A_or_B as "[HA|HB]".
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
    iDestruct stenning_A_or_B as "[HA|HB]"; last first.
    { iDestruct (stenning_A_B with "[$Hs $HB]") as "H".
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
    iApply ltl_eventually_next.
    iApply stenning_2.
    iDestruct (ltl_dup with "HA") as "[HA1 HA2]".
    iDestruct (fair_net _ (λ m, m = i) with "[HA1] [HA2]") as "Hfair"; last first.
    { iMod "Hfair" as (m ->) "Hfair". by iModUnIntro. }
    { iDestruct (stenning_A_always_try_recv with "[$Hm $HA2]") as "#H".
      iIntros "!>". iMod "H" as (m) "[_ H]". iModUnIntro. eauto. }
    { iDestruct (stenning_A_always_send with "[$Hm $HA1]") as "#H".
      iDestruct (stenning_B_recv with "[H]") as "H'".
      { iModIntro. iMod "H". iModUnIntro. iDestruct "H" as "[_ $]". }
      iDestruct (stenning_B_send with "[Hm HA1] H'") as "#H''".
      { by iApply stenning_A_foo. }
      iIntros "!>". iMod "H''". iModUnIntro. iFrame. done. }
  Qed.

  (* TODO: Initial value of B should be -1 *)
  (* TODO: Safety invariant? (at-most-one-off) *)
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

  (* TODO: Need to thread non-succees *)
  (* TODO: Need to consider restricting behaviour of other participant. *)

End stenning_ex.
