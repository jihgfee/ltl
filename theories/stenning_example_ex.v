From ltl Require Import ltl.

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
    omsg ≠ Some $ mAB n →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BReceiving, n))
  | B_RecvSucc stA n omsg :
    omsg = Some $ mAB n →
    stenning_trans (stA, (BReceiving, n))
      (Brole, Recv saB omsg)
      (stA, (BSending, (1+n)))
  .

  Notation tProp := (tProp stenning_state stenning_label stenning_trans).

  Axiom fair_sched :
    ∀ (b:actor), ⊢ (◊ ∃ (a:stenning_action), ↓l (b,a)):tProp.

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

  (* Lemma ltl_eventually_until {S L Rel} (P : tProp S L Rel) : *)
  (*   ◊P ⊢ (¬ P) ∪ P. *)
  (* Proof. rewrite ltl_until_foo. rewrite left_id. done. Qed. *)

  Lemma stenning_1 i stB :
    ↓s ((ASending, i), stB)
    ⊢ ◊ ↓s ((AReceiving, i), stB)
    : tProp.
  Proof. Admitted.

  (* Needs that state is correct one *)
  Lemma stenning_2 i :
    ↓l (saA, Recv saA (Some $ mBA i))
    ⊢ ○ ↓sA (ASending, S i)
    : tProp.
  Proof. Admitted.

  Lemma stenning_foo i :
    ↓sA (ASending,i) ⊢
    (↓l (A,Send (mAB i)) ∧ ○ ↓sA (AReceiving,i)) ∨
    (↓ll B ∧ ○ ↓sA (ASending,i)) : tProp.
  Proof. Admitted.

  Lemma stenning_foo' i :
    ↓sA (AReceiving,i) ⊢
    ∃ om, (↓l (A,Recv saA om) ∧ ○ ↓sA (ASending, i)) ∨ (* OBS: Discrepancy, should incr *)
    (↓ll B ∧ ○ ↓sA (AReceiving,i)) : tProp.
  Proof. Admitted.

  Lemma stenning_bar :
    ⊢ ↓ll A → ↓ll B → False.
  Proof. Admitted.

  Lemma stenning_baz a b :
    ↓l (a,b) ⊢ ↓ll a.
  Proof. Admitted.

  Lemma ltl_dup (P : tProp) : P ⊢ P ∧ P.
  Proof. iIntros "H". iFrame. Qed.

  Lemma stenning_split stA stB :
    ↓s (stA, stB) ⊢ ↓sA stA ∧ ↓sB stB.
  Proof. Admitted.

  Lemma stenning_A_send i :
    ↓sA ((ASending, i)) ⊢ ◊ (↓sA ((ASending, i)) ∧ ↓l (saA, Send (mAB i))) : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (fair_sched A) as "H".
    iRevert "Hs".
    iApply (ltl_eventually_ind with "[] H").
    iIntros "!> [H1|H2]".
    { iIntros "H'". iDestruct "H1" as (a) "HA".
      iDestruct (ltl_dup with "H'") as "[H' H'']".
      iDestruct (stenning_foo with "H'") as "[[Hl Hs]|[Hl Hs]]".
      - iModUnIntro. iFrame.
      - iDestruct (stenning_baz with "HA") as "HA".
        iDestruct (stenning_bar with "HA Hl") as "[]".
    }
    iDestruct "H2" as "[H1 H2]".
    iIntros "H'".
    iDestruct (ltl_dup with "H'") as "[H' H'']".
    iDestruct (stenning_foo with "H'") as "[[Hl Hs]|[Hl Hs]]".
    { iModUnIntro. iFrame. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    by iApply "H2".
  Qed.

  Lemma stenning_A_recv i :
    ↓sA ((AReceiving, i)) ⊢ ∃ om, ◊ (↓sA ((AReceiving, i)) ∧ ↓l (saA, Recv saA om)) : tProp.
  Proof. Admitted.

  Lemma stenning_A_always_send i :
    ↓sA (ASending, i) ⊢ □ ◊ (↓sA (ASending, i) ∧ ↓l (saA, Send (mAB i))) : tProp.
  Proof.
    iIntros "Hs".
    iMod (stenning_A_send with "Hs") as "[Hs Hl]".
    iApply (ltl_always_intro with "[] [Hs Hl]"); last first.
    { iModUnIntro. iFrame. }
    iIntros "!> >[Hs Hl]".
    iDestruct (stenning_foo with "Hs") as "[[Hl' Hs]|[Hl' Hs]]"; last first.
    { iDestruct (stenning_baz with "Hl") as "Hl".
      iDestruct (stenning_bar with "Hl Hl'") as "[]". }
    iModIntro.
    iDestruct (stenning_A_recv with "Hs") as (m) ">[Hs Hl]".
    iDestruct (stenning_foo' with "Hs") as (m') "[[Hl' Hs]|[Hl' Hs]]"; last first.
    { iDestruct (stenning_baz with "Hl") as "Hl".
      iDestruct (stenning_bar with "Hl Hl'") as "[]". }
    rewrite -ltl_next_eventually. iModIntro.
    by iApply stenning_A_send.
  Qed.

  Lemma stenning_A_always_try_recv i :
    ↓sA (ASending, i)
    ⊢ □ ◊ ∃ om : option Message, ↓l (saA, Recv saA om)
    : tProp.
  Proof. Admitted.

  (* (* OBS: Lacking B always trying to receive *) *)
  Lemma stenning_B_recv i :
    □ ◊ ↓l (saA, Send (mAB i)) ⊢
    ◊ ↓l (saB, Recv saB $ Some (mAB i)) : tProp.
  Proof. Admitted.

  (* (* Needs state correspondence *) *)
  Lemma stenning_B_send i :
    □ ◊ ↓l (saB, Recv saB $ Some (mAB i)) ⊢
    ◊ ↓l (saB, Send (mBA i))
    : tProp.
  Proof. Admitted.

  Lemma stenning_A_advances i :
    ↓sA ((ASending, i)) ⊢ ◊ ↓sA ((ASending, S i)) : tProp.
  Proof.
    iIntros "HA".
    iApply ltl_eventually_next.
    iApply stenning_2.
    iDestruct (ltl_dup with "HA") as "[HA1 HA2]".
    iDestruct (fair_net _ (λ m, m = i) with "[HA1] [HA2]") as "Hfair"; last first.
    { iMod "Hfair" as (m ->) "Hfair". by iModUnIntro. }
    { iDestruct (stenning_A_always_try_recv with "HA2") as "HA2". done. }
    { iDestruct (stenning_A_always_send with "HA1") as "#H".
      iDestruct (stenning_B_recv with "[H]") as "H'".
      { iModIntro. iMod "H". iModUnIntro. iDestruct "H" as "[_ $]". }
      iDestruct (stenning_B_send with "H'") as "H''".
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
