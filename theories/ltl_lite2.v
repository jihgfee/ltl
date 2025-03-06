From Paco Require Import paconotation.
From fairneris Require Export inftraces.

Declare Scope trace_scope.
Delimit Scope trace_scope with trace.
Bind Scope trace_scope with trace.

Definition ltl_pred S L := trace S L → Prop.

Section ltl_constructors.
  Context {S L : Type}.

  Notation ltl_pred := (ltl_pred S L).

  Definition trace_entails (P Q : ltl_pred) := ∀ tr, P tr → Q tr. 

  (* Primitive operators *)
  Definition trace_now P : ltl_pred := λ tr, pred_at tr 0 P.
  Definition trace_not P : ltl_pred := λ tr, ¬ P tr.
  Definition trace_or P Q : ltl_pred := λ tr, P tr ∨ Q tr.
  Definition trace_next P : ltl_pred :=
    λ tr, ∃ tr', after 1 tr = Some tr' ∧ P tr'.
  Inductive trace_until P Q : ltl_pred :=
  | trace_until_here tr : Q tr -> trace_until P Q tr
  | trace_until_next s l tr : P (s -[l]-> tr) → trace_until P Q tr → trace_until P Q (s -[l]-> tr).

  (* Derived operators *)
  Definition trace_and P Q := (trace_not (trace_or (trace_not P) (trace_not Q))).
  Definition trace_implies P Q := (trace_or (trace_not P) Q).
  Definition trace_biimplies P Q :=
    (trace_and (trace_implies P Q) (trace_implies Q P)).
  Definition trace_true := (trace_now (λ _ _, True)).
  Definition trace_false := (trace_now (λ _ _,False)).
  Definition trace_eventually P := (trace_until trace_true P).
  Definition trace_always P := (trace_not $ trace_eventually (trace_not P)).
  Definition trace_weak_until (P Q : trace S L → Prop) : ltl_pred :=
    trace_or (trace_until P Q) (trace_always P).

  Definition trace_forall {A} (P : A → ltl_pred) : ltl_pred :=
    λ tr, ∀ (x:A), P x tr.
  Definition trace_exists {A} (P : A → ltl_pred) : ltl_pred :=
    λ tr, ∃ (x:A), P x tr.

  (* OBS: Might be better to use entailment *)
  Definition trace_bientails (P Q : ltl_pred) :=
    trace_entails P Q ∧ trace_entails Q P.

  (* Custom constructors *)
  Definition trace_always_eventually_implies
             (P Q : trace S L → Prop) : ltl_pred :=
    trace_always (trace_implies P (trace_eventually Q)).

  Definition trace_always_eventually_implies_now
             (P Q : S → option L → Prop) : ltl_pred :=
    trace_always_eventually_implies (trace_now P) (trace_now Q).

  Lemma trace_eventually_ind (P P0 : trace S L → Prop) :
    (∀ tr : trace S L, P tr → P0 tr) →
    (∀ (s : S) (l : L) (tr : trace S L),
         trace_eventually P tr → P0 tr → P0 (s -[ l ]-> tr)) →
    ∀ t : trace S L, trace_eventually P t → P0 t.
  Proof.
    intros ? IH ??.
    eapply (trace_until_ind trace_true); [done|by intros; apply IH|done].
  Qed.

  Definition trace_suffix_of (tr1 tr2 : trace S L) : Prop :=
    ∃ n, after n tr2 = Some tr1.

End ltl_constructors.

(* Logic *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P%type) ..)
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P%type) ..)
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "x ∨ y" := (x%type \/ y%type) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x%type /\ y%type) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x%type -> y%type)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x%type <-> y%type) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x%type) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x%type <> y%type) (at level 70) : type_scope.

(* Abstraction *)
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t%type) ..)
  (at level 10, x binder, y binder, t at level 200,
  format "'[  ' '[  ' 'λ'  x  ..  y ']' ,  '/' t ']'").

Arguments trace_eventually_ind : clear implicits.

Notation "'True'" := (trace_true) : trace_scope.
Notation "'False'" := (trace_false) : trace_scope.
Notation "○ P" := (trace_next P%trace) (at level 20, right associativity) : trace_scope.
Notation "□ P" := (trace_always P%trace) (at level 20, right associativity) : trace_scope.
Notation "◊ P" := (trace_eventually P%trace) (at level 20, right associativity) : trace_scope.
Notation "↓ P" := (trace_now P) (at level 20, right associativity) : trace_scope.
Notation "P → Q" := (trace_implies P%trace Q%trace) : trace_scope.
Notation "P ⊢ Q" := (trace_entails P%trace Q%trace) : trace_scope.
Notation "⊢ Q" := (trace_entails trace_true Q%trace) : trace_scope.
Notation "¬ P" := (trace_not P%trace) : trace_scope.
Infix "⊣⊢" := trace_bientails : trace_scope.
Infix "∧" := trace_and : trace_scope.
Infix "∨" := trace_or : trace_scope.

(* TODO: Replace existing library lemma with this *)
Lemma not_exists_forall_not_alt {A} (P : A → Prop) x : ¬ (∃ x, P x) → ¬ P x.
Proof. intros Hnex HP; apply Hnex; eauto. Qed.

Section ltl_lemmas.
  Context {S L : Type}.

  Notation ltl_pred := (ltl_pred S L).
    
  (* TODO: Move this *)
  Lemma after_is_Some_le (tr : trace S L) n m :
    m ≤ n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  Lemma after_is_Some_lt (tr : trace S L) n m :
    m < n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  Lemma after_levis n m (tr1 tr2 tr3: trace S L):
    n ≤ m →
    after n tr1 = Some tr2 →
    after m tr1 = Some tr3 →
    after (m - n) tr2 = Some tr3.
  Proof.
    intros Hle Haftern Hafterm.
    pose proof (Nat.le_exists_sub n m Hle) as [p [-> Hle']].
    rewrite Nat.add_comm Nat.add_sub'.
    by rewrite after_sum Haftern in Hafterm.
  Qed.

  (** trace_suffix_of lemmas  *)

  Lemma trace_suffix_of_refl (tr : trace S L) :
    trace_suffix_of tr tr.
  Proof. by exists 0. Qed.

  Lemma trace_suffix_of_cons_l s l (tr tr' : trace S L) :
    trace_suffix_of (s -[l]-> tr) tr' → trace_suffix_of tr tr'.
  Proof.
    intros [n Hafter]. exists (Datatypes.S n).
    replace (Datatypes.S n) with (n + 1) by lia.
    rewrite after_sum'. rewrite Hafter. done.
  Qed.

  Lemma trace_suffix_of_cons_r s l (tr tr' : trace S L) :
    trace_suffix_of tr tr' → trace_suffix_of tr (s -[l]-> tr').
  Proof. intros [n Hafter]. by exists (Datatypes.S n). Qed.

  Lemma trace_suffix_of_trans (tr tr' tr'' : trace S L) :
    trace_suffix_of tr'' tr' → trace_suffix_of tr' tr → trace_suffix_of tr'' tr.
  Proof.
    intros [n Hsuffix1] [m Hsuffix2].
    exists (n+m). rewrite after_sum. rewrite Hsuffix2.
    rewrite Hsuffix1. done.
  Qed.

  (** trace_true lemmas *)
  
  Lemma trace_trueI : (⊢ (True : ltl_pred))%trace.
  Proof. intros tr. destruct tr; done. Qed.

  (** trace_implies lemmas *)

  Lemma trace_impliesI (P Q : ltl_pred) tr :
    trace_implies P Q tr ↔ (P tr → Q tr).
  Proof.
    split; [by intros [|]|].
    intros HPQ.
    assert (P tr ∨ ¬ P tr) as [HP|HP] by apply ExcludedMiddle.
    + by right; apply HPQ.
    + by left.
  Qed.

  Lemma trace_implies_refl (P : ltl_pred) tr :
    trace_implies P P tr.
  Proof. by apply trace_impliesI. Qed.

  Lemma trace_entails_implies (P Q : ltl_pred) :
    (P ⊢ Q)%trace → (⊢ P → Q)%trace.
  Proof.
    rewrite /trace_entails.
    intros HPQ tr _. rewrite trace_impliesI. apply HPQ.
  Qed.

  Lemma trace_implies_entails (P Q : ltl_pred) :
    (⊢ P → Q)%trace → (P ⊢ Q)%trace.
  Proof.
    rewrite /trace_entails.
    intros HPQ tr HP.
    specialize (HPQ tr). rewrite trace_impliesI in HPQ.
    apply HPQ.
    - by destruct tr. (* OBS: Hacky *)
    - done.
  Qed.

  (** trace_not lemmas *)

 (* Lemma trace_notI (P : trace S L → Prop) tr : *)
 (*    trace_not P tr ↔ ¬ P tr. *)
 (*  Proof. done. Qed. *)
  Lemma trace_notI (P : ltl_pred) :
    trace_not P ⊣⊢ ¬ P.
  Proof. split; intros tr; done. Qed.

  Lemma trace_not_idemp (P : ltl_pred) :
    ¬ (¬ P) ⊣⊢ P.
  Proof. split; intros tr; [apply NNP_P|apply P_NNP]. Qed.

  Lemma trace_not_mono (P Q : ltl_pred) :
    (Q ⊢ P) → (¬ P ⊢ ¬ Q)%trace.
  Proof. intros HQP tr HP HQ. apply HP. by apply HQP. Qed.

  (* Lemma trace_not_mono (P Q : ltl_pred) : *)
  (*   (Q → P) ⊢ ¬ P → ¬ Q. *)
  (* Proof. *)
  (*   intros tr. rewrite !trace_impliesI. *)
  (*   intros HQP HP HQ. apply HP. by apply HQP. *)
  (* Qed. *)
  
  (** trace_next lemmas *)

  (* Lemma trace_next_intro (P : trace S L → Prop) : *)
  (*   (⊢ P)%trace → (⊢ ○ P)%trace. *)
  (* Proof. intros ?. intros tr. destruct tr; [|simpl]. exists tr. simpl in *. by simplify_eq. Qed. *)

  Lemma trace_next_intro (P : ltl_pred) s l (tr : trace S L) :
    P tr → (○ P) (s -[l]-> tr).
  Proof. intros ?. exists tr. simpl in *. by simplify_eq. Qed.

  Lemma trace_next_elim (P : ltl_pred) s l tr :
    (○ P) (s -[l]-> tr) → P tr.
  Proof. inversion 1. naive_solver. Qed.

  Lemma trace_next_elim_inv (P : ltl_pred) tr :
    (○ P) tr → ∃ s l tr', tr = s -[l]-> tr' ∧ P tr'.
  Proof. inversion 1. destruct tr; naive_solver. Qed.

  Lemma trace_next_mono (P Q : ltl_pred) :
    (P ⊢ Q) → (○ P ⊢ ○ Q).
  Proof.
    intros HPQ tr HP. simpl in *.
    destruct HP as [tr' [Htr' HP]].
    destruct tr; [done|]. simpl in *.
    simplify_eq.
    exists tr'. split; [done|].
    by apply HPQ.
  Qed.

  (** trace_or lemmas *)

  Lemma trace_orI (P Q : ltl_pred) (tr : trace S L) :
    (P ∨ Q)%trace tr ↔ P tr ∨ Q tr.
  Proof. done. Qed.

  Lemma trace_or_l (P Q : ltl_pred) :
    P ⊢ P ∨ Q.
  Proof.
    apply trace_implies_entails.
    intros tr _. rewrite trace_impliesI. intros HP.
    by left.
  Qed.

  Lemma trace_or_r (P Q : ltl_pred) :
    Q ⊢ P ∨ Q.
  Proof.
    apply trace_implies_entails.
    intros tr _. rewrite trace_impliesI. intros HP.
    by right.
  Qed.

  (** trace_and lemmas *)

  Lemma trace_andI (P Q : ltl_pred) (tr : trace S L) :
    (P ∧ Q)%trace tr ↔ P tr ∧ Q tr.
  Proof.
    split.
    - intros HPQ.
      assert (P tr ∨ ¬ P tr) as [HP|HP] by apply ExcludedMiddle; last first.
      { eapply trace_not_mono in HPQ; [|by apply trace_or_l]. done. }
      assert (Q tr ∨ ¬ Q tr) as [HQ|HQ] by apply ExcludedMiddle; last first.
      { eapply trace_not_mono in HPQ; [|by apply trace_or_r]. done. }
      done.
    - intros [HP HQ] [HP'|HQ']; done.
  Qed.

  (** trace_now lemmas *)

  Definition trfirst_label (tr: trace S L) : option L :=
    match tr with
    | ⟨_⟩ => None
    | _ -[ℓ]-> _ => Some ℓ
    end.

  Lemma trace_now_mono_strong (P Q : S → option L → Prop) tr :
    (∀ s l, trfirst tr = s → trfirst_label tr = l → P s l → Q s l) →
    (↓P) tr → (↓Q) tr.
  Proof.
    destruct tr as [s|s l tr].
    - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
    - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
  Qed.

  Lemma trace_now_mono (P Q : S → option L → Prop) tr :
    (∀ s l, P s l → Q s l) → (↓P) tr → (↓Q) tr.
  Proof. intros. eapply trace_now_mono_strong; [|done]. by eauto. Qed.

  Lemma trace_now_not (P : S → option L → Prop) (tr : trace S L) :
    (↓ (λ s l, ¬ P s l)) tr ↔ trace_not (↓ P) tr.
  Proof. by destruct tr. Qed.

  Lemma trace_now_exists {A} (P : A → S → option L → Prop) (tr : trace S L) :
    (↓ (λ s l, ∃ (x:A), P x s l)) tr → ∃ (x:A), (↓ P x) tr.
  Proof. rewrite /trace_now /pred_at. intros H. by destruct tr. Qed.

  Lemma trace_now_or (P Q : S → option L → Prop) tr :
    (↓ (P \2/ Q)) tr → (↓ P) tr ∨ (↓ Q) tr.
  Proof. rewrite /trace_now /pred_at. by destruct tr=>/=. Qed.

  Lemma trace_now_and P Q (tr : trace S L) :
    (↓ (P /2\ Q)) tr ↔ trace_and (↓P) (↓Q) tr .
  Proof. rewrite trace_andI. destruct tr; done. Qed.

  (* TODO: Maybe remove *)
  Lemma trace_now_split P Q (tr : trace S L) :
    (↓ P) tr → (↓ Q) tr → (↓ (P /2\ Q)) tr.
  Proof. intros. apply trace_now_and. rewrite trace_andI. done. Qed.

  (** trace_eventually lemmas *)

  Lemma trace_eventually_intro (P : ltl_pred) :
    P ⊢ ◊ P.
  Proof. by constructor 1. Qed.

  Lemma trace_eventually_cons (P : ltl_pred) s l (tr : trace S L) :
    (◊ P) tr → (◊ P) (s -[l]-> tr).
  Proof. intros. by constructor 2. Qed.

  Lemma trace_eventually_idemp (P : ltl_pred) (tr : trace S L) :
    (◊◊P) tr → (◊P) tr.
  Proof.
    intros Htr. induction Htr using trace_eventually_ind; [done|].
    apply trace_eventually_cons. done.
  Qed.
  
  Lemma trace_eventuallyI_alt (P : ltl_pred) tr :
    (◊ P) tr ↔ (∃ tr', trace_suffix_of tr' tr ∧ (◊ P) tr').
  Proof.
    split.
    - intros Heventually.
      induction Heventually using trace_eventually_ind.
      { exists tr. split; [apply trace_suffix_of_refl|].
        by apply trace_eventually_intro. }
      destruct IHHeventually as [tr' [Hsuffix HP]].
      exists tr'.
      split; [|done].
      by apply trace_suffix_of_cons_r.
    - intros [tr' [Hsuffix Htr']].
      induction Htr' using trace_eventually_ind.
      { destruct Hsuffix as [n Hafter].
        revert tr tr0 Hafter H.
        induction n; intros tr tr0 Hafter HP.
        { simpl in *. simplify_eq. by apply trace_eventually_intro. }
        destruct tr; [done|].
        constructor 2; [done|].
        by eapply IHn. }
      apply IHHtr'.
      by eapply trace_suffix_of_cons_l.
  Qed.

  Lemma trace_eventuallyI (P : ltl_pred) tr :
    (◊ P) tr ↔ (∃ tr', trace_suffix_of tr' tr ∧ P tr').
  Proof.
    split.
    - intros Heventually.
      induction Heventually using trace_eventually_ind.
      { exists tr. split; [apply trace_suffix_of_refl|]. done. }
      destruct IHHeventually as [tr' [Hsuffix HP]].
      exists tr'.
      split; [|done].
      by apply trace_suffix_of_cons_r.
    - intros [tr' [Hsuffix Htr']].
      apply trace_eventuallyI_alt. exists tr'. split=>//.
      by apply trace_eventually_intro.
  Qed.

  Lemma trace_eventually_until (P : ltl_pred) (tr : trace S L) :
    (◊P) tr → trace_until (trace_not P) (P) tr.
  Proof.
    assert (∀ tr, P tr ∨ ¬ P tr) as Hdec by by intros; apply ExcludedMiddle.
    induction 1 using trace_eventually_ind; [by constructor|].
    specialize (Hdec (s -[l]-> tr)) as [H1|H2].
    - by apply trace_until_here.
    - by apply trace_until_next.
  Qed.

  Lemma trace_eventually_mono_strong (P Q : ltl_pred) tr :
    (∀ tr', trace_suffix_of tr' tr → P tr' → Q tr') → (◊P) tr → (◊Q) tr.
  Proof.
    intros HPQ.
    induction 1 using trace_eventually_ind.
    { apply HPQ, trace_eventually_intro in H. done. apply trace_suffix_of_refl. }
    constructor 2; [done|].
    apply IHtrace_eventually.
    intros tr' Hsuffix HP.
    apply HPQ; [|done].
    destruct Hsuffix as [n Heq].
    exists (Datatypes.S n). done.
  Qed.

  Lemma trace_eventually_mono (P Q : ltl_pred) tr :
    (∀ tr, P tr → Q tr) → (◊P) tr → (◊Q) tr.
  Proof.
    intros. eapply trace_eventually_mono_strong; [|done]. intros. by apply H.
  Qed.

  Lemma trace_eventually_elim_l (P Q : ltl_pred) :
    (∀ tr, P tr → (◊ Q) tr) → (∀ tr, (◊P) tr → (◊ Q) tr).
  Proof.
    intros HPQ tr HP.
    apply trace_eventually_idemp.
    revert HP.
    apply trace_eventually_mono.
    apply HPQ.
  Qed.

  Lemma trace_eventually_next (P : ltl_pred) (tr : trace S L) :
    (◊ ○ P) tr → (◊ P) tr.
  Proof.
    intros Hnext.
    induction Hnext using trace_eventually_ind.
    { destruct tr; [inversion H; naive_solver|].
      constructor 2; [done|]. constructor. by eapply trace_next_elim. }
    constructor 2; [done|]. apply IHHnext.
  Qed.

  Lemma trace_eventually_next' (P : ltl_pred) :
    (◊ ○ P) ⊢ (◊ P).
  Proof.
    intros tr Hnext.
    induction Hnext using trace_eventually_ind.
    { destruct tr; [inversion H; naive_solver|].
      constructor 2; [done|]. constructor. by eapply trace_next_elim. }
    constructor 2; [done|]. apply IHHnext.
  Qed.

  (* TODO: This is a bit of a weird statement *)
  (* Lemma trace_eventually_implies (P Q : ltl_pred) (tr : trace S L) : *)
  (*   (P tr → Q tr) → (◊P) tr → (◊ Q) tr. *)
  (* Proof. Admitted. *)
  (*   intros HPQ HP. *)
  (*   eapply trace_always_mono_strong; [|done]. *)
  (*   intros tr' Hsuffix. *)
  (*   apply trace_always_elim. *)
  (*   by eapply trace_always_suffix_of. *)
  (* Qed. *)

  (* Lemma trace_eventually_next_comm (P : ltl_pred) (tr : trace S L) : *)
  (*   (◊ ○ P) tr → (○ ◊ P) tr. *)
  (* Proof. *)
  (*   intros Hnext. *)
  (*   induction Hnext using trace_eventually_ind. *)
  (*   { destruct tr; [inversion H; naive_solver|]. *)
  (*     revert H. apply trace_next_mono. apply trace_eventually_intro. } *)
  (*   apply trace_next_intro. apply trace_eventually_next. done. *)
  (* Qed. *)

  Lemma trace_suffix_of_cons_l_inv s l (tr tr' : trace S L) :
    trace_suffix_of tr' tr →
    trace_suffix_of tr (s -[ l ]-> tr) →
    ∃ s' l' (tr'' : trace S L), tr'' = s' -[l']-> tr' ∧
      trace_suffix_of tr'' (s -[ l ]-> tr).
  Proof.
    intros [n Hsuff] Hsuff'.
    destruct n.
    { simpl in *. simplify_eq. exists s, l, (s -[ l ]-> tr').
      split; [done|]. apply trace_suffix_of_refl. }
    replace (Datatypes.S n) with (n + 1) in Hsuff by lia.
    destruct (after n tr) eqn:Heqn; last first.
    { by rewrite after_sum' Heqn in Hsuff. }
    rewrite after_sum' Heqn in Hsuff.
    destruct t; [done|]. simpl in *. simplify_eq.
    exists s0, ℓ, (s0 -[ ℓ ]-> tr').
    split; [done|]. by exists (Datatypes.S n).
  Qed.
      
  Lemma trace_eventually_next_comm (P : ltl_pred) (tr : trace S L) :
    (◊ ○ P) tr ↔ (○ ◊ P) tr.
  Proof.
    split.
    - intros Hnext.
      induction Hnext using trace_eventually_ind.
      { destruct tr; [inversion H; naive_solver|].
        revert H. apply trace_next_mono. apply trace_eventually_intro. }
      apply trace_next_intro. apply trace_eventually_next. done.
    - intros Hnext.
      apply trace_eventuallyI.
      destruct tr; [inversion Hnext; naive_solver|].
      destruct Hnext as [tr' [Htr' Hnext]].
      subst.
      assert (trace_suffix_of tr' (s -[ ℓ ]-> tr)).
      { exists 1. done. }
      simpl in *. simplify_eq.
      apply trace_eventuallyI in Hnext as [tr'' [Hsuff Htr']].
      assert (∃ s'' l'' tr''', tr''' = s'' -[ l'' ]-> tr'' ∧
                               trace_suffix_of tr''' ((s -[ ℓ ]-> tr')))
        as (?&?&tr'''&Heq&Hsuff').
      { by apply trace_suffix_of_cons_l_inv. }
      exists tr'''.
      subst.
      split; [|by apply trace_next_intro]. done.
  Qed.

  Lemma trace_eventually_next_comm' (P : ltl_pred) :
    (◊ ○ P) ⊣⊢ (○ ◊ P).
  Proof.
    split.
    - intros tr Hnext.
      induction Hnext using trace_eventually_ind.
      { destruct tr; [inversion H; naive_solver|].
        revert H. apply trace_next_mono. apply trace_eventually_intro. }
      apply trace_next_intro. apply trace_eventually_next. done.
    - intros tr Hnext.
      apply trace_eventuallyI.
      destruct tr; [inversion Hnext; naive_solver|].
      destruct Hnext as [tr' [Htr' Hnext]].
      subst.
      assert (trace_suffix_of tr' (s -[ ℓ ]-> tr)).
      { exists 1. done. }
      simpl in *. simplify_eq.
      apply trace_eventuallyI in Hnext as [tr'' [Hsuff Htr']].
      assert (∃ s'' l'' tr''', tr''' = s'' -[ l'' ]-> tr'' ∧
                               trace_suffix_of tr''' ((s -[ ℓ ]-> tr')))
        as (?&?&tr'''&Heq&Hsuff').
      { by apply trace_suffix_of_cons_l_inv. }
      exists tr'''.
      subst.
      split; [|by apply trace_next_intro]. done.
  Qed.

  Lemma trace_eventually_suffix_of (P : ltl_pred) tr1 tr2 :
    trace_suffix_of tr1 tr2 → (◊P) tr1 → (◊P) tr2.
  Proof. intros Hsuffix HP. apply trace_eventuallyI_alt. by exists tr1. Qed.

  Lemma trace_eventually_or (P Q : ltl_pred) tr :
    (◊ (P \1/ Q)) tr → (◊ P) tr ∨ (◊ Q) tr.
  Proof.
    intros Hdisj.
    induction Hdisj using trace_eventually_ind.
    { inversion H; [left; by constructor|right; by constructor]. }
    inversion IHHdisj.
    - left. by constructor 2.
    - right. by constructor 2.
  Qed.

  (** trace_always lemmas *)

  Lemma trace_always_cons (P : ltl_pred) s l (tr : trace S L) :
    (□ P) (s -[l]-> tr) → (□ P) tr.
  Proof.
    intros Htr Htr'. apply Htr. clear Htr. by apply trace_eventually_cons.
  Qed.

  Lemma trace_always_idemp P (tr : trace S L) :
    (□ P) tr → (□ □ P) tr.
  Proof.
    intros Htr Htr'. induction Htr'; [by apply H|].
    apply IHHtr'. by apply trace_always_cons in Htr.
  Qed.

  Lemma trace_always_elim (P : ltl_pred) (tr : trace S L) :
    (□P) tr → P tr.
  Proof.
    intros Htr.
    assert (P tr ∨ ¬ P tr) as [|HP] by apply ExcludedMiddle; [done|].
    rewrite /trace_always in Htr.
    assert (trace_not (trace_not P) tr).
    { intros Htr'. apply Htr. apply trace_eventually_intro. done. }
    done.
  Qed.

  Lemma trace_always_mono (P Q : ltl_pred) tr :
    (∀ tr, trace_implies P Q tr) → (□P) tr → (□Q) tr.
  Proof.
    intros HPQ HP HQ. apply HP. eapply trace_eventually_mono; [|done].
    clear HP HQ. intros tr' HP HQ. apply HP.
    specialize (HPQ tr'). rewrite trace_impliesI in HPQ. by apply HPQ.
  Qed.

  Lemma trace_always_mono_strong (P Q : ltl_pred) tr :
    (∀ tr', trace_suffix_of tr' tr → trace_implies P Q tr') → (□P) tr → (□Q) tr.
  Proof.
    intros HPQ HP HQ. apply HP. eapply trace_eventually_mono_strong; [|done].
    clear HP HQ. intros tr' Htr' HP HQ. apply HP.
    specialize (HPQ tr'). rewrite trace_impliesI in HPQ. by apply HPQ.
  Qed.

  Lemma trace_alwaysI_alt (P : ltl_pred) tr :
    (□P) tr ↔ (∀ tr', trace_suffix_of tr' tr → (□ P) tr').
  Proof.
    split.
    - intros Htr tr' Hsuffix Htr'.
      apply Htr.
      induction Htr' using trace_eventually_ind.
      { eapply trace_eventuallyI_alt. exists tr0. split; [done|].
        by apply trace_eventually_intro. }
      apply IHHtr'. by eapply trace_suffix_of_cons_l.
    - intros Htr' Htr.
      induction Htr using trace_eventually_ind.
      { specialize (Htr' tr). apply Htr'.
        { apply trace_suffix_of_refl. }
        by apply trace_eventually_intro. }
      apply IHHtr. intros tr' Htsuffix. apply Htr'.
      by eapply trace_suffix_of_cons_r.
  Qed.

  Lemma trace_always_suffix_of (P : ltl_pred) tr1 tr2 :
    trace_suffix_of tr2 tr1 → (□P) tr1 → (□P) tr2.
  Proof. rewrite (trace_alwaysI_alt _ tr1). intros Hsuffix HP. by eapply HP. Qed.

  Lemma trace_alwaysI (P : ltl_pred) tr :
    (□P) tr ↔ (∀ tr', trace_suffix_of tr' tr → P tr').
  Proof.
    split.
    - intros HP tr' Hsuff. rewrite trace_alwaysI_alt in HP.
      apply trace_always_elim. eauto.
    - intros H Habs. apply trace_eventuallyI in Habs as (tr'&Hsuff&?).
      by specialize (H _ Hsuff).
  Qed.

  Lemma trace_always_forall {A} (P : A → ltl_pred) tr :
    (∀ (x:A), (□ (P x)) tr) ↔ (□ (λ tr', ∀ x, P x tr')) tr.
  Proof.
    split.
    - intros Htr Htr'.
      induction Htr' using trace_eventually_ind.
      { apply H. intros x. specialize (Htr x).
        apply trace_always_elim in Htr. apply Htr. }
      apply IHHtr'.
      intros x. specialize (Htr x).
      by apply trace_always_cons in Htr.
    - intros Htr x Htr'.
      induction Htr' using trace_eventually_ind.
      { apply H. apply trace_always_elim in Htr. apply Htr. }
      apply IHHtr'. by apply trace_always_cons in Htr.
  Qed.

  (* TODO: This breaks naming convention *)
  Lemma trace_always_universal (P : ltl_pred) (tr : trace S L) :
    (∀ tr, P tr) → (□P) tr.
  Proof.
    intros ? H. induction H using trace_eventually_ind; [|done].
    simplify_eq. specialize (H0 tr). done.
  Qed.

  (* TODO: This is a bit of a weird statement *)
  Lemma trace_always_implies' (P Q : ltl_pred) :
    ⊢ ((□(P → Q))) → (□P) → (□ Q).
  Proof.
    intros tr. rewrite !trace_impliesI.
    intros HPQ HP.
    eapply trace_always_mono_strong.
    intros tr' Hsuffix.
    apply trace_always_elim.
    by eapply trace_always_suffix_of.
  Qed.

  (* TODO: This is a bit of a weird statement *)
  Lemma trace_always_implies (P Q : ltl_pred) tr :
    (□(P → Q))%trace tr → (□P) tr → (□ Q) tr.
  Proof.
    intros HPQ HP.
    eapply trace_always_mono_strong; [|done].
    intros tr' Hsuffix.
    apply trace_always_elim.
    by eapply trace_always_suffix_of.
  Qed.

  Lemma trace_always_eventually P (tr : trace S L) :
    (□ P) tr → (◊ P) tr.
  Proof.
    intros Halways. eapply trace_eventuallyI_alt. exists tr.
    split; [apply trace_suffix_of_refl|]. apply trace_eventually_intro.
    by apply trace_always_elim in Halways.
  Qed.

  Lemma trace_always_intro (P Q : ltl_pred) :
    (P ⊢ Q)%trace → ((Q ⊢ (○ Q))%trace) → (P ⊢ (□ Q))%trace.
  Proof.
    intros HPQ IHQ tr HP.
    apply trace_alwaysI.
    intros tr' [n Hsuff].
    revert tr tr' Hsuff HP.
    induction n; intros tr tr' Hsuff HP.
    { simpl in *. simplify_eq. by apply HPQ. }
    destruct tr; [done|].
    replace (Datatypes.S n) with (n + 1) in Hsuff by lia.
    rewrite after_sum' in Hsuff.
    destruct (after n (s -[ ℓ ]-> tr)) eqn:Heqn; [|done].
    eapply IHn in HP; [|done].
    assert ((○ Q) t).
    { by apply IHQ. }
    destruct H as [? [H' H'']].
    simplify_eq. done.
  Qed.

  (* Lemma trace_always_intro (P Q : ltl_pred) : *)
  (*   (□ P ⊢ Q)%trace → (((□ P ∧ Q) ⊢ (○ Q))%trace) → (□ P ⊢ (□ Q))%trace. *)
  (* Proof. *)
  (*   intros HPQ IHQ tr HP. *)
  (*   apply trace_alwaysI. *)
  (*   intros tr' [n Hsuff]. *)
  (*   revert tr tr' Hsuff HP. *)
  (*   induction n; intros tr tr' Hsuff HP. *)
  (*   { simpl in *. simplify_eq. by apply HPQ. } *)
  (*   destruct tr; [done|]. *)
  (*   replace (Datatypes.S n) with (n + 1) in Hsuff by lia. *)
  (*   rewrite after_sum' in Hsuff. *)
  (*   destruct (after n (s -[ ℓ ]-> tr)) eqn:Heqn; [|done]. *)
  (*   assert ((□ P) t). *)
  (*   { eapply trace_always_suffix_of. *)
  (*     { eexists _.  done. } *)
  (*     done. } *)
  (*   assert (Q t). *)
  (*   { by apply HPQ. } *)
  (*   assert ((○ Q) t). *)
  (*   { apply IHQ. apply trace_andI. done. } *)
  (*   destruct H1 as [? [H' H'']]. *)
  (*   simplify_eq. done. *)
  (* Qed. *)

  (* Lemma trace_always_intro (P : ltl_pred) tr : *)
  (*   (P tr)%trace → (∀ tr, (P → (○ P))%trace tr) → ((□ P) tr)%trace. *)
  (* Proof. *)
  (*   intros HP IHP. *)
  (*   apply trace_alwaysI. *)
  (*   intros tr' [n Hsuff]. *)
  (*   revert tr tr' Hsuff HP. *)
  (*   induction n; intros tr tr' Hsuff HP. *)
  (*   { simpl in *. simplify_eq. apply HP. } *)
  (*   destruct tr; [done|]. *)
  (*   replace (Datatypes.S n) with (n + 1) in Hsuff by lia. *)
  (*   rewrite after_sum' in Hsuff. *)
  (*   destruct (after n (s -[ ℓ ]-> tr)) eqn:Heqn; [|done]. *)
  (*   eapply IHn in HP; [|done]. *)
  (*   rewrite /trace_entails in IHP. *)
  (*   specialize (IHP t). *)
  (*   rewrite trace_impliesI in IHP. *)
  (*   apply IHP in HP. *)
  (*   destruct t; [done|]. *)
  (*   simpl in *. simplify_eq. *)
  (*   apply trace_next_elim in HP. *)
  (*   done. *)
  (* Qed. *)

  Lemma trace_entails_always_l (P Q R: ltl_pred) :
    (⊢ R) → (P ∧ □ R ⊢ Q)%trace → (P ⊢ Q)%trace.
  Proof.
    intros HR HPQ tr HP.
    apply HPQ. apply trace_andI.
    split; [done|].
    apply trace_alwaysI. intros ??.
    apply HR. by destruct tr'.
  Qed.

  Lemma trace_eventually_and (P Q : ltl_pred) tr :
    (◊ (trace_and P Q)) tr → (◊ P) tr ∧ (◊ Q) tr.
  Proof.
    intros Hconj.
    induction Hconj using trace_eventually_ind.
    { apply trace_andI in H. destruct H as [H1 H2].
      split; by apply trace_eventually_intro. }
    destruct IHHconj as [H1 H2].
    split.
    - by constructor 2.
    - by constructor 2.
  Qed.

  Lemma trace_entails_implies' (P Q R : ltl_pred) :
    (P ∧ Q ⊢ R)%trace → (P ⊢ Q → R)%trace.
  Proof.
    rewrite /trace_entails.
    intros HPQ tr HP. rewrite trace_impliesI. intro HQ. apply HPQ.
    apply trace_andI. done.
  Qed.

  Lemma trace_entails_and_l_weak_l (P Q R : ltl_pred) :
    (Q ⊢ R) → (P ∧ Q ⊢ R)%trace.
  Proof.
    intros HQR tr. rewrite trace_andI. intros [_ HQ]. by apply HQR.
  Qed.

  Lemma trace_entails_and_l_comm (P Q R : ltl_pred) :
    (Q ∧ P ⊢ R)%trace → (P ∧ Q ⊢ R)%trace.
  Proof.
    intros HQR tr. rewrite trace_andI. intros [HP HQ]. apply HQR.
    apply trace_andI. done.
  Qed.

  Lemma trace_and_assoc (P Q : ltl_pred) :
    P ∧ Q ⊣⊢ Q ∧ P.
  Proof.
    split.
    - intros tr. rewrite !trace_andI. intros [HP HQ]. done.
    - intros tr. rewrite !trace_andI. intros [HP HQ]. done.
  Qed.

  Lemma trace_entails_trans (P Q R : ltl_pred) :
    (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. intros HPQ HQR tr HP. by apply HQR, HPQ. Qed.

  Lemma trace_bientails_trans_l (P Q R : ltl_pred) :
    (P ⊣⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. intros HPQ HQR tr HP. by apply HQR, HPQ. Qed.

  Lemma trace_bientails_trans_r (P Q R : ltl_pred) :
    (P ⊢ Q) → (Q ⊣⊢ R) → (P ⊢ R).
  Proof. intros HPQ HQR tr HP. by apply HQR, HPQ. Qed.

  Lemma trace_always_mono' (P Q R : ltl_pred) :
    (Q ⊢ R) → (P ⊢ □Q) → (P ⊢ □R).
  Proof.
    intros HQR HPQ tr HP. 
    apply trace_alwaysI.
    apply HPQ in HP.
    intros tr' Htr'.
    rewrite trace_alwaysI in HP.
    specialize (HP tr' Htr').
    by apply HQR.
  Qed.

  Lemma trace_entails_refl (P : ltl_pred) :
    P ⊢ P.
  Proof. intros tr. done. Qed.

  Lemma trace_eventually_mono' (P Q : ltl_pred) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof.
    intros HPQ tr. rewrite !trace_eventuallyI. intros [tr' [Htr' HP]].
    exists tr'. split; [done|]. by apply HPQ.
  Qed.

  Lemma trace_and_weak_r (P Q : ltl_pred) :
    (P ∧ Q) ⊢ P.
  Proof. intros tr. rewrite trace_andI. intros [HP _]. done. Qed.

  Lemma trace_and_weak_l (P Q : ltl_pred) :
    (P ∧ Q) ⊢ Q.
  Proof. intros tr. rewrite trace_andI. intros [_ HQ]. done. Qed.

  Lemma trace_bientails_comm (P Q : ltl_pred) :
    (P ⊣⊢ Q) ↔ (Q ⊣⊢ P).
  Proof. 
    split.
    - intros [HPQ HQP]. split; done.
    - intros [HQP HPQ]. split; done.
  Qed.

  Lemma trace_eventually_idemp' (P : ltl_pred) :
    (◊◊P) ⊢ (◊P).
  Proof.
    intros tr Htr. induction Htr using trace_eventually_ind; [done|].
    apply trace_eventually_cons. done.
  Qed.

  Lemma foo (P Q : ltl_pred) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    intros HPQ.
    eapply (trace_always_mono' _ (◊ (trace_and P Q))).
    { eapply trace_entails_trans.
      { apply trace_eventually_mono'. apply trace_and_weak_l. }
      apply trace_entails_refl. }
    apply trace_always_intro.
    { eapply trace_entails_trans; [apply HPQ|].
      eapply trace_bientails_trans_l.
      { apply trace_bientails_comm. apply trace_eventually_next_comm'. }
      eapply trace_entails_trans.
      { apply trace_eventually_next'. }
      apply trace_entails_refl. }
    eapply trace_entails_trans; [|apply trace_eventually_next_comm'].
    eapply trace_entails_trans; [|apply trace_eventually_idemp'].
    apply trace_eventually_mono'.
    eapply trace_entails_trans.
    { eapply trace_entails_trans; [apply trace_and_weak_r|]. 
      eapply trace_entails_trans; [apply HPQ|].
      apply trace_entails_refl. }
    eapply trace_bientails_trans_l.
    { apply trace_bientails_comm. apply trace_eventually_next_comm'. }
    apply trace_entails_refl.
  Qed.
    

  (* Lemma foo (P Q : ltl_pred) : *)
  (*   (⊢ P → ○◊ (trace_and P Q))%trace → *)
  (*   (⊢ P → □◊ Q)%trace. *)
  (* Proof. *)
  (*   intros HPQ tr. rewrite !trace_impliesI. intros _ HP. *)
  (*   eapply (trace_always_mono (◊ (trace_and P Q))). *)
  (*   { intros tr'. apply trace_impliesI. intros Hand. *)
  (*     apply trace_eventually_and in Hand. by destruct Hand. } *)
  (*   apply trace_always_intro. *)
  (*   { rewrite /trace_entails in HPQ. *)
  (*     specialize (HPQ tr). rewrite trace_impliesI in HPQ. *)
  (*     apply HPQ in HP; [|by destruct tr]. *)
  (*     apply trace_eventually_next_comm in HP. *)
  (*     by apply trace_eventually_next in HP. } *)
  (*   intros tr'. *)
  (*   apply trace_impliesI. *)
  (*   intros HPQ'. *)
  (*   apply trace_eventually_next_comm, trace_eventually_idemp. *)
  (*   revert HPQ'. apply trace_eventually_mono. *)
  (*   intros tr'' HPQ'. *)
  (*   apply trace_andI in HPQ'. *)
  (*   destruct HPQ' as [HP' HQ]. *)
  (*   specialize (HPQ tr''). rewrite trace_impliesI in HPQ. *)
  (*   apply HPQ in HP'; [|by destruct tr'']. by apply trace_eventually_next_comm. *)
  (* Qed.     *)
    
  Lemma trace_always_eventually_suffix_of tr1 tr2 (P : ltl_pred) :
    trace_suffix_of tr1 tr2 → (□◊ P) tr1 → (□◊ P) tr2.
  Proof.
    intros [n Hn] H1.
    apply trace_alwaysI.
    intros tr' [m Hm].
    apply trace_eventuallyI_alt.
    destruct (decide (m ≤ n)).
    - exists tr1. split.
      + exists (n - m). eapply after_levis =>//.
      + by apply trace_always_elim in H1.
    - exists tr'. split=>//.
      + exists 0. done.
      + assert (Hsuff: trace_suffix_of tr' tr1).
        * exists (m - n). assert (n ≤ m) by lia. eapply after_levis =>//.
        * rewrite trace_alwaysI_alt in H1. specialize (H1 tr' Hsuff).
          by apply trace_always_elim in H1.
  Qed.

  Lemma trace_always_eventually_always_implies (P Q : ltl_pred) tr :
    trace_always_eventually_implies P Q tr → (□P) tr → (◊Q) tr.
  Proof.
    intros HPQ HP.
    eapply trace_always_implies in HP; [|done].
    by apply trace_always_elim.
  Qed.

  Lemma trace_always_eventually_always_mono (P1 P2 Q1 Q2 : ltl_pred) tr :
    (∀ tr, trace_implies P2 P1 tr) → (∀ tr, trace_implies Q1 Q2 tr) →
    trace_always_eventually_implies P1 Q1 tr → trace_always_eventually_implies P2 Q2 tr.
  Proof.
    setoid_rewrite trace_impliesI.
    intros HP HQ Htr.
    eapply trace_always_mono; [|done].
    intros Htr'.
    apply trace_impliesI.
    rewrite !trace_impliesI.
    intros HPQ HP2.
    eapply trace_eventually_mono; [apply HQ|by apply HPQ; apply HP].
  Qed.

  Lemma trace_always_not_not_eventually (P : ltl_pred) (tr : trace S L) :
    (□ (trace_not P)) tr ↔ trace_not (◊ P) tr.
  Proof.
    split.
    - intros Halways Heventually.
      induction Heventually.
      { apply Halways. apply trace_eventually_intro. by apply P_NNP. }
      apply IHHeventually.
      by apply trace_always_cons in Halways.
    - intros Heventually Halways.
      induction Halways using trace_eventually_ind.
      { apply Heventually. apply trace_eventually_intro.
        eapply trace_not_mono in Heventually; [|by apply trace_eventually_intro].
        done. }
      apply IHHalways.
      intros Heventually'. apply Heventually. by apply trace_eventually_cons.
  Qed.

  Lemma trace_eventually_not_not_always (P : ltl_pred) (tr : trace S L) :
    (◊ trace_not P) tr ↔ (trace_not (□ P)) tr.
  Proof.
    split.
    - intros Heventually. apply P_NNP. done.
    - intros Halways. apply NNP_P in Halways. done.
  Qed.

  Lemma trace_always_and P Q (tr : trace S L) :
    (□ trace_and P Q) tr ↔ ((□ P) tr ∧ (□ Q) tr).
  Proof.
    split.
    - intros HPQ.
      assert ((□ P) tr ∨ ¬ (□ P) tr) as [|HP] by apply ExcludedMiddle; last first.
      { apply NNP_P in HP. induction HP using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ. apply IHHP in HPQ.
        destruct HPQ as [HP' HQ].
        apply trace_eventually_not_not_always in HP. done. }
      assert ((□ Q) tr ∨ ¬ (□ Q) tr) as [|HQ] by apply ExcludedMiddle; last first.
      { apply NNP_P in HQ. induction HQ using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ.
        apply trace_always_cons in H.
        apply IHHQ in HPQ; [|done].
        destruct HPQ as [HP HQ'].
        apply trace_eventually_not_not_always in HQ. done. }
      done.
    - intros [HP HQ] HPQ. induction HPQ.
      { apply H. apply trace_andI. apply trace_always_elim in HP, HQ. done. }
      by apply IHHPQ; eapply trace_always_cons.
  Qed.

  Lemma trace_weak_until_always P Q (tr : trace S L) :
    (□P) tr → trace_weak_until P Q tr.
  Proof. intros HP. by apply trace_or_r. Qed.

  (* TODO: Remove? *)
  Lemma trace_always_implies_always (P Q : ltl_pred) (tr : trace S L) :
    (∀ tr, (□P) tr → Q tr) → ((□P) tr → (□ Q) tr).
  Proof.
    intros HPQ HP%trace_always_idemp. eapply trace_always_mono; [|done].
    intros ?. apply trace_impliesI, HPQ.
  Qed.

End ltl_lemmas.

Section ltl_proofmode.
  Context {S L : Type}.
  
  Notation ltl_pred := (ltl_pred S L).

End ltl_proofmode.

Section ltl_theorems.
  Context {S L : Type}.

  Notation ltl_pred := (ltl_pred S L).

  (* Strong fairness implies our (network) fairness *)
  Lemma SF_implies_OF (P Q: ltl_pred) tr :
    ((□◊ P) → (□◊ Q))%trace tr → (□ ((□◊ P) → (◊ Q)))%trace tr.
  Proof.
    intros Hsf. apply trace_alwaysI. intros tr' Hsuff.
    apply trace_impliesI. intros Hae.
    eapply trace_always_eventually_suffix_of in Hae =>//.
    rewrite trace_impliesI in Hsf. specialize (Hsf Hae).
    apply trace_always_elim. by eapply trace_always_suffix_of.
  Qed.

  Lemma OF_implies_SF (P Q: ltl_pred) tr :
    (□ ((□◊ P) → (◊ Q)))%trace tr → ((□◊ P) → (□◊ Q))%trace tr.
  Proof.
    intros Hsf. apply trace_impliesI.
    intros HP. apply trace_always_idemp in HP. revert HP.
    by apply trace_always_implies.
  Qed.

  Theorem SF_equiv_OF (P Q: ltl_pred) tr :
    ((□◊ P) → (□◊ Q))%trace tr ≡ (□ ((□◊ P) → (◊ Q))) tr.
  Proof. split; [apply SF_implies_OF|apply OF_implies_SF]. Qed.

  (* Our (scheduling) Fairness implies Strong Fairness *)
  Lemma OF_implies_SF' (P Q: ltl_pred) tr :
    (□ (P → (◊ Q)))%trace tr → ((□◊ P) → (□◊ Q))%trace tr.
  Proof.
    intros Htr. apply trace_impliesI.
    apply trace_always_implies.
    rewrite trace_alwaysI_alt in Htr.
    rewrite trace_alwaysI.
    intros tr' Hsuffix.
    specialize (Htr tr' Hsuffix).
    apply trace_impliesI.
    intros HP.
    rewrite trace_eventuallyI in HP.
    destruct HP as [tr'' [Hsuffix' HP]].
    rewrite trace_alwaysI in Htr.
    specialize (Htr tr'' Hsuffix').
    rewrite trace_impliesI in Htr.
    rewrite trace_eventuallyI_alt.
    exists tr''. split; [done|].
    apply Htr. done.
  Qed.

End ltl_theorems.
