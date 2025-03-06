From Paco Require Import paconotation.
From fairneris Require Export inftraces.

Declare Scope trace_scope.
Delimit Scope trace_scope with trace.
Bind Scope trace_scope with trace.

Definition ltl_pred S L := trace S L → Prop.

Section ltl_constructors.
  Context {S L : Type}.
  Notation ltl_pred := (ltl_pred S L).
  Implicit Type P Q : ltl_pred.

  Inductive trace_entails (P Q : ltl_pred) : Prop :=
    { trace_in_entails : ∀ tr, P tr → Q tr }.
  
  (* Primitive operators *)
  Definition trace_now (P : S → option L → Prop) : ltl_pred :=
    λ tr, pred_at tr 0 P.
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

  Lemma trace_entails_refl (P : ltl_pred) :
    P ⊢ P.
  Proof. constructor. intros tr. done. Qed.

  Lemma trace_entails_trans (P Q R : ltl_pred) :
    (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. intros HPQ HQR. constructor. intros tr HP. by apply HQR, HPQ. Qed.

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
  Proof. constructor. intros tr. destruct tr; done. Qed.

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
    intros HPQ. constructor. intro tr. rewrite trace_impliesI.
    intros _. apply HPQ.
  Qed.

  Lemma trace_implies_entails (P Q : ltl_pred) :
    (⊢ P → Q)%trace → (P ⊢ Q)%trace.
  Proof.
    intros HPQ.
    constructor.    
    intros tr HP. destruct HPQ as [HPQ].
    specialize (HPQ tr). rewrite trace_impliesI in HPQ.
    apply HPQ.
    - by destruct tr. (* OBS: Hacky *)
    - done.
  Qed.

  (** trace_not lemmas *)

  Lemma trace_notI (P : ltl_pred) :
    trace_not P ⊣⊢ ¬ P.
  Proof. split; split; intros tr; done. Qed.

  Lemma trace_not_idemp (P : ltl_pred) :
    ¬ (¬ P) ⊣⊢ P.
  Proof. split; split; intros tr; [apply NNP_P|apply P_NNP]. Qed.

  Lemma trace_not_mono (P Q : ltl_pred) :
    (Q ⊢ P) → (¬ P ⊢ ¬ Q)%trace.
  Proof. intros HQP. constructor. intros tr HP HQ. apply HP. by apply HQP. Qed.
  
  (** trace_next lemmas *)

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
    intros HPQ. constructor.
    intros tr HP. simpl in *.
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
    constructor.
    intros tr _. rewrite trace_impliesI. intros HP.
    by left.
  Qed.

  Lemma trace_or_r (P Q : ltl_pred) :
    Q ⊢ P ∨ Q.
  Proof.
    apply trace_implies_entails.
    constructor.
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
  Proof. by constructor; constructor 1. Qed.

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
    constructor.
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
    - constructor.
      intros tr Hnext.
      induction Hnext using trace_eventually_ind.
      { destruct tr; [inversion H; naive_solver|].
        revert H. apply trace_next_mono. apply trace_eventually_intro. }
      apply trace_next_intro. apply trace_eventually_next. done.
    - constructor.
      intros tr Hnext.
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

  Lemma trace_always_idemp' (P : ltl_pred) :
    (□ P) ⊢ (□ □ P).
  Proof.
    constructor.
    intros tr Htr Htr'. induction Htr'; [by apply H|].
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

  Lemma trace_always_elim' (P : ltl_pred) :
    (□P) ⊢ P.
  Proof.
    constructor.
    intros tr Htr.
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

  (* Lemma trace_always_and (P Q : ltl_pred) : *)
  (*   (□ (P ∧ Q))%trace ⊢ (□ P) ∧ (□ Q). *)
  (* Proof. *)
  (*   intros tr. rewrite !trace_alwaysI. *)
  (*   rewrite !trace_andI. *)
  (*   intros HPQ. *)
  (*   split. *)
  (*   - rewrite trace_alwaysI. *)
  (*     intros tr' Hsuff. apply HPQ in Hsuff. *)
  (*     apply trace_andI in Hsuff. by destruct Hsuff as [HP _]. *)
  (*   - rewrite trace_alwaysI. *)
  (*     intros tr' Hsuff. apply HPQ in Hsuff. *)
  (*     apply trace_andI in Hsuff. by destruct Hsuff as [_ HQ]. *)
  (* Qed. *)
    
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

  Lemma trace_always_forall' {A} (P : A → ltl_pred) :
    (trace_forall (λ (x:A), (□ (P x))))%trace ⊣⊢
    (□ (trace_forall (λ (x:A), P x))).
  Proof.
    split.
    - constructor.
      intros tr Htr Htr'.
      induction Htr' using trace_eventually_ind.
      { apply H. intros x. specialize (Htr x).
        apply trace_always_elim in Htr. apply Htr. }
      apply IHHtr'.
      intros x. specialize (Htr x).
      by apply trace_always_cons in Htr.
    - constructor.
      intros tr Htr x Htr'.
      induction Htr' using trace_eventually_ind.
      { apply H. apply trace_always_elim in Htr. apply Htr. }
      apply IHHtr'. by apply trace_always_cons in Htr.
  Qed.

  (* Lemma trace_always_exists' {A} (P : A → ltl_pred) : *)
  (*   (trace_exists (λ (x:A), (□ (P x))))%trace ⊣⊢ *)
  (*   (□ (trace_exists (λ (x:A), P x))). *)
  (* Proof. *)
  (*   split. *)
  (*   - intros tr Htr Htr'. *)
  (*     induction Htr' using trace_eventually_ind. *)
  (*     { apply H. destruct Htr as [x Htr]. exists x.  *)
  (*       apply trace_always_elim in Htr. apply Htr. } *)
  (*     apply IHHtr'. *)
  (*     destruct Htr as [x Htr]. exists x. *)
  (*     by apply trace_always_cons in Htr. *)
  (*   - intros tr Htr. *)
  (*     rewrite trace_alwaysI in Htr.       *)
  (*     induction Htr' using trace_eventually_ind. *)
  (*     { apply H. apply trace_always_elim in Htr. apply Htr. } *)
  (*     apply IHHtr'. by apply trace_always_cons in Htr. *)
  (* Qed. *)

  Lemma trace_always_exists' {A} (P : A → ltl_pred) :
    (trace_exists (λ (x:A), (□ (P x))))%trace ⊢
    (□ (trace_exists (λ (x:A), P x))).
  Proof.
    constructor.
    intros tr Htr Htr'.
    induction Htr' using trace_eventually_ind.
    { apply H. destruct Htr as [x Htr]. exists x. 
      apply trace_always_elim in Htr. apply Htr. }
    apply IHHtr'.
    destruct Htr as [x Htr]. exists x.
    by apply trace_always_cons in Htr.
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
    constructor.
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
    intros HPQ IHQ.
    constructor.
    intros tr HP.
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

  Lemma trace_always_intro' (P : ltl_pred) :
    (⊢ P) → (⊢ □ P)%trace.
  Proof.
    intros HP.
    constructor.
    intros tr _. apply trace_alwaysI.
    intros tr' Hsuff. apply HP. by destruct tr'.
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
    intros HR HPQ.
    constructor.
    intros tr HP.
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
    intros HPQ.
    constructor.
    intros tr HP. rewrite trace_impliesI. intro HQ. apply HPQ.
    apply trace_andI. done.
  Qed.

  Lemma trace_entails_and_l_weak_l (P Q R : ltl_pred) :
    (Q ⊢ R) → (P ∧ Q ⊢ R)%trace.
  Proof.
    intros HQR. constructor. intros tr. rewrite trace_andI. intros [_ HQ]. by apply HQR.
  Qed.

  Lemma trace_entails_and_l_comm (P Q R : ltl_pred) :
    (Q ∧ P ⊢ R)%trace → (P ∧ Q ⊢ R)%trace.
  Proof.
    intros HQR. constructor. intros tr. rewrite trace_andI. intros [HP HQ]. apply HQR.
    apply trace_andI. done.
  Qed.

  Lemma trace_and_assoc (P Q : ltl_pred) :
    P ∧ Q ⊣⊢ Q ∧ P.
  Proof.
    split.
    - constructor. intros tr. rewrite !trace_andI. intros [HP HQ]. done.
    - constructor. intros tr. rewrite !trace_andI. intros [HP HQ]. done.
  Qed.

  Lemma trace_bientails_trans_l (P Q R : ltl_pred) :
    (P ⊣⊢ Q) → (Q ⊢ R) → (P ⊢ R).
  Proof. intros HPQ HQR. constructor. intros tr HP. by apply HQR, HPQ. Qed.

  Lemma trace_bientails_trans_r (P Q R : ltl_pred) :
    (P ⊢ Q) → (Q ⊣⊢ R) → (P ⊢ R).
  Proof. intros HPQ HQR. constructor. intros tr HP. by apply HQR, HPQ. Qed.

  Lemma trace_always_mono' (P Q R : ltl_pred) :
    (Q ⊢ R) → (P ⊢ □Q) → (P ⊢ □R).
  Proof.
    intros HQR HPQ. constructor. intros tr HP. 
    apply trace_alwaysI.
    apply HPQ in HP.
    intros tr' Htr'.
    rewrite trace_alwaysI in HP.
    specialize (HP tr' Htr').
    by apply HQR.
  Qed.

  Lemma trace_eventually_mono' (P Q : ltl_pred) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof.
    intros HPQ. constructor. intros tr.
    rewrite !trace_eventuallyI. intros [tr' [Htr' HP]].
    exists tr'. split; [done|]. by apply HPQ.
  Qed.

  Lemma trace_and_intro (P Q R : ltl_pred) :
    (P ⊢ Q) → (P ⊢ R) → (P ⊢ Q ∧ R).
  Proof.
    intros HPQ HPR. constructor. intros tr. rewrite trace_andI.
    intros HP. split; [by apply HPQ|by apply HPR].
  Qed.

  Lemma trace_and_weak_r (P Q : ltl_pred) :
    (P ∧ Q) ⊢ P.
  Proof. constructor. intros tr. rewrite trace_andI. intros [HP _]. done. Qed.

  Lemma trace_and_weak_l (P Q : ltl_pred) :
    (P ∧ Q) ⊢ Q.
  Proof. constructor. intros tr. rewrite trace_andI. intros [_ HQ]. done. Qed.

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
    constructor. intros tr Htr. induction Htr using trace_eventually_ind; [done|].
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

  Lemma trace_always_and' (P Q : ltl_pred) :
    (□ (P ∧ Q)) ⊣⊢ ((□ P) ∧ (□ Q)).
  Proof.
    split.
    - constructor. intros tr HPQ.
      assert ((□ P) tr ∨ ¬ (□ P) tr) as [|HP] by apply ExcludedMiddle; last first.
      { apply NNP_P in HP. induction HP using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ. apply IHHP in HPQ.
        rewrite trace_andI in HPQ.
        destruct HPQ as [HP' HQ].
        apply trace_eventually_not_not_always in HP. done. }
      assert ((□ Q) tr ∨ ¬ (□ Q) tr) as [|HQ] by apply ExcludedMiddle; last first.
      { apply NNP_P in HQ. induction HQ using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ.
        apply trace_always_cons in H.
        apply IHHQ in HPQ; [|done].
        rewrite trace_andI in HPQ.
        destruct HPQ as [HP HQ'].
        apply trace_eventually_not_not_always in HQ. done. }
      rewrite trace_andI.
      done.
    - constructor. intros tr. rewrite trace_andI. intros [HP HQ] HPQ. induction HPQ.
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

From iris.bi Require Export bi.
From iris.prelude Require Import options.

Definition trace_emp {S L} : ltl_pred S L := trace_true.
(* Definition trace_sep {S L} : ltl_pred S L → ltl_pred S L → ltl_pred S L := *)
(*   trace_and. *)
(* Definition trace_wand {S L} : ltl_pred S L → ltl_pred S L → ltl_pred S L := *)
(*   trace_implies. *)
Definition trace_persistently {S L} (P : ltl_pred S L) : ltl_pred S L := P.
Definition trace_plainly {S L} (P : ltl_pred S L) : ltl_pred S L := P.
Definition trace_pure {S L} (P : Prop) : ltl_pred S L := λ tr, P.

Section ltl_meta.
  Context {S L : Type}.
  Notation ltl_pred := (ltl_pred S L).
          
  Global Instance ltl_equiv : Equiv (ltl_pred) := λ P Q, (P ⊣⊢ Q)%trace.
  Global Instance ltl_dist : Dist (ltl_pred) := λ n P Q, (P ⊣⊢ Q)%trace.
  Lemma ltl_entails_po : PreOrder (@trace_entails S L).
  Proof.
    split.
    - intros tr. apply (@trace_entails_refl S L).
    - intros tr. apply (@trace_entails_trans S L).
  Qed.

  Lemma ltl_entails_anti_symm : AntiSymm (≡) trace_entails.
  Proof. intros P Q HPQ HQP; by split; [apply HPQ|apply HQP]. Qed.

  Lemma ltl_equiv_entails (P Q : ltl_pred) :
    (P ≡ Q) ↔ (P ⊢ Q)%trace ∧ (Q ⊢ P)%trace.
  Proof.
    split.
    - intros HPQ; split; apply HPQ. 
    - intros [??]. by apply ltl_entails_anti_symm.
  Qed.

  (* Lemma pure_ne n : Proper (iff ==> dist n) trace_pure. *)
  (* Proof. Admitted. *)
  (* Lemma and_ne : NonExpansive2 siProp_and. *)
  (* Proof. *)
  (*   intros n P P' HP Q Q' HQ; unseal; split=> n' ?. *)
  (*   split; (intros [??]; split; [by apply HP|by apply HQ]). *)
  (* Qed. *)
  (* Lemma or_ne : NonExpansive2 siProp_or. *)
  (* Proof. *)
  (*   intros n P P' HP Q Q' HQ; split=> n' ?. *)
  (*   unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]). *)
  (* Qed. *)
  (* Lemma impl_ne : NonExpansive2 siProp_impl. *)
  (* Proof. *)
  (*   intros n P P' HP Q Q' HQ; split=> n' ?. *)
  (*   unseal; split; intros HPQ n'' ??; apply HQ, HPQ, HP; auto with lia. *)
  (* Qed. *)

End ltl_meta. 

Local Existing Instance ltl_entails_po.

(* Definition trace_exists' {S L} (P : A → ltl_pred S L) : ltl_pred S L :=  *)
(*   P (). *)

Lemma ltl_bi_mixin {S L} :
  BiMixin
    trace_entails trace_emp trace_pure trace_and trace_or trace_implies
    (@trace_forall S L) (@trace_exists S L) trace_and trace_implies.
Proof. Admitted.
(*   split. *)
(*   - exact: ltl_entails_po. *)
(*   - exact: ltl_equiv_entails. *)
(*   - exact: ltl_pure_ne. *)
(*   - exact: and_ne. *)
(*   - exact: or_ne. *)
(*   - exact: impl_ne. *)
(*   - exact: forall_ne. *)
(*   - exact: exist_ne. *)
(*   - exact: and_ne. *)
(*   - exact: impl_ne. *)
(*   - exact: pure_intro. *)
(*   - exact: pure_elim'. *)
(*   - exact: and_elim_l. *)
(*   - exact: and_elim_r. *)
(*   - exact: and_intro. *)
(*   - exact: or_intro_l. *)
(*   - exact: or_intro_r. *)
(*   - exact: or_elim. *)
(*   - exact: impl_intro_r. *)
(*   - exact: impl_elim_l'. *)
(*   - exact: @forall_intro. *)
(*   - exact: @forall_elim. *)
(*   - exact: @exist_intro. *)
(*   - exact: @exist_elim. *)
(*   - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *) *)
(*     intros P P' Q Q' H1 H2. apply and_intro. *)
(*     + by etrans; first apply and_elim_l. *)
(*     + by etrans; first apply and_elim_r. *)
(*   - (* P ⊢ emp ∗ P *) *)
(*     intros P. apply and_intro; last done. by apply pure_intro. *)
(*   - (* emp ∗ P ⊢ P *) *)
(*     intros P. apply and_elim_r. *)
(*   - (* P ∗ Q ⊢ Q ∗ P *) *)
(*     intros P Q. apply and_intro; [ apply and_elim_r | apply and_elim_l ]. *)
(*   - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *) *)
(*     intros P Q R. repeat apply and_intro. *)
(*     + etrans; first apply and_elim_l. by apply and_elim_l. *)
(*     + etrans; first apply and_elim_l. by apply and_elim_r. *)
(*     + apply and_elim_r. *)
(*   - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *) *)
(*     apply impl_intro_r. *)
(*   - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *) *)
(*     apply impl_elim_l'. *)
(* Qed. *)

Lemma ltl_bi_persistently_mixin {S L} :
  BiPersistentlyMixin
    trace_entails trace_emp trace_and
    (@trace_exists S L) trace_and trace_persistently.
Proof. Admitted.
(*   split. *)
(*   - admit. *)
(*   - intros P Q HPQ.  *)
(*     eapply trace_always_mono'; [apply HPQ|]. *)
(*     apply trace_entails_refl. *)
(*   - intros P. apply trace_always_idemp'. *)
(*   - apply trace_always_intro'. apply trace_trueI. *)
(*   - intros P Q. apply trace_always_and'. *)
(*   - intros A Ψ.  *)
(*     ∃ *)
(*     admit. *)
(*   - intros P Q. rewrite /trace_sep. apply trace_and_weak_r. *)
(*   - intros P Q. *)
(*     apply trace_and_intro. *)
(*     + eapply trace_entails_trans. *)
(*       { apply trace_and_weak_r. } *)
(*       apply trace_always_elim'. *)
(*     + eapply trace_entails_trans. *)
(*       { apply trace_and_weak_l. } *)
(*       apply trace_entails_refl. *)
(* Admitted. *)

Lemma ltl_bi_later_mixin {S L }:
  BiLaterMixin
    trace_entails trace_pure trace_or trace_implies
    (@trace_forall S L) (@trace_exists S L) trace_and trace_persistently trace_next.
Proof. Admitted.
  (* split. *)
(*   - apply contractive_ne, later_contractive. *)
(*   - exact: later_mono. *)
(*   - exact: later_intro. *)
(*   - exact: @later_forall_2. *)
(*   - exact: @later_exist_false. *)
(*   - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *) *)
(*     intros P Q. *)
(*     apply and_intro; apply later_mono. *)
(*     + apply and_elim_l. *)
(*     + apply and_elim_r. *)
(*   - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *) *)
(*     intros P Q. *)
(*     trans (siProp_forall (λ b : bool, siProp_later (if b then P else Q))). *)
(*     { apply forall_intro=> -[]. *)
(*       - apply and_elim_l. *)
(*       - apply and_elim_r. } *)
(*     etrans; [apply later_forall_2|apply later_mono]. *)
(*     apply and_intro. *)
(*     + refine (forall_elim true). *)
(*     + refine (forall_elim false). *)
(*   - (* ▷ <pers> P ⊢ <pers> ▷ P *) *)
(*     done. *)
(*   - (* <pers> ▷ P ⊢ ▷ <pers> P *) *)
(*     done. *)
(*   - exact: later_false_em. *)
(* Qed. *)

Definition ltl_ofe_mixin {S L} : OfeMixin (ltl_pred S L).
Proof. Admitted.

Canonical Structure ltl_predO S L : ofe := Ofe (ltl_pred S L) (@ltl_ofe_mixin S L).

Program Definition ltl_compl {S L} : Compl (ltl_predO S L) := _.
Next Obligation. Admitted.

Global Program Instance ltl_cofe {S L} : Cofe (ltl_predO S L) :=
  {| compl := (@ltl_compl S L) |}.
Next Obligation. Admitted.

Canonical Structure ltlI {S L} : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (ltl_pred S L);
     bi_bi_mixin := @ltl_bi_mixin S L;
     bi_bi_persistently_mixin := @ltl_bi_persistently_mixin S L;
     bi_bi_later_mixin := @ltl_bi_later_mixin S L |}.

Global Instance ltl_pure_forall {S L} : BiPureForall (@ltlI S L).
Proof. Admitted.

Global Instance siProp_later_contractive {S L} :
  BiLaterContractive (@ltlI S L).
Proof. Admitted.

Definition trace_internal_eq {S L} {A : ofe} (a1 a2 : A) : ltl_pred S L :=
  λ tr, a1 ≡ a2.

Lemma siProp_internal_eq_mixin {S L} :
  BiInternalEqMixin (@ltlI S L) (@trace_internal_eq S L).
Proof. Admitted.
(*   split. *)
(*   - exact: internal_eq_ne. *)
(*   - exact: @internal_eq_refl. *)
(*   - exact: @internal_eq_rewrite. *)
(*   - exact: @fun_ext. *)
(*   - exact: @sig_eq. *)
(*   - exact: @discrete_eq_1. *)
(*   - exact: @later_eq_1. *)
(*   - exact: @later_eq_2. *)
(* Qed. *)
Global Instance siProp_internal_eq {S L} : BiInternalEq (@ltlI S L) :=
  {| bi_internal_eq_mixin := siProp_internal_eq_mixin |}.

Lemma ltl_plainly_mixin {S L} : BiPlainlyMixin (@ltlI S L) trace_plainly.
Proof. Admitted.
(*   split; try done. *)
(*   - solve_proper. *)
(*   - (* P ⊢ ■ emp *) *)
(*     intros P. by apply pure_intro. *)
(*   - (* ■ P ∗ Q ⊢ ■ P *) *)
(*     intros P Q. apply and_elim_l. *)
(* Qed. *)
Global Instance ltl_plainlyC {S L} : BiPlainly (@ltlI S L) :=
  {| bi_plainly_mixin := ltl_plainly_mixin |}.

Global Instance ltl_prop_ext {S L} : BiPropExt (@ltlI S L).
Proof. Admitted.

(* (** extra BI instances *) *)

Global Instance ltl_affine {S L} : BiAffine (@ltlI S L) | 0.
Proof. Admitted.
(* Also add this to the global hint database, otherwise [eauto] won't work for *)
(* many lemmas that have [BiAffine] as a premise. *)
Global Hint Immediate ltl_affine : core.

Global Instance ltl_plain {S L} (P : ltl_pred S L) : Plain P | 0.
Proof. Admitted.
Global Instance ltl_persistent {S L} (P : ltl_pred S L) : Persistent P.
Proof. Admitted.

Global Instance siProp_plainly_exist_1 {S L} : BiPlainlyExist (@ltlI S L).
Proof. Admitted.

(** Re-state/export soundness lemmas *)

Module ltlpred.
Section restate.
  Context {S L : Type}.

  Notation ltlI := (@ltlI S L).
  Notation ltl_pred := (ltl_pred S L).
          
  Lemma pure_soundness φ : (⊢@{ltlI} ⌜ φ ⌝) → φ.
  Proof. Admitted.
  Lemma internal_eq_soundness {A : ofe} (x y : A) : (⊢@{ltlI} x ≡ y) → x ≡ y.
  Proof. Admitted.

  Lemma later_soundness (P : ltl_pred) : (⊢ ▷ P) → ⊢ P.
  Proof. Admitted.

  (** We restate the unsealing lemmas so that they also unfold the BI layer. The *)
(*   sealing lemmas are partially applied so that they also work under binders. *)
  Local Lemma ltl_emp_unseal : bi_emp = @trace_emp S L.
  Proof. Admitted.
  Local Lemma ltl_pure_unseal : bi_pure = @trace_pure S L.
  Proof. Admitted.
  Local Lemma ltl_and_unseal : bi_and = @trace_and S L.
  Proof. Admitted.
  Local Lemma ltl_or_unseal : bi_or = @trace_or S L.
  Proof. Admitted.
  Local Lemma ltl_impl_unseal : bi_impl = @trace_implies S L.
  Proof. Admitted.
  Local Lemma ltl_forall_unseal : @bi_forall _ = @trace_forall S L.
  Proof. Admitted.
  Local Lemma ltl_exist_unseal : @bi_exist _ = @trace_exists S L.
  Proof. Admitted.
  Local Lemma ltl_sep_unseal : bi_sep = @trace_and S L.
  Proof. Admitted.
  Local Lemma ltl_wand_unseal : bi_wand = @trace_implies S L.
  Proof. Admitted.
  Local Lemma ltl_plainly_unseal : plainly = @id ltlI.
  Proof. Admitted.
  Local Lemma ltl_persistently_unseal : bi_persistently = @id ltlI.
  Proof. Admitted.
  Local Lemma ltl_later_unseal : bi_later = @trace_next S L.
  Proof. Admitted.
  Local Lemma ltl_internal_eq_unseal :
    @internal_eq _ _ = @trace_internal_eq S L.
  Proof. Admitted.

  Local Definition ltl_unseal :=
    (ltl_emp_unseal, ltl_pure_unseal, ltl_and_unseal, ltl_or_unseal,
    ltl_impl_unseal, ltl_forall_unseal, ltl_exist_unseal,
    ltl_sep_unseal, ltl_wand_unseal,
    ltl_plainly_unseal, ltl_persistently_unseal, ltl_later_unseal,
    ltl_internal_eq_unseal).
End restate.

(** The final unseal tactic that also unfolds the BI layer. *)
Ltac unseal := rewrite !ltl_unseal /=.
End ltlpred.

(* Override bi notation for persistent to use LTL always *)

From iris.proofmode Require Import proofmode.

Notation "□ P" := (trace_always P) : bi_scope.

Notation "□^ P" := (bi_intuitionistically P) (at level 20, right associativity).
Notation "'□^?' p P" := (bi_intuitionistically_if p P) (at level 20, p at level 9, P at level 20,
   right associativity, format "'□^?' p  P").

Section ltl_proofmode.
  Context {S L : Type}.
  
  Notation ltl_pred := (ltl_pred S L).

  Lemma bi_intuitionistically_id (P : ltl_pred) :
    □^ P ⊣⊢ P.
  Proof. Admitted.

  Lemma trace_eventually_and' (P Q : ltl_pred) :
    (◊ (P ∧ Q)) ⊢ (◊ P) ∧ (◊ Q).
  Proof.
    constructor.
    intros tr Hconj.
    induction Hconj using trace_eventually_ind.
    { apply trace_andI in H. destruct H as [H1 H2].
      apply trace_andI.
      split; by apply trace_eventually_intro. }
    apply trace_andI in IHHconj.
    destruct IHHconj as [H1 H2].
    apply trace_andI.
    split.
    - by constructor 2.
    - by constructor 2.
  Qed.

  Global Instance into_wand_next p (P Q R : ltl_pred) :
    IntoWand p p R P Q → IntoWand p p (○ R)%trace (○ P)%trace (○ Q)%trace.
  Proof.
    rewrite /IntoWand.
    destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros HR. rewrite HR. iIntros "HPQ HP". by iApply "HPQ".
    - intros HR. rewrite HR. iIntros "HPQ HP". by iApply "HPQ".
  Qed.
  Global Instance into_wand_next_args p (P Q R : ltl_pred) :
    IntoWand' p p R P Q → IntoWand' p p (R)%trace (○ P)%trace (○ Q)%trace.
  Proof. 
    rewrite /IntoWand' /IntoWand.
    destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros HR. rewrite HR. iIntros "HPQ HP". by iApply "HPQ".
    - intros HR. rewrite HR. iIntros "HPQ HP". by iApply "HPQ".
  Qed.
  Global Instance into_wand_always p (P Q R : ltl_pred) :
    IntoWand p p R P Q → IntoWand p p (□ R)%trace (□ P)%trace (□ Q)%trace.
  Proof.
    rewrite /IntoWand.
    destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros HR. 
      iApply trace_entails_trans.
      { iApply trace_always_mono'; [apply HR|done]. }
      iIntros "HPQ HP".
      iAssert (□ ((P -∗ Q) ∧ P))%I with "[HPQ HP]" as "HP'".
      { rewrite trace_always_and'. by iSplit. }
      iStopProof. eapply trace_always_mono'; [|done].
      iIntros "[HPQ HP]". by iApply "HPQ".
    - intros HR. 
      iApply trace_entails_trans.
      { iApply trace_always_mono'; [apply HR|done]. }
      iIntros "HPQ HP".
      iAssert (□ ((P -∗ Q) ∧ P))%I with "[HPQ HP]" as "HP'".
      { rewrite trace_always_and'. by iSplit. }
      iStopProof. eapply trace_always_mono'; [|done].
      iIntros "[HPQ HP]". by iApply "HPQ".
  Qed.
  (* Global Instance into_wand_always_args p (P Q R : ltl_pred) : *)
  (*   IntoWand' p p R P Q → IntoWand' p p (R)%trace (□ P)%trace (□ Q)%trace. *)
  (* Proof. *)
  (*   rewrite /IntoWand' /IntoWand. *)
  (*   destruct p; simpl; [rewrite !bi_intuitionistically_id|]. *)
  (*   - intros HR. rewrite HR. *)
  (*     iIntros "HPQ HP". *)
  (*     iAssert (□ ((P -∗ Q) ∧ P))%I with "[HPQ HP]" as "HP'". *)
  (*     { rewrite trace_always_and'. by iSplit. } *)
  (*     iStopProof. eapply trace_always_mono'; [|done]. *)
  (*     iIntros "[HPQ HP]". by iApply "HPQ". *)
  (*   - intros HR. rewrite HR. *)
  (*     iIntros "HPQ HP". *)
  (*     iAssert (□ ((P -∗ Q) ∧ P))%I with "[HPQ HP]" as "HP'". *)
  (*     { rewrite trace_always_and'. by iSplit. } *)
  (*     iStopProof. eapply trace_always_mono'; [|done]. *)
  (*     iIntros "[HPQ HP]". by iApply "HPQ". *)
  (* Qed. *)

  (* Global Instance into_wand_eventually_args p q (P Q R : ltl_pred) : *)
  (*   IntoWand p q R P Q → IntoWand' p q (R)%trace (◊ P)%trace (◊ Q)%trace. *)
  (* Proof. Admitted. *)

  (* TODO: Why is this needed??? *)
  Lemma trace_always_and'' (P Q : ltl_pred) :
    (□ (P ∧ Q)) ⊣⊢ ((□ P) ∧ (□ Q)).
  Proof. apply trace_always_and'. Qed.

  Global Instance into_and_always b (P Q1 Q2 : ltl_pred) :
    @IntoAnd ltlI b P Q1 Q2 →
    @IntoAnd ltlI b (□ P)%trace (□ Q1)%trace (□ Q2)%trace.
  Proof.
    destruct b; simpl.
    - rewrite /IntoAnd. simpl. rewrite !bi_intuitionistically_id.
      intros HPQ.
      rewrite -(trace_always_and'' Q1 Q2).
      by eapply trace_always_mono'.
    - rewrite /IntoAnd. simpl.
      intros HPQ.
      rewrite -(trace_always_and'' Q1 Q2).
      by eapply trace_always_mono'.
  Qed.

  Global Instance into_and_eventually b (P Q1 Q2 : ltl_pred) :
    @IntoAnd ltlI b P Q1 Q2 →
    @IntoAnd ltlI b (◊ P)%trace (◊ Q1)%trace (◊ Q2)%trace.
  Proof.
    destruct b; simpl.
    - rewrite /IntoAnd. simpl. rewrite !bi_intuitionistically_id.
      intros HPQ.
      rewrite -trace_eventually_and'.
      by eapply trace_eventually_mono'.
    - rewrite /IntoAnd. simpl.
      intros HPQ.
      rewrite -trace_eventually_and'.
      by eapply trace_eventually_mono'.
  Qed.

  Global Instance elim_modal_always p (P Q : ltl_pred) :
    @ElimModal ltlI True%type p p (□ P)%trace P Q Q.
  Proof.
    rewrite /ElimModal; destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros _. iIntros "[HP HPQ]". iApply "HPQ". by rewrite trace_always_elim'.
    - intros _. iIntros "[HP HPQ]". iApply "HPQ". by rewrite trace_always_elim'.
  Qed.
  Class IntoEventually (P Q : ltl_pred) :=
    into_eventually (p:bool) : □?p P ⊢ ◊ Q.
  Global Arguments IntoEventually _%I _%I : simpl never.
  Global Arguments into_eventually _%I _%I {_}.
  Global Hint Mode IntoEventually ! - : typeclass_instances.

  Instance into_eventually_eventually (P : ltl_pred) :
    IntoEventually (◊ P) P.
  Proof.
    rewrite /IntoEventually. intros p.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Instance into_eventually_next (P Q : ltl_pred) :
    IntoEventually P Q →
    IntoEventually (○ P) (○ Q).
  Proof.
    rewrite /IntoEventually. intros HPQ p.
    destruct p; simpl.
    - rewrite trace_eventually_next_comm'.
      iIntros "#HP".
      specialize (HPQ true). simpl in HPQ.
      by iDestruct (HPQ with "HP") as "PQ".
    - rewrite trace_eventually_next_comm'.
      iIntros "HP".
      specialize (HPQ false). simpl in HPQ.
      by iDestruct (HPQ with "HP") as "PQ".
  Qed.

  Class IntoNext (P Q : ltl_pred) :=
    into_next (p:bool) : □?p P ⊢ ○ Q.
  Global Arguments IntoNext _%I _%I : simpl never.
  Global Arguments into_next _%I _%I {_}.
  Global Hint Mode IntoNext ! - : typeclass_instances.

  Instance into_next_next (P : ltl_pred) :
    IntoNext (○ P) P.
  Proof.
    rewrite /IntoNext. intros p.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Instance into_next_eventually (P Q : ltl_pred) :
    IntoNext P Q →
    IntoNext (◊ P) (◊ Q).
  Proof.
    rewrite /IntoNext. intros HPQ p.
    destruct p; simpl; [rewrite bi_intuitionistically_id|].
    - rewrite -trace_eventually_next_comm'.
      eapply trace_eventually_mono'.
      specialize (HPQ true). simpl in HPQ.
      rewrite bi_intuitionistically_id in HPQ.
      done.
    - rewrite -trace_eventually_next_comm'.
      eapply trace_eventually_mono'.
      specialize (HPQ true). simpl in HPQ.
      rewrite bi_intuitionistically_id in HPQ.
      done.
  Qed.

  Class AlwaysTransform (P Q : ltl_pred) : Prop.
  Instance always_transform_always (P : ltl_pred) :
    AlwaysTransform (□ P) (□ P).
  Proof. Qed.
  Lemma modality_always_mixin : modality_mixin (@id ltlI)
    (MIEnvTransform AlwaysTransform) (MIEnvTransform AlwaysTransform).
  Proof. split; simpl; eauto. Admitted.

  Definition modality_always := Modality (@id ltlI) modality_always_mixin.
  Global Instance from_modal_always (P : ltl_pred) :
    @FromModal ltlI ltlI _ True%type modality_always (□ P)%trace (□ P)%trace (P)%trace.
  Proof. Admitted.

  Class EventuallyTransform (P Q : ltl_pred) : Prop.
  Instance eventually_transform_eventually (P : ltl_pred) :
    EventuallyTransform (◊ P) P.
  Proof. Qed.
  Lemma modality_eventually_mixin : modality_mixin (@id ltlI)
    (MIEnvTransform EventuallyTransform)
    (MIEnvTransform EventuallyTransform).
  Proof. split; simpl; eauto. Admitted.

  Definition modality_eventually := Modality (@id ltlI) modality_eventually_mixin.
  (* Global Instance from_modal_eventually (P : ltl_pred) : *)
  (*   @FromModal ltlI ltlI _ True%type modality_eventually (◊ P)%trace (◊ P)%trace (P)%trace . *)
  (* Proof. Admitted. *)

  (* TODO: This is unsound, as it does not clean up the context *)
  Global Instance elim_modal_eventually p (P Q R R' : ltl_pred) :
    IntoEventually P Q →
    IntoEventually R R' →
    @ElimModal ltlI True%type p p (P)%trace Q R (◊ R').
  Proof. Admitted.

  (* (* TODO: This is unsound, as it does not clean up the context *) *)
  (* Global Instance elim_modal_eventually_next p (P Q R R' : ltl_pred) : *)
  (*   IntoNext P Q → *)
  (*   IntoEventually R R' → *)
  (*   @ElimModal ltlI True%type p p (P)%trace Q R (◊ R'). *)
  (* Proof. Admitted. *)

  (* (* TODO: This is unsound, as it does not clean up the context *) *)
  (* Global Instance elim_modal_eventually p (P Q R : ltl_pred) : *)
  (*   IntoEventually P Q → *)
  (*   @ElimModal ltlI True%type p p (P)%trace Q (◊ R) (◊ R). *)
  (* Proof. Admitted. *)

  (* TODO: This is unsound, as it does not clean up the context *)
  (* Global Instance elim_modal_eventually p (P Q : ltl_pred) : *)
  (*   @ElimModal ltlI True%type p p (◊ P)%trace P (◊ Q) (◊ Q). *)
  (* Proof. Admitted. *)

  Global Instance from_modal_eventually (P : ltl_pred) :
    @FromModal ltlI ltlI _ True%type modality_id (◊ P)%trace (◊ P)%trace (P)%trace.
  Proof. Admitted.

  (* TODO: This is unsound, as it does not clean up the context *)
  (* ALSO: We need to prove that R' can revert back to R *)
  (* Global Instance elim_modal_next p (P Q R R' : ltl_pred) : *)
  (*   IntoNext P Q → IntoNext R R' → *)
  (*   @ElimModal ltlI True%type p p (P)%trace Q R R'. *)
  (* Proof. Admitted. *)

  (* Instance into_later_eventually (n:nat) (P Q : ltl_pred) : *)
  (*   IntoLaterN false n P Q → *)
  (*   IntoLaterN false n (◊P) (◊Q). *)
  (* Proof. Admitted. *)

  Lemma test (P Q : ltl_pred) :
    (P ⊢ ◊ Q) → (◊ P ⊢ ◊ Q).
  Proof. Admitted.

  Lemma test' (P Q : ltl_pred) :
    (◊ P ⊢ ◊ Q).
  Proof.
    iIntros "HP".
    iApply (test with "HP").
    

  Lemma bar (P Q : ltl_pred) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    iIntros (HPQ) "HP".
    rewrite HPQ.
    iAssert (□ ◊ (P ∧ Q))%trace with "[-]" as "[_ H2]"; [|done].
    iApply (trace_always_intro with "HP").
    { iIntros "HP". iMod (HPQ with "HP") as "HPQ".
      iApply trace_eventually_next'. by iModIntro. }
    iIntros "HPQ". iMod "HPQ" as "[HP _]".
    iDestruct (HPQ with "HP") as "HPQ". 
    iMod "HPQ". by iModIntro.
  Qed.

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
