From iris.bi Require Import fixpoint_mono.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export proofmode.

Delimit Scope trace_scope with trace.

CoInductive trace_aux (S L : Type) :=
| tr_singl (s: S)
| tr_cons (s: S) (ℓ: L) (r: trace_aux S L).

Definition trace (S L : Type) := option $ trace_aux S L.

Arguments tr_singl {_} {_} _.
Arguments tr_cons {_} {_} _ _ _.

Bind Scope trace_scope with trace.

Arguments tr_singl {_} {_} _.
Arguments tr_cons {_} {_} _ _ _%trace.
Notation "⟨ ⟩" := (None) : trace_scope.
Notation "⟨ s ⟩" := (Some (tr_singl s)) : trace_scope.
Notation "s -[ ℓ ]->  r" := (Some (tr_cons s ℓ r)) (at level 33) : trace_scope.
Open Scope trace.

Section well_formed.
  Context {S L : Type}.
  Context (R : S → L → S → Prop).

  Definition head_trace (tr : trace S L) : option S :=
    match tr with
    | Some (tr_singl s) => Some s
    | Some (tr_cons s ℓ r) => Some s
    | None => None
    end.

  CoInductive trace_maximal : trace S L → SProp :=
  | trace_maximal_empty : trace_maximal None
  | trace_maximal_singleton c :
    (∀ oζ c', ¬ R c oζ c') → trace_maximal (Some $ tr_singl c)
  | trace_maximal_cons c oζ tr c' :
    head_trace (Some tr) = Some c' →
    R c oζ c' →
    trace_maximal (Some tr) →
    trace_maximal (Some $ tr_cons c oζ tr).

End well_formed.

Record wf_trace S L R := Trace {
  tr_car : trace S L;
  tr_wf : trace_maximal R tr_car;
}.

Arguments Trace {_ _ _} _ _.
Arguments tr_car {_ _ _} _.
Arguments tr_wf {_ _ _} _.
Arguments trace_maximal_empty {_ _ _}.
Arguments trace_maximal_singleton {_ _ _} _ _.

Notation "tr @ tr_wf" := (Trace tr tr_wf) (at level 100).

Section trace.
  Context {St L: Type}.

  Fixpoint after (n: nat) (t: trace St L) : (trace St L):=
    match n with
    | 0 => t
    | Datatypes.S n =>
        match t with
        | ⟨ ⟩ => ⟨ ⟩
        | ⟨ s ⟩ => ⟨ ⟩
        | (s -[ ℓ ]-> xs) => after n (Some xs)
        end
    end.  

End trace.

Definition tProp S L R := wf_trace S L R → Prop.

Bind Scope bi_scope with tProp.
Bind Scope bi_scope with trace.

Section cofe.
  Context {S L : Type}.
  Context {R : S → L → S → Prop}.
  Notation tProp := (@tProp S L R).

  Inductive tProp_equiv' (P Q : tProp) : Prop :=
    { tProp_in_equiv : ∀ tr, P tr ↔ Q tr }.
  Local Instance tProp_equiv : Equiv tProp := tProp_equiv'.
  Local Instance heapProp_equivalence : Equivalence (≡@{tProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure tPropO := discreteO tProp.
End cofe.

Section ltl_constructors.
  Context {S L : Type}.
  Context {R : S → L → S → Prop}.
  Notation tProp := (tProp S L R).
  Implicit Type P Q : tProp.

  Inductive ltl_entails (P Q : tProp) : Prop :=
    { ltl_in_entails : ∀ tr, P tr → Q tr }.

  (* Primitive operators *)
  Definition ltl_pure_def (P : Prop) : tProp :=
    λ tr, P.
  Definition ltl_pure_aux : seal (@ltl_pure_def).
  Proof. by eexists. Qed.
  Definition ltl_pure := unseal ltl_pure_aux.
  Definition ltl_pure_unseal :
    @ltl_pure = @ltl_pure_def := seal_eq ltl_pure_aux.

  Definition ltl_or_def (P Q : tProp) : tProp :=
    λ tr, P tr ∨ Q tr.
  Definition ltl_or_aux : seal (@ltl_or_def).
  Proof. by eexists. Qed.
  Definition ltl_or := unseal ltl_or_aux.
  Definition ltl_or_unseal :
    @ltl_or = @ltl_or_def := seal_eq ltl_or_aux.

  Definition ltl_and_def (P Q : tProp) : tProp :=
    λ tr, P tr ∧ Q tr.
  Definition ltl_and_aux : seal (@ltl_and_def).
  Proof. by eexists. Qed.
  Definition ltl_and := unseal ltl_and_aux.
  Definition ltl_and_unseal :
    @ltl_and = @ltl_and_def := seal_eq ltl_and_aux.

  Definition ltl_impl_def (P Q : tProp) : tProp :=
    λ tr, P tr → Q tr.
  Definition ltl_impl_aux : seal (@ltl_impl_def).
  Proof. by eexists. Qed.
  Definition ltl_impl := unseal ltl_impl_aux.
  Definition ltl_impl_unseal :
    @ltl_impl = @ltl_impl_def := seal_eq ltl_impl_aux.

  Definition ltl_forall_def {A} (Ψ : A → tProp) : tProp :=
    λ tr, ∀ (x:A), Ψ x tr.
  Definition ltl_forall_aux : seal (@ltl_forall_def).
  Proof. by eexists. Qed.
  Definition ltl_forall {A} := unseal ltl_forall_aux A.
  Definition ltl_forall_unseal :
    @ltl_forall = @ltl_forall_def := seal_eq ltl_forall_aux.

  Definition ltl_exist_def {A} (Ψ : A → tProp) : tProp :=
    λ tr, ∃ (x:A), Ψ x tr.
  Definition ltl_exist_aux : seal (@ltl_exist_def).
  Proof. by eexists. Qed.
  Definition ltl_exist {A} := unseal ltl_exist_aux A.
  Definition ltl_exist_unseal :
    @ltl_exist = @ltl_exist_def := seal_eq ltl_exist_aux.

  Definition ltl_later_def (P : tProp) : tProp := P.
  Definition ltl_later_aux : seal (@ltl_later_def).
  Proof. by eexists. Qed.
  Definition ltl_later := unseal ltl_later_aux.
  Definition ltl_later_unseal :
    @ltl_later = @ltl_later_def := seal_eq ltl_later_aux.

  Definition ltl_internal_eq_def {A:ofe} (a1 a2 : A) : tProp :=
    λ tr, a1 ≡ a2.
  Definition ltl_internal_eq_aux : seal (@ltl_internal_eq_def).
  Proof. by eexists. Qed.
  Definition ltl_internal_eq {A} := unseal ltl_internal_eq_aux A.
  Definition ltl_internal_eq_unseal :
    @ltl_internal_eq = @ltl_internal_eq_def := seal_eq ltl_internal_eq_aux.

End ltl_constructors.

Module ltl_primitive.

Section primitive.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).
  Implicit Type P Q : tProp.

  Definition ltl_unseal :=
    (@ltl_pure_unseal S L Rel, @ltl_and_unseal S L Rel, @ltl_or_unseal S L Rel,
       @ltl_impl_unseal S L Rel, @ltl_forall_unseal S L Rel, @ltl_exist_unseal S L Rel,
         @ltl_later_unseal S L Rel, @ltl_internal_eq_unseal S L Rel).

  Ltac unseal := rewrite !ltl_unseal /=.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (ltl_entails P Q).
  Notation "'True'" := (ltl_pure True) : bi_scope.
  Notation "'False'" := (ltl_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (ltl_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := ltl_and : bi_scope.
  Infix "∨" := ltl_or : bi_scope.
  Infix "→" := ltl_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (ltl_forall (λ x, .. (ltl_forall (λ y, P%I)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (ltl_exist (λ x, .. (ltl_exist (λ y, P%I)) ..)) : bi_scope.
  Notation "▷ P" := (ltl_later P) : bi_scope.
  Notation "x ≡ y" := (ltl_internal_eq x y) : bi_scope.

  (** Below there follow the primitive laws for [ltl]. There are no derived laws
  in this file. *)

  (** Entailment *)
  Lemma entails_po : PreOrder (@ltl_entails S L Rel).
  Proof.
    split.
    - intros P; by split=> i.
    - intros P Q Q' HP HQ.
      split=> ? ?. by apply HQ, HP.
  Qed.
  Lemma entails_anti_symm : AntiSymm (≡) (@ltl_entails S L Rel).
  Proof. intros P Q HPQ HQP; split=> n. by split; [apply HPQ|apply HQP]. Qed.
  Lemma equiv_entails (P Q : tProp) : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros HPQ; split; split=> i; apply HPQ.
    - intros [??]. by apply entails_anti_symm.
  Qed.

  (** Non-expansiveness and setoid morphisms *)
  Lemma pure_ne n : Proper (iff ==> dist n) (@ltl_pure S L Rel).
  Proof. intros φ1 φ2 Hφ. by unseal. Qed.
  Lemma and_ne : NonExpansive2 (@ltl_and S L Rel).
  Proof.
    intros n P P' HP Q Q' HQ; unseal; split=> ?.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  Qed.
  Lemma or_ne : NonExpansive2 (@ltl_or S L Rel).
  Proof.
    intros n P P' HP Q Q' HQ; split=> ?.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  Qed.
  Lemma impl_ne : NonExpansive2 (@ltl_impl S L Rel).
  Proof.
    intros n P P' HP Q Q' HQ; split=> ?.
    unseal; split; intros HPQ ?; apply HQ, HPQ, HP; auto with lia.
  Qed.
  Lemma forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@ltl_forall S L Rel A).
  Proof.
     by intros Ψ1 Ψ2 HΨ; unseal; split=> x; split; intros HP a; apply HΨ.
  Qed.
  Lemma exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@ltl_exist S L Rel A).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    unseal; split=> ?; split; intros [a ?]; exists a; by apply HΨ.
  Qed.
  Lemma later_ne : NonExpansive (@ltl_later S L Rel).
  Proof. unseal; intros n P Q HPQ. rewrite /ltl_later_def. done. Qed.

  (** Introduction and elimination rules *)
  Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
  Proof. intros ?. unseal; by split. Qed.
  Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
  Proof. unseal=> HP; split=> n ?. by apply HP. Qed.
  (* Lemma test {A} (φ : A → tProp S L Rel) : ⊢ (∀ a, φ a)%ltl. *)
  Lemma pure_forall_2 {A} (φ : A → Prop) :
    ((∀ a, ⌜ φ a ⌝):tProp) ⊢ ⌜ ∀ a, φ a ⌝.
  Proof. by unseal. Qed.

  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof. unseal; by split=> n [??]. Qed.
  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof. unseal; by split=> n [??]. Qed.
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof.
    intros HQ HR; unseal; split=> n ?.
    split.
    - by apply HQ.
    - by apply HR.
  Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof. unseal; split=> n ?; left; auto. Qed.
  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof. unseal; split=> n ?; right; auto. Qed.
  Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof.
    intros HP HQ. unseal; split=> n [?|?].
    - by apply HP.
    - by apply HQ.
  Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof.
    unseal=> HQ; split=> ???.
    apply HQ. by split.
  Qed.
  Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof. unseal=> HP; split=> tr [??]. by apply HP. Qed.

  Lemma forall_intro {A} P (Ψ : A → tProp) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n ? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → tProp} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → tProp} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> n ?; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → tProp) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΨ; split=> n [a ?]; by apply HΨ with a. Qed.

  (** Later *)
  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof. unseal=> HP; split=>tr. rewrite /ltl_later_def.
         destruct HP as [HP]. apply HP. Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof. unseal; split=> /= HP. done. Qed.

  Lemma later_forall_2 {A} (Φ : A → tProp) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; by split. Qed.
  Lemma later_exist_false {A} (Φ : A → tProp) :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
  Proof. unseal; split=> tr /=; eauto. rewrite /ltl_later_def.
         intros [a Ha]. right. exists a. done.
  Qed.
  Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
  Proof.
    unseal; split=> tr /= HP. rewrite /ltl_later_def.
    right. intros _. done.
  Qed.

  (** Equality *)
  Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ (a ≡ a).
  Proof. unseal; split=> n ? /=. rewrite /ltl_internal_eq_def. done. Qed.
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → tProp) :
    NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
  Proof.
    intros Hnonexp. unseal; split=> tr Hab HΨ.
    rewrite /ltl_internal_eq_def in Hab.
    eapply Hnonexp; [|done].
    rewrite Hab. done. Unshelve. apply 0.
  Qed.

End primitive.
End ltl_primitive.

Import ltl_primitive.

Section ltl_always.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  CoInductive ltl_always_def (P : tProp) : tProp :=
  | ltl_always_def_empty H1 H2 : P (⟨⟩ @ H1) → ltl_always_def P (⟨⟩ @ H2)
  | ltl_always_def_singl s H1 H2 H3 : P (Trace ⟨ s ⟩ H1) → P (⟨⟩ @ H2) → ltl_always_def P (⟨s⟩ @ H3)
  | ltl_always_def_cons s l tr H1 H2 H3 : P (s -[l]-> tr @ H1) → ltl_always_def P (Some tr @ H2) → ltl_always_def P (s -[l]-> tr @ H3).
  Definition ltl_always_aux : seal (@ltl_always_def).
  Proof. by eexists. Qed.
  Definition ltl_always := unseal ltl_always_aux.
  Definition ltl_always_unseal :
    @ltl_always = @ltl_always_def := seal_eq ltl_always_aux.

End ltl_always.

Section ltl.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_emp : tProp := ltl_pure True.
  Definition ltl_persistently (P : tProp) : tProp := ltl_always P.
  Definition ltl_plainly (P : tProp) : tProp := P.

  Local Existing Instance entails_po.

  Lemma ltl_bi_mixin :
    BiMixin
      ltl_entails ltl_emp ltl_pure ltl_and ltl_or ltl_impl
      (@ltl_forall S L Rel) (@ltl_exist S L Rel) ltl_and ltl_impl.
  Proof.
    split.
    - exact: entails_po.
    - exact: equiv_entails.
    - exact: pure_ne.
    - exact: and_ne.
    - exact: or_ne.
    - exact: impl_ne.
    - exact: forall_ne.
    - exact: exist_ne.
    - exact: and_ne.
    - exact: impl_ne.
    - exact: pure_intro.
    - exact: pure_elim'.
    - exact: and_elim_l.
    - exact: and_elim_r.
    - exact: and_intro.
    - exact: or_intro_l.
    - exact: or_intro_r.
    - exact: or_elim.
    - exact: impl_intro_r.
    - exact: impl_elim_l'.
    - exact: @forall_intro.
    - exact: @forall_elim.
    - exact: @exist_intro.
    - exact: @exist_elim.
    - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
      intros P P' Q Q' H1 H2. apply and_intro.
      + by etrans; first apply and_elim_l.
      + by etrans; first apply and_elim_r.
    - (* P ⊢ emp ∗ P *)
      intros P. apply and_intro; last done. by apply pure_intro.
    - (* emp ∗ P ⊢ P *)
      intros P. apply and_elim_r.
    - (* P ∗ Q ⊢ Q ∗ P *)
      intros P Q. apply and_intro; [ apply and_elim_r | apply and_elim_l ].
    - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
      intros P Q R. repeat apply and_intro.
      + etrans; first apply and_elim_l. by apply and_elim_l.
      + etrans; first apply and_elim_l. by apply and_elim_r.
      + apply and_elim_r.
    - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
      apply impl_intro_r.
    - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
      apply impl_elim_l'.
  Qed.

  Instance ne_proper (f : tProp → tProp) `{!Proper ((≡) ==> (≡)) f} : NonExpansive f.
  Proof.
    constructor. intros.
    apply Proper0. done.
  Qed.

  Lemma ltl_bi_persistently_mixin :
    BiPersistentlyMixin
      ltl_entails ltl_emp ltl_and
      (@ltl_exist S L Rel) ltl_and ltl_persistently.
  Proof.
    split.
    - apply ne_proper. rewrite /ltl_persistently ltl_always_unseal.
      constructor.
      intros.
      constructor.
      + intros.
        revert H tr H0.
        cofix IH.
        intros Heq tr Htr.
        inversion Htr; simplify_eq.
        { econstructor. apply Heq. done. }
        { econstructor; apply Heq; done. }
        econstructor.
        * apply Heq; done.
        * apply IH; done.
      + intros.
        revert H tr H0.
        cofix IH.
        intros Heq tr Htr.
        inversion Htr; simplify_eq.
        { econstructor. apply Heq. done. }
        { econstructor; apply Heq; done. }
        econstructor.
        * apply Heq; done.
        * apply IH; done.
    - (* (P ⊢ Q) → <pers> P ⊢ <pers> Q *)
      rewrite /ltl_persistently ltl_always_unseal.
      intros. constructor. intros.
      rewrite /ltl_persistently. intros.
      revert tr H0.
      cofix IH.
      intros tr Htr.
      inversion Htr; simplify_eq.
      { econstructor. by apply H. }
      + econstructor.
        * by apply H.
        * by apply H.
      + econstructor.
        * by apply H.
        * by apply IH.  
    - (* <pers> P ⊢ <pers> <pers> P *)
      intros. constructor. rewrite /ltl_persistently ltl_always_unseal.
      cofix IH.
      intros tr Htr.
      inversion Htr; simplify_eq.
      + econstructor. done.
      + econstructor.
        * done.
        * econstructor. done.
      + econstructor.
        * done.
        * apply IH. done. 
    - (* emp ⊢ <pers> emp *)
      rewrite /ltl_persistently ltl_always_unseal. econstructor. intros.
      revert tr H.
      cofix IH.
      intros tr Htr.
      destruct tr as [[[]|] ?].
      { econstructor. done. simpl. rewrite /ltl_emp. simpl. rewrite ltl_pure_unseal. done. }
      + econstructor. done. apply IH. rewrite /ltl_emp ltl_pure_unseal. done.
      + econstructor. done.
    - (* (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a) *)
      intros.
      rewrite /ltl_persistently ltl_always_unseal. econstructor. intros.
      revert tr H.
      cofix IH.
      intros tr Htr.
      rewrite ltl_and_unseal in Htr. inversion Htr.
      inversion H; simplify_eq.
      { inversion H0; simplify_eq. econstructor. rewrite ltl_and_unseal. split; done. }
      { inversion H0; simplify_eq. econstructor; rewrite ltl_and_unseal; split; done. }
      inversion H0; simplify_eq. econstructor.
      + rewrite ltl_and_unseal. done.
      + apply IH. rewrite ltl_and_unseal. split; done.
    - (* <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a) *)      
      admit.
    - (* <pers> P ∗ Q ⊢ <pers> P *)
      intros.
      constructor. intros. rewrite ltl_and_unseal in H.
      destruct H. done.
    - (* <pers> P ∧ Q ⊢ P ∗ Q *)
      intros. constructor. intros. rewrite ltl_and_unseal in H. destruct H.
      rewrite ltl_and_unseal. split.
      + rewrite /ltl_persistently ltl_always_unseal in H. by inversion H.
      + done.
  Admitted.

  Lemma ltl_bi_later_mixin :
    BiLaterMixin
      ltl_entails ltl_pure ltl_or ltl_impl
      (@ltl_forall S L Rel) (@ltl_exist S L Rel) ltl_and ltl_persistently ltl_later.
  Proof.
    split.
    - exact: later_ne.
    - exact: later_mono.
    - exact: later_intro.
    - exact: @later_forall_2.
    - exact: @later_exist_false.
    - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *)
      intros P Q.
      apply and_intro; apply later_mono.
      + apply and_elim_l.
      + apply and_elim_r.
    - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *)
      intros P Q.
      trans (ltl_forall (λ b : bool, ltl_later (if b then P else Q))).
      { apply forall_intro=>[[]].
        - apply and_elim_l.
        - apply and_elim_r. }
      etrans; [apply later_forall_2|apply later_mono].
      apply and_intro.
      + refine (forall_elim true).
      + refine (forall_elim false).
    - (* ▷ <pers> P ⊢ <pers> ▷ P *)
      rewrite ltl_later_unseal /ltl_later_def. done.
    - (* <pers> ▷ P ⊢ ▷ <pers> P *)
      rewrite ltl_later_unseal /ltl_later_def. done.
    - (* <pers> ▷ P ⊢ ▷ <pers> P *)
      rewrite ltl_later_unseal /ltl_later_def.
      intros P. constructor. intros.
      rewrite ltl_or_unseal. right. rewrite ltl_impl_unseal. intros HP. done.
  Qed.

End ltl.

Canonical Structure ltlI {S L : Type} {Rel} : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (tProp S L Rel);
    bi_bi_mixin := ltl_bi_mixin;
    bi_bi_persistently_mixin := ltl_bi_persistently_mixin;
    bi_bi_later_mixin := ltl_bi_later_mixin |}.

Section ltl.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Global Instance ltl_pure_forall : BiPureForall (@ltlI S L Rel).
  Proof. exact: @pure_forall_2. Qed.

  Global Instance ltl_affine : BiAffine (@ltlI S L Rel) | 0.
  Proof. intros P. exact: pure_intro. Qed.
  (* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)

End ltl.

Global Hint Immediate ltl_affine : core.

(* OBS: This seems to be needed to avoid collision with FromImpl *)
Global Remove Hints class_instances.from_impl_impl : typeclass_instances.

(** extra BI instances *)

(** Re-state/export soundness lemmas *)

Module tProp.
Section restate.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  (** We restate the unsealing lemmas so that they also unfold the BI layer. The *)
(*   sealing lemmas are partially applied so that they also work under binders. *)
  Local Lemma ltl_emp_unseal : bi_emp = @ltl_pure_def S L Rel True.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Local Lemma ltl_pure_unseal : bi_pure = @ltl_pure_def S L Rel.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Local Lemma ltl_and_unseal : bi_and = @ltl_and_def S L Rel.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Local Lemma ltl_or_unseal : bi_or = @ltl_or_def S L Rel.
  Proof. by rewrite -ltl_or_unseal. Qed.
  Local Lemma ltl_impl_unseal : bi_impl = @ltl_impl_def S L Rel.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Local Lemma ltl_forall_unseal : @bi_forall _ = @ltl_forall_def S L Rel.
  Proof. by rewrite -ltl_forall_unseal. Qed.
  Local Lemma ltl_exist_unseal : @bi_exist _ = @ltl_exist_def S L Rel.
  Proof. by rewrite -ltl_exist_unseal. Qed.
  Local Lemma ltl_sep_unseal : bi_sep = @ltl_and_def S L Rel.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Local Lemma ltl_wand_unseal : bi_wand = @ltl_impl_def S L Rel.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Local Lemma ltl_persistently_unseal : bi_persistently = @ltl_persistently S L Rel.
  Proof. done. Qed.
  Local Lemma ltl_later_unseal : bi_later = @ltl_later_def S L Rel.
  Proof. by rewrite -ltl_later_unseal. Qed.

  Definition ltl_unseal :=
    (ltl_emp_unseal, ltl_pure_unseal, ltl_and_unseal, ltl_or_unseal,
    ltl_impl_unseal, ltl_forall_unseal, ltl_exist_unseal,
    ltl_sep_unseal, ltl_wand_unseal,
    ltl_persistently_unseal, ltl_later_unseal).
End restate.

(** The final unseal tactic that also unfolds the BI layer. *)
Ltac unseal := rewrite !ltl_unseal /=.
End tProp.

Section ltl_primitives.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (* LTL Operators *)
  (* Primitive operators *)
  Inductive ltl_now_def (P : option (S * option L) → Prop) : tProp :=
  | ltl_now_empty H : P None → ltl_now_def P (⟨⟩ @ H)
  | ltl_now_single s H : P (Some (s, None)) → ltl_now_def P (⟨s⟩ @ H)
  | ltl_now_cons s l tr H : P (Some (s,Some l)) → ltl_now_def P ((s -[ l ]-> tr) @ H).
  Definition ltl_now_aux : seal (@ltl_now_def).
  Proof. by eexists. Qed.
  Definition ltl_now := unseal ltl_now_aux.
  Definition ltl_now_unseal :
    @ltl_now = @ltl_now_def := seal_eq ltl_now_aux.

  Inductive ltl_next_def (P : tProp) : tProp :=
  | ltl_next_empty H1 H2 : P (⟨⟩ @ H1) -> ltl_next_def P (⟨⟩ @ H2)
  | ltl_next_single s H1 H2 : P (⟨⟩ @ H1) -> ltl_next_def P (⟨s⟩ @ H2)
  | ltl_next_cons s l tr H1 H2 : P (Trace (Some tr) H1) → ltl_next_def P ((s -[ l ]-> tr) @ H2).
  Definition ltl_next_aux : seal (@ltl_next_def).
  Proof. by eexists. Qed.
  Definition ltl_next := unseal ltl_next_aux.
  Definition ltl_next_unseal :
    @ltl_next = @ltl_next_def := seal_eq ltl_next_aux.

  Inductive ltl_until_def (P Q : tProp) : tProp :=
  | ltl_until_here tr H1 H2 : Q (tr @ H1) -> ltl_until_def P Q (tr @ H2)
  | ltl_until_single s H1 H2 H3 : P (⟨s⟩ @ H1) → Q (Trace ⟨⟩ H2) → ltl_until_def P Q (⟨s⟩ @ H3)
  | ltl_until_cons s l tr H1 H2 H3 : P (Trace (s -[l]-> tr) H1) → ltl_until_def P Q ((Some tr) @ H2) → ltl_until_def P Q ((s -[l]-> tr) @ H3).
  Definition ltl_until_aux : seal (@ltl_until_def).
  Proof. by eexists. Qed.
  Definition ltl_until := unseal ltl_until_aux.
  Definition ltl_until_unseal :
    @ltl_until = @ltl_until_def := seal_eq ltl_until_aux.

  Notation ltl_eventually P := (ltl_until True P).

End ltl_primitives.

Global Instance: Params (@ltl_now) 2 := {}.
Global Instance: Params (@ltl_next) 2 := {}.
Global Instance: Params (@ltl_until) 2 := {}.
Global Instance: Params (@ltl_always) 2 := {}.

Notation "○ P" := (ltl_next P%I) (at level 20, right associativity) : bi_scope.
Notation "◊ P" := (ltl_until True P%I) (at level 20, right associativity) : bi_scope.
Notation "P ∪ Q" := (ltl_until P Q%I) : bi_scope.
Notation "↓ P" := (ltl_now P) (at level 20, right associativity) : bi_scope.

Section ltl_lemmas.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_unseal' :=
    (@ltl_pure_unseal S L, @ltl_and_unseal S L, @ltl_or_unseal S L,
       @ltl_impl_unseal S L, @ltl_forall_unseal S L, @ltl_exist_unseal S L,
         @ltl_later_unseal S L, @ltl_internal_eq_unseal S L,
    @ltl_next_unseal S L, @ltl_now_unseal S L, @ltl_always_unseal S L,
    @ltl_until_unseal S L).

  Ltac ltl_unseal := rewrite !ltl_unseal' /=.

  Import tProp.

  Lemma bi_intuitionistically_unseal (P : tProp) :
    @bi_intuitionistically (@ltlI S L Rel) P ≡ ltl_always P.
  Proof. rewrite /bi_intuitionistically.
         rewrite /bi_affinely.
         rewrite left_id. done.
  Qed.

  Lemma bi_intuitionistically_unseal' (P : tProp) tr :
    @bi_intuitionistically (@ltlI S L Rel) P tr ≡ ltl_always P tr.
  Proof. 
    rewrite /bi_intuitionistically.
    rewrite /bi_affinely.
    unseal. simpl. rewrite /ltl_and_def /ltl_pure_def. simpl.
    rewrite left_id. done.
  Qed.

  Tactic Notation "unseal_apply" constr(pat) :=
    let H := fresh in
    pose proof pat as H;
    revert H; ltl_unseal; intros H; apply H; clear H.

  Tactic Notation "unseal_eapply" constr(pat) :=
    let H := fresh in
    pose proof pat as H;
    revert H; ltl_unseal; intros H; eapply H; clear H.

  (** AXIOMS *)

  (** ltl_not lemmas *)

  Lemma excl_false (P : tProp) :
    P ∧ ¬ P ⊢ False.
  Proof.
    constructor. unseal.
    intros tr [H1 H2].
    by apply H2.
  Qed.

  Lemma ltl_not_not (P :tProp) :
    P ⊢ ¬ ¬ P.
  Proof.
    constructor.
    intros tr HP.
    unseal.
    intros H1. apply H1. done.
  Qed.

  Lemma impl_intro_l (P Q : tProp) :
    (⊢ P → Q) → (P ⊢ Q).
  Proof. iIntros (HPQ) "HP". by iApply HPQ. Qed.

  Lemma impl_intro_r (P Q : tProp) :
    (P ⊢ Q) → (⊢ P → Q).
  Proof. iIntros (HPQ) "HP". by rewrite HPQ. Qed.

  (** ltl_next lemmas *)

  (* N○ *)
  Lemma ltl_next_taut (P : tProp) :
    (⊢ P) → (⊢ ○ P).
  Proof.
    intros [HP].
    constructor.
    intros tr _.
    ltl_unseal. destruct tr as [[[]|]].
    - econstructor 2. apply HP. unseal. done. Unshelve. apply trace_maximal_empty.
    - econstructor 3. apply HP. unseal. done. Unshelve. inversion tr_wf0. done.
    - econstructor 1. apply HP. unseal. done. Unshelve. done.
  Qed.

  (* A3 *)
  Lemma ltl_next_mono_strong (P Q : tProp) :
    ○ (P → Q) ⊢ ○ P → ○ Q.
  Proof.
    constructor. ltl_unseal. unseal.
    intros tr HPQ HP.
    inversion HP; inversion HPQ; simplify_eq; econstructor; naive_solver.
  Qed.

  Lemma ltl_next_or_r (P Q : tProp) :
    ○ (P ∨ Q) ⊢ (○ P) ∨ (○ Q).
  Proof.
    ltl_unseal. unseal. constructor.
    intros tr. inversion 1; simplify_eq.
    + inversion H0; simplify_eq; [left|right]; by econstructor.
    + inversion H0; simplify_eq; [left|right]; by econstructor.
    + inversion H0; simplify_eq; [left|right]; by econstructor.
  Qed.

  (** ltl_until lemmas *)

  Lemma ltl_until_intro (P Q : tProp) :
    Q ∨ P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof.
    ltl_unseal. unseal. constructor.
    intros [tr tr_wf] [HQ|[HP HPQ]].
    { by econstructor 1. }
    destruct tr.
    { revert HPQ. inversion 1.
      - simplify_eq. inversion H0. by econstructor 2.
      - simplify_eq. by econstructor 3. }
    revert HPQ. inversion 1. done.
  Qed.

  Lemma ltl_until_ind (P Q R : tProp) :
    (Q ⊢ R) →
    (○ (ltl_until P Q) ∧ ○ R ∧ P ⊢ R) →
    P ∪ Q ⊢ R.
  Proof.
    constructor.
    intros tr H'.
    rewrite ltl_until_unseal in H'. induction H'.
    { by apply H. }
    { apply H0.
      unseal.
      repeat split.
      - ltl_unseal. econstructor. econstructor. done. Unshelve. done.
      - ltl_unseal. econstructor. apply H. done.
      - done. }
    apply H0.
    unseal.
    repeat split.
    - ltl_unseal. econstructor. done.
    - ltl_unseal. econstructor. done.
    - done.
  Qed.

  Lemma ltl_until_mono (P1 P2 Q1 Q2 : tProp) :
    (P1 ⊢ P2) → (Q1 ⊢ Q2) → (P1 ∪ Q1) ⊢ (P2 ∪ Q2).
  Proof.
    intros HP HQ. constructor. intros tr.
    ltl_unseal. intros HPQ. induction HPQ.
    { econstructor. by apply HQ. } 
    { econstructor 2.
      + apply HP. done.
      + apply HQ. done. }
    econstructor 3.
    + by apply HP. 
    + done.
  Qed.

  Lemma ltl_until_idemp (P Q : tProp) :
    (P ∪ (P ∪ Q)) ⊣⊢ (P ∪ Q).
  Proof.
    constructor.
    split.
    - ltl_unseal. intros Htr. induction Htr; [done| |].
      + inversion H0. by econstructor 2.
      + by econstructor 3.
    - ltl_unseal.
      intros HPQ.
      destruct tr.
      econstructor 1. done.
  Qed.

  (** ltl_eventually lemmas *)

  Lemma ltl_until_and (P Q1 Q2 : tProp) :
    (P ∪ (Q1 ∧ Q2)) ⊢ (P ∪ Q1) ∧ (P ∪ Q2).
  Proof.
    ltl_unseal.
    constructor. unseal.
    intros [tr tr_wf] Hconj.
    induction Hconj.
    { destruct H as [? ?].
      split; by econstructor. }
    { destruct H0 as [? ?]. split; by econstructor 2. }
    destruct IHHconj as [??].
    split.
    - by econstructor 3.
    - by econstructor 3.
  Qed.

  Lemma ltl_until_next_comm (P Q : tProp) :
    (○ P ∪ ○ Q) ⊣⊢ ○ (P ∪ Q).
  Proof.
    constructor.
    intros tr.
    split.
    - ltl_unseal.
      intros HP.
      induction HP.
      { inversion H; simplify_eq; econstructor; econstructor; done. }
      { inversion H0; simplify_eq. econstructor. econstructor. done. }
      destruct tr as [].
      + inversion IHHP; simplify_eq. subst. inversion H. subst. inversion H6; simplify_eq. econstructor. econstructor 2; [done|].
        done.
      + inversion IHHP. subst. inversion H. subst. econstructor 3. econstructor 3; done.
    - ltl_unseal.
      intros HP.
      induction HP.
      + inversion H. econstructor. econstructor. done.
      + inversion H. econstructor. econstructor. done.
      + assert (∃ tr', tr' = {| tr_car := Some tr; tr_wf := H1 |}) as [tr' Heq] by eauto.
        rewrite -Heq in H.
        revert tr s l H1 H2 Heq.
        induction H; intros tr'' s' l' ?? Heq.
        * simplify_eq. econstructor. econstructor. done.
        * simplify_eq. econstructor 3; [by econstructor|]. econstructor. by econstructor.
        * simplify_eq. econstructor 3; [by econstructor|]. by eapply IHltl_until_def.
    Unshelve.
    all: eauto.
  Qed.

  (** Misc *)

  (** ltl_always lemmas *)

  Lemma ltl_always_intro (P : tProp) :
    □(P → ○ P) ⊢ P → □P.
  Proof.
    rewrite !bi_intuitionistically_unseal.
    constructor. ltl_unseal. unseal.
    cofix IH.
    intros tr Htr.
    inversion Htr; simplify_eq.
    - intros HP. econstructor. done.
    - intros HP. pose proof (HP) as HP'. apply H in HP'. inversion HP'. by econstructor.
    - intros HP. econstructor; [done|].
      + apply H in HP. inversion HP. apply IH.
        * done.
        * done.
  Qed.

  Lemma ltl_always_next (P : tProp) :
    □ P ⊢ ○ □ P.
  Proof.
    constructor. ltl_unseal. intros tr Halways.
    rewrite bi_intuitionistically_unseal' ltl_always_unseal in Halways.
    destruct tr as [[[]|]]; inversion Halways.
    - econstructor. rewrite bi_intuitionistically_unseal' ltl_always_unseal. econstructor. done.
    - econstructor. rewrite bi_intuitionistically_unseal' ltl_always_unseal.  done.
    - econstructor. rewrite bi_intuitionistically_unseal' ltl_always_unseal.  done.
      Unshelve. done.
  Qed.

  Lemma ltl_always_next_comm (P : tProp) :
    □ ○ P ⊢ ○ □ P.
  Proof.
    constructor. ltl_unseal. intros tr Halways.
    rewrite bi_intuitionistically_unseal' in Halways. rewrite ltl_always_unseal in Halways.
    destruct tr as [[[]|]].
    - econstructor. inversion Halways. inversion H4. inversion H5.
      rewrite bi_intuitionistically_unseal' ltl_always_unseal. econstructor. done.
    - assert (trace_maximal Rel (Some r)) as Hwf.
      { inversion tr_wf0. done. }
      econstructor.
      instantiate (1:=Hwf).
      rewrite bi_intuitionistically_unseal' ltl_always_unseal.
      revert s ℓ r tr_wf0 Halways Hwf. cofix IH.
      intros. destruct r as [].
      { inversion Halways. simplify_eq.
        inversion H9. simplify_eq.
        inversion H4. simplify_eq.
        inversion H12. simplify_eq.
        econstructor.
        - done.
        - done.
      }
      inversion Halways. simplify_eq. inversion H4. simplify_eq.
      econstructor.
      { done. }
      eapply IH.
      done.
    - inversion Halways. inversion H. econstructor. rewrite bi_intuitionistically_unseal' ltl_always_unseal. 
      econstructor. done.
      Unshelve.
      all: eauto.
      { constructor. }
      { inversion Hwf. done. }
  Qed.

  (** LTL Now (TBD) *)

  Lemma ltl_now_false (P Q : option (S* option L) → Prop) :
    (∀ osl, P osl → Q osl → False) → (↓ P:tProp) -∗ ↓ Q -∗ False.
  Proof. unseal. ltl_unseal.
         intros HPQ. constructor.
         intros tr _ HP HQ.
         destruct tr as [[[]|]]; eapply (HPQ); simpl in *.
         - by inversion HP.
         - by inversion HQ.
         - by inversion HP.
         - by inversion HQ.
         - by inversion HP.
         - by inversion HQ.
  Qed.

  Lemma ltl_now_mono P Q :
    (∀ osl, P osl → Q osl) → ↓ P ⊢ (↓ Q):tProp.
  Proof.
    intros HPQ.
    ltl_unseal. constructor.
    intros [[[]|]]; inversion 1; try constructor; by apply HPQ.
  Qed.

  (** LTL Exists (TBD) *)

  Lemma ltl_next_exists {A} (P : A → tProp) :
    (○ ∃ x, P x)%I ⊢ ∃ x, ○ P x.
  Proof.
    unseal. ltl_unseal.
    constructor. intros tr Hnext. inversion Hnext.
    - simplify_eq. destruct H as [a H]. exists a. econstructor. apply H.
    - simplify_eq. destruct H as [a H]. exists a. econstructor. apply H.
    - simplify_eq. destruct H as [a H]. exists a. econstructor. apply H.
  Qed.

  (** DERIVED RULES *)

  Lemma ltl_next_mono (P Q : tProp) :
    (P ⊢ Q) → (○ P ⊢ ○ Q).
  Proof.
    intros HPQ.
    apply impl_intro_l.
    rewrite -ltl_next_mono_strong.
    apply ltl_next_taut.
    apply impl_intro_r.
    apply HPQ.
  Qed.

  Lemma ltl_next_and (P Q : tProp) :
    (○ P) ∧ (○ Q) ⊣⊢ ○ (P ∧ Q).
  Proof.
    apply bi.equiv_entails_2.
    - apply bi.impl_elim_r'.
      rewrite -ltl_next_mono_strong.
      apply ltl_next_mono.
      apply bi.impl_intro_l.
      done.
    - apply bi.and_intro.
      + apply ltl_next_mono. rewrite bi.and_elim_l. done.
      + apply ltl_next_mono. rewrite bi.and_elim_r. done.
  Qed.

  Lemma ltl_next_or (P Q : tProp) :
    (○ P) ∨ (○ Q) ⊣⊢ ○ (P ∨ Q).
  Proof.
    apply bi.equiv_entails_2.
    - apply bi.or_elim.
      + apply ltl_next_mono. apply bi.or_intro_l.
      + apply ltl_next_mono. apply bi.or_intro_r.
    - apply ltl_next_or_r.
  Qed.

  Lemma ltl_until_intro_now (P Q : tProp) :
    Q ⊢ P ∪ Q.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_until_intro_next (P Q : tProp) :
    P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof. rewrite -{2}ltl_until_intro. apply bi.or_intro_r. Qed.

  (* TODO: Is this needed? *)
  Lemma ltl_until_unfold (P Q : tProp) :
    P ∪ Q ⊣⊢ Q ∨ (P ∧ ○ (P ∪ Q)).
  Proof.
    apply bi.equiv_entails_2.
    { apply ltl_until_ind. 
      - apply bi.or_intro_l.
      - iIntros "(H1&_&H2)". iRight. iFrame. }
    iIntros "[HPQ | [HP HPQ]]".
    - iApply ltl_until_intro. by iLeft. 
    - iApply ltl_until_intro. by iRight; iFrame.
  Qed.

  Lemma ltl_eventually_intro (P : tProp) :
    P ∨ ○ ◊ P ⊢ ◊ P.
  Proof.
    rewrite -{2}(ltl_until_intro True P).
    iIntros "[HP|HP]".
    { by iLeft. }
    iRight. by iFrame.
  Qed.

  Lemma ltl_eventually_intro_now (P : tProp) :
    P ⊢ ◊ P.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_eventually_intro_next (P : tProp) :
    (○ P) ⊢ (◊ P).
  Proof. rewrite -ltl_eventually_intro. 
         etrans; [|apply bi.or_intro_r]. apply ltl_next_mono.
         apply ltl_eventually_intro_now.
  Qed.

  Lemma ltl_eventually_mono (P Q : tProp) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof. by apply ltl_until_mono. Qed.

  Lemma ltl_eventually_and (P Q : tProp) :
    (◊ (P ∧ Q)) ⊢ (◊ P) ∧ (◊ Q).
  Proof. by rewrite -ltl_until_and. Qed.

  Lemma ltl_eventually_next_comm (P : tProp) :
    (◊ ○ P) ⊣⊢ (○ ◊ P).
  Proof.
    rewrite -ltl_until_next_comm.
    apply bi.equiv_entails_2.
    - apply ltl_until_mono; [|done]. by apply ltl_next_taut.
    - apply ltl_until_mono; [|done]. eauto.
  Qed.

  Lemma ltl_eventually_idemp (P : tProp) :
    (◊◊P) ⊣⊢ (◊P).
  Proof. apply ltl_until_idemp. Qed.

  Lemma ltl_eventually_next (P : tProp) :
    (◊ ○ P) ⊢ (◊ P).
  Proof.
    rewrite <-(ltl_eventually_idemp P).
    apply ltl_eventually_mono.
    apply ltl_eventually_intro_next.
  Qed.

  Lemma ltl_next_eventually (P : tProp) :
    (○ ◊ P) ⊢ (◊ P).
  Proof. rewrite -{2}ltl_eventually_next ltl_eventually_next_comm. done. Qed.

  Lemma ltl_until_eventually_equiv (P : tProp) :
    (True ∪ P) ⊣⊢ (◊ P).
  Proof. done. Qed.

  Lemma ltl_until_eventually (P Q : tProp) :
    (P ∪ Q) ⊢ (◊ Q).
  Proof. apply ltl_until_mono; by eauto. Qed.

  Lemma ltl_eventually_ind (P Q : tProp) :
    (P ⊢ Q) →
    ((○ ◊ P) ∧ ○ Q ⊢ Q) →
    ◊ P ⊢ Q.
  Proof.
    intros. apply ltl_until_ind; [done|].
    rewrite -{2}H0.
    iIntros "(?&?&?)". iFrame.
  Qed.

  Lemma ltl_next_always_combine (P Q : tProp) :
    (□ P ∧ ○ Q) ⊢ (○ (Q ∧ □ P)).
  Proof.
    rewrite bi.and_comm.
    rewrite {1}ltl_always_next. rewrite ltl_next_and.
    done.
  Qed.

  Lemma ltl_sep_and (P Q : tProp) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. done. Qed.

  (** Proofmode stuff *)

  Lemma bi_sep_and (P Q : tProp) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. constructor. intros tr. unseal. done. Qed.
  Lemma bi_wand_impl (P Q : tProp) :
    (P -∗ Q) ⊣⊢ (P → Q).
  Proof. constructor. intros tr. unseal. done. Qed.

  (* TODO: Move *)
  Global Instance ltl_next_proper : Proper ((≡) ==> (≡)) (@ltl_next S L Rel).
  Proof.
    constructor.
    intros. split.
    - apply ltl_next_mono. rewrite H. done.
    - apply ltl_next_mono. rewrite H. done.
  Qed.

End ltl_lemmas.

Section ltl_proofmode.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Import tProp.

  Global Instance into_wand_next p (P Q R : tProp) :
    IntoWand p p R P Q → IntoWand p p (○ R)%I (○ P)%I (○ Q)%I.
  Proof. Admitted.
  (*   rewrite /IntoWand. *)
  (*   destruct p; simpl; [rewrite !bi_intuitionistically_id|]. *)
  (*   - intros HR. iIntros "HR HP". *)
  (*     iAssert (○ (R ∧ P))%I with "[HR HP]" as "H". *)
  (*     { iApply ltl_next_and. iSplit; iFrame. } *)
  (*     iApply (ltl_next_mono with "H"). *)
  (*     rewrite HR. *)
  (*     iIntros "[HPQ HP]". by iApply "HPQ". *)
  (*   - intros HR. iIntros "HR HP". *)
  (*     iAssert (○ (R ∧ P))%I with "[HR HP]" as "H". *)
  (*     { iApply ltl_next_and. iSplit; iFrame. } *)
  (*     iApply (ltl_next_mono with "H"). *)
  (*     rewrite HR. *)
  (*     iIntros "[HPQ HP]". by iApply "HPQ". *)
  (* Qed. *)

  Global Instance into_and_eventually b (P Q1 Q2 : tProp) :
    IntoAnd b P Q1 Q2 →
    IntoAnd b (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof. Admitted.
  (*   destruct b; simpl. *)
  (*   - rewrite /IntoAnd. simpl. rewrite !bi_intuitionistically_id. *)
  (*     intros HPQ. *)
  (*     rewrite -ltl_eventually_and. *)
  (*     by eapply ltl_eventually_mono. *)
  (*   - rewrite /IntoAnd. simpl. *)
  (*     intros HPQ. *)
  (*     rewrite -ltl_eventually_and. *)
  (*     by eapply ltl_eventually_mono. *)
  (* Qed. *)

  Global Instance into_sep_eventually (P Q1 Q2 : tProp) :
    IntoSep P Q1 Q2 →
    IntoSep (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof.
    rewrite /IntoSep.
    simpl.
    rewrite !bi_sep_and.
    intros HPQ.
    rewrite -ltl_eventually_and.
    by eapply ltl_eventually_mono.
  Qed.

  Class IntoNext  (p:bool) (P Q : tProp) :=
    into_next : □?p P ⊢ ○ Q.
  Global Arguments IntoNext _ _%I _%I : simpl never.
  Global Arguments into_next _ _%I _%I {_}.
  Global Hint Mode IntoNext ! ! - : typeclass_instances.

  Global Instance into_next_next p (P : tProp) :
    IntoNext p (○ P) P.
  Proof.
    rewrite /IntoNext.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Global Instance into_next_and b (P1 P2 Q1 Q2 : tProp) :
    IntoNext b P1 P2 →
    IntoNext b Q1 Q2 →
    IntoNext b (P1 ∧ Q1) (P2 ∧ Q2).
  Proof. Admitted.
  (*   rewrite /IntoNext. intros HP HQ p. *)
  (*   destruct p; simpl; [rewrite bi_intuitionistically_id|]. *)
  (*   - rewrite -ltl_next_and. *)
  (*     rewrite -(HP true). *)
  (*     rewrite -(HQ true). simpl. *)
  (*     rewrite !bi_intuitionistically_id. done. *)
  (*   - rewrite -ltl_next_and. *)
  (*     rewrite -(HP true). *)
  (*     rewrite -(HQ true). simpl. *)
  (*     rewrite !bi_intuitionistically_id. done. *)
  (* Qed. *)

  Global Instance into_next_eventually p (P Q : tProp) :
    IntoNext p P Q →
    IntoNext p (◊ P) (◊ Q).
  Proof. Admitted.
  (*   rewrite /IntoNext. intros HPQ p. *)
  (*   destruct p; simpl; [rewrite bi_intuitionistically_id|]. *)
  (*   - rewrite -ltl_eventually_next_comm. *)
  (*     eapply ltl_eventually_mono. *)
  (*     specialize (HPQ true). simpl in HPQ. *)
  (*     rewrite bi_intuitionistically_id in HPQ. *)
  (*     done. *)
  (*   - rewrite -ltl_eventually_next_comm. *)
  (*     eapply ltl_eventually_mono. *)
  (*     specialize (HPQ true). simpl in HPQ. *)
  (*     rewrite bi_intuitionistically_id in HPQ. *)
  (*     done. *)
  (* Qed. *)

  Global Instance into_next_always p (P : tProp) :
    IntoNext p (□ P) (□ P) | 1.
  Proof. Admitted.
    (* rewrite /IntoNext. intros p. *)
  (*   destruct p; simpl; [rewrite bi_intuitionistically_id|]. *)
  (*   - apply ltl_always_next. *)
  (*   - apply ltl_always_next. *)
  (* Qed. *)

  Global Instance into_next_always' p (P : tProp) :
    IntoNext p (□ ○ P) (□ P) | 0.
  Proof. Admitted.
  (*   rewrite /IntoNext. intros p. *)
  (*   destruct p; simpl; [rewrite bi_intuitionistically_id|]. *)
  (*   - apply ltl_always_next_comm. *)
  (*   - apply ltl_always_next_comm. *)
  (* Qed. *)

  Global Instance into_next_always_id (P : tProp) :
    IntoNext true P P | 10.
  Proof. Admitted.

  Lemma modality_next_mixin : modality_mixin (ltl_next)
    (MIEnvTransform (IntoNext true)) (MIEnvTransform (IntoNext false)).
  Proof.
    split; simpl; eauto.
    - intros. split.
      + intros. rewrite -ltl_always_next_comm. 
        iIntros "#HP !>". iStopProof.
        rewrite /IntoNext in H. apply H.
      + intros. by rewrite ltl_next_and.
    - by apply ltl_next_taut.
    - by apply ltl_next_mono.
    - iIntros (P Q) "[HP HQ]". iApply ltl_next_and. by iSplit.
    Unshelve. all: done.
  Qed.
  Definition modality_next := Modality (@ltl_next S L Rel) modality_next_mixin.
  Global Instance from_modal_next (P : tProp) :
    @FromModal ltlI ltlI _ True%type modality_next (○ P) (○ P) (P).
  Proof. rewrite /FromModal /=. done. Qed.

  Global Instance ltl_next_combine (P Q : tProp) :
    CombineSepAs (○ P) (○ Q) (○ (P ∧ Q)).
  Proof. by rewrite /CombineSepAs bi_sep_and ltl_next_and. Qed.

  Class ltl_eventually_equiv (P : tProp) :=
    ltl_eventually_conv : ∃ Q, P ≡ (◊ Q)%I.

  Global Instance ltl_eventually_equiv_refl (P : tProp) :
    ltl_eventually_equiv (◊ P).
  Proof. exists P. done. Qed.
    
  Global Instance ltl_eventually_equiv_next (P : tProp) :
    ltl_eventually_equiv P →
    ltl_eventually_equiv (○ P).
  Proof.
    intros. destruct H as [Q HQ]. exists (○ Q)%I.
    rewrite ltl_eventually_next_comm. rewrite HQ. done.
  Qed.

  Lemma tac_eventually i j b Δ Δ2 Δ3 (P Q : tProp) :
    ltl_eventually_equiv Q →
    envs_lookup i Δ = Some (b, ◊ P)%I →
    envs_clear_spatial Δ = Δ2 →
    envs_app false (Esnoc Enil j P) Δ2 = Some Δ3 →
    envs_entails Δ3 Q →
    envs_entails Δ Q.
  Proof. Admitted.

End ltl_proofmode.

Tactic Notation "iModEvCore" constr(pat) "as" tactic3(tac) :=
  let Hnew := iFresh in
  eapply (tac_eventually pat Hnew); [tc_solve|done..|pm_reduce; tac Hnew].
Tactic Notation "iModEv" constr(pat) "as" constr(pat2) :=
  iModEvCore pat as (fun H => iDestruct H as pat2).
Tactic Notation "iModEv" constr(pat) :=
  iModEvCore pat as (fun H => iDestruct H as pat).
Tactic Notation "iModEvIntro" :=
  iEval (rewrite -ltl_eventually_intro_now).
