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

  Instance ne_proper (f : tProp → tProp) `{!Proper ((≡) ==> (≡)) f} : NonExpansive f.
  Proof.
    constructor. intros.
    apply Proper0. done.
  Qed.

  Lemma ltl_always_ne : NonExpansive ltl_always.
  Proof.
    apply ne_proper. rewrite ltl_always_unseal.
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
  Qed.

  Lemma ltl_always_mono (P Q : tProp) :
    (ltl_entails P Q)%I → ltl_entails (ltl_always P) (ltl_always Q).
  Proof.
    rewrite ltl_always_unseal.
    intros. constructor. intros.
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
  Qed.

  Lemma ltl_always_idemp (P : tProp) :
    ltl_entails (ltl_always P) (ltl_always (ltl_always P)).
  Proof.
    intros. constructor. rewrite ltl_always_unseal.
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
    Unshelve. done.
  Qed.

  Lemma ltl_always_emp :
    ltl_entails (ltl_pure True) (ltl_always (ltl_pure True)).
  Proof.
    rewrite ltl_always_unseal. econstructor. intros.
    revert tr H.
    cofix IH.
    intros tr Htr.
    destruct tr as [[[]|] ?].
    { econstructor. done. simpl. simpl. rewrite ltl_pure_unseal. done. }
    + econstructor. done. apply IH. rewrite ltl_pure_unseal. done.
    + econstructor. done.
    Unshelve. all: try econstructor. all: by inversion tr_wf0.
  Qed.

  Lemma ltl_always_and (P Q : tProp) :
    ltl_entails (ltl_and (ltl_always P) (ltl_always Q)) (ltl_always (ltl_and P Q)).
  Proof.
    intros.
    rewrite ltl_always_unseal. econstructor. intros.
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
  Qed.

  Lemma ltl_always_affine (P Q : tProp) :
    ltl_entails (ltl_and (ltl_always P) Q) (ltl_always P).
  Proof.
    intros.
    constructor. intros. rewrite ltl_and_unseal in H.
    destruct H. done.
  Qed.

  Lemma ltl_always_sep_and (P Q : tProp) :
    ltl_entails (ltl_and (ltl_always P) Q) (ltl_and P Q).
  Proof.
    intros. constructor. intros. rewrite ltl_and_unseal in H. destruct H.
    rewrite ltl_and_unseal. split.
    + rewrite ltl_always_unseal in H. by inversion H.
    + done.
  Qed.

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

  (* TODO: Move out proofs to axiom modal laws *)
  Lemma ltl_bi_persistently_mixin :
    BiPersistentlyMixin
      ltl_entails ltl_emp ltl_and
      ltl_and ltl_persistently.
  Proof.
    split.
    - apply ltl_always_ne.
    - (* (P ⊢ Q) → <pers> P ⊢ <pers> Q *)
      apply ltl_always_mono.
    - (* <pers> P ⊢ <pers> <pers> P *)
      apply ltl_always_idemp.
    - (* emp ⊢ <pers> emp *)
      apply ltl_always_emp.
    - (* (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q) *)
      apply ltl_always_and.
    - (* <pers> P ∗ Q ⊢ <pers> P *)
      apply ltl_always_affine.
    - (* <pers> P ∧ Q ⊢ P ∗ Q *)
      apply ltl_always_sep_and.
  Qed.

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
  Lemma ltl_emp_unseal : bi_emp = @ltl_pure_def S L Rel True.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Lemma ltl_pure_unseal : bi_pure = @ltl_pure_def S L Rel.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Lemma ltl_and_unseal : bi_and = @ltl_and_def S L Rel.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Lemma ltl_or_unseal : bi_or = @ltl_or_def S L Rel.
  Proof. by rewrite -ltl_or_unseal. Qed.
  Lemma ltl_impl_unseal : bi_impl = @ltl_impl_def S L Rel.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Lemma ltl_forall_unseal : @bi_forall _ = @ltl_forall_def S L Rel.
  Proof. by rewrite -ltl_forall_unseal. Qed.
  Lemma ltl_exist_unseal : @bi_exist _ = @ltl_exist_def S L Rel.
  Proof. by rewrite -ltl_exist_unseal. Qed.
  Lemma ltl_sep_unseal : bi_sep = @ltl_and_def S L Rel.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Lemma ltl_wand_unseal : bi_wand = @ltl_impl_def S L Rel.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Lemma ltl_persistently_unseal : bi_persistently = @ltl_persistently S L Rel.
  Proof. done. Qed.
  Lemma ltl_later_unseal : bi_later = @ltl_later_def S L Rel.
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

End ltl_primitives.

Global Instance: Params (@ltl_now) 2 := {}.
Global Instance: Params (@ltl_next) 2 := {}.

Notation "○ P" := (ltl_next P%I) (at level 20, right associativity) : bi_scope.
Notation "↓ P" := (ltl_now P) (at level 20, right associativity) : bi_scope.

Section ltl_lemmas.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_unseal' :=
    (@ltl_pure_unseal S L, @ltl_and_unseal S L, @ltl_or_unseal S L,
       @ltl_impl_unseal S L, @ltl_forall_unseal S L, @ltl_exist_unseal S L,
         @ltl_later_unseal S L, @ltl_internal_eq_unseal S L,
    @ltl_next_unseal S L, @ltl_now_unseal S L, @ltl_always_unseal S L).

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

  (** Misc *)

  (** ltl_always lemmas *)

  Lemma ltl_always_intro (P : tProp) :
    □ (P → ○ P) ⊢ P → □P.
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

  (* Proofmode stuff *)

  Lemma bi_sep_and (P Q : tProp) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. constructor. intros tr. unseal. done. Qed.
  Lemma bi_wand_impl (P Q : tProp) :
    (P -∗ Q) ⊣⊢ (P → Q).
  Proof. constructor. intros tr. unseal. done. Qed.

End ltl_lemmas.

Section ltl_derived_rules.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

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

  Lemma ltl_next_always_combine (P Q : tProp) :
    (□ P ∧ ○ Q) ⊢ (○ (Q ∧ □ P)).
  Proof. by rewrite bi.and_comm {1}ltl_always_next ltl_next_and. Qed.

  Lemma ltl_sep_and (P Q : tProp) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. done. Qed.

  (** Proofmode stuff *)

  (* TODO: Move *)
  Global Instance ltl_next_proper : Proper ((≡) ==> (≡)) (@ltl_next S L Rel).
  Proof.
    constructor.
    intros. split.
    - apply ltl_next_mono. rewrite H. done.
    - apply ltl_next_mono. rewrite H. done.
  Qed.

End ltl_derived_rules.

Section ltl_proofmode.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Import tProp.

  (* Proofmode support for next modality *)

  Global Instance into_and_next (P Q1 Q2 : tProp) :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (○ P)%I (○ Q1)%I (○ Q2)%I.
  Proof.
    rewrite /IntoAnd. simpl.
    intros HPQ.
    rewrite ltl_next_and.
    by eapply ltl_next_mono.
  Qed.

  Global Instance into_sep_next (P Q1 Q2 : tProp) :
    IntoSep P Q1 Q2 →
    IntoSep (○ P)%I (○ Q1)%I (○ Q2)%I.
  Proof. apply into_and_next. Qed.

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
  Proof.
    rewrite /IntoNext. intros HP HQ.
    destruct b; simpl.
    - rewrite -ltl_next_and. simpl in *.
      rewrite bi.intuitionistically_and.
      rewrite HP HQ. done.
    - rewrite -ltl_next_and. simpl in *.
      rewrite HP HQ. done.
  Qed.

  Global Instance into_next_sep b (P1 P2 Q1 Q2 : tProp) :
    IntoNext b P1 P2 →
    IntoNext b Q1 Q2 →
    IntoNext b (P1 ∗ Q1) (P2 ∗ Q2).
  Proof. apply into_next_and. Qed.

  Global Instance into_next_always p (P : tProp) :
    IntoNext p (□ P) (□ P) | 1.
  Proof.
    rewrite /IntoNext. destruct p.
    - simpl. rewrite -ltl_always_next. eauto.
    - apply ltl_always_next.
  Qed.

  Global Instance into_next_always_comm p (P : tProp) :
    IntoNext p (□ ○ P) (□ P) | 0.
  Proof.
    rewrite /IntoNext. destruct p.
    - simpl. rewrite -ltl_always_next_comm. eauto.
    - apply ltl_always_next_comm.
  Qed.

  Global Instance into_next_always_id (P : tProp) :
    IntoNext true P P | 10.
  Proof.
    rewrite /IntoNext. simpl. rewrite ltl_always_next.
    apply ltl_next_mono. eauto.
  Qed.

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

  Global Instance into_wand_next p (P Q R : tProp) :
    IntoWand p p R P Q → IntoWand p p (○ R)%I (○ P)%I (○ Q)%I.
  Proof.
    rewrite /IntoWand.
    destruct p; simpl.
    - intros HR. iIntros "#HR #HP".
      iModIntro. iApply (HR with "HR HP").
    - intros HR. iIntros "HR HP".
      iAssert (○ (R ∧ P))%I with "[HR HP]" as "H".
      { iApply ltl_next_and. iSplit; iFrame. }
      iApply (ltl_next_mono with "H").
      rewrite HR.
      iIntros "[HPQ HP]". by iApply "HPQ".
  Qed.

End ltl_proofmode.

Section ltl_derived_constructs.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (* Eventually *)
  Definition ltl_until_F (P Q : tProp) : (() → tProp) → (() → tProp) :=
    (λ (X : unit → tProp) _, Q ∨ (P ∧ ○ (X ())))%I.

  Instance ltl_until_F_mono P Q : BiMonoPred (ltl_until_F P Q).
  Proof.
    constructor.
    - intros. iIntros "#H" (x) "HF".
      rewrite /ltl_until_F.
      iDestruct "HF" as "[HQ|[HP HF]]"; [by iLeft|].
      iRight. iFrame.
      iModIntro. by iApply "H".
    - intros. apply _.
  Qed.

  Definition ltl_until_def (P Q : tProp) : tProp :=
    bi_least_fixpoint (ltl_until_F P Q)%I ().
  Definition ltl_until_aux : seal (@ltl_until_def).
  Proof. by eexists. Qed.
  Definition ltl_until := unseal ltl_until_aux.
  Definition ltl_until_unseal :
    @ltl_until = @ltl_until_def := seal_eq ltl_until_aux.

  Notation "P ∪ Q" := (ltl_until P Q%I) : bi_scope.
  Notation "◊ P" := (ltl_until True P%I) (at level 20, right associativity) : bi_scope.

  Lemma ltl_until_unfold (P Q : tProp) :
    (P ∪ Q)%I ≡ (Q ∨ P ∧ ○ (P ∪ Q))%I.
  Proof. rewrite ltl_until_unseal. by rewrite /ltl_until_def {1}least_fixpoint_unfold. Qed.

  Lemma ltl_until_intro (P Q : tProp) :
    Q ∨ P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof. rewrite {2}ltl_until_unfold. done. Qed.

  Lemma ltl_until_ind P Q R :
    □ (Q ∨ (P ∧ ○ (P ∪ Q) ∧ ○ R) -∗ R) -∗
    P ∪ Q -∗ R.
  Proof.
    iIntros "#IH HPQ".
    rewrite ltl_until_unseal.
    iApply (least_fixpoint_ind with "[] HPQ").
    iIntros "!>" (?) "[Q|[HP HR]]".
    { iApply "IH". by eauto. }
    iApply "IH". iRight. iFrame.
    iSplit.
    - iModIntro. iDestruct "HR" as "[_ $]".
    - iModIntro. iDestruct "HR" as "[$ _]".
  Qed.

  Lemma ltl_until_mono P1 P2 Q1 Q2 :
    □ (P1 → P2) ⊢ □ (Q1 → Q2) →
    P1 ∪ Q1 → P2 ∪ Q2.
  Proof.
    iIntros "#HP #HQ HPQ".
    iApply (ltl_until_ind with "[] HPQ").
    iModIntro.
    iDestruct 1 as "[H|H]".
    { rewrite ltl_until_unfold. iLeft. by iApply "HQ". }
    iEval (rewrite ltl_until_unfold). iRight.
    iDestruct "H" as "[H IH]".
    iSplit.
    - by iApply "HP".
    - iDestruct "IH" as "[_ $]".
  Qed.

  Lemma ltl_until_mono_alt P1 P2 Q1 Q2 :
    (P1 ⊢ P2) → (Q1 ⊢ Q2) →
    P1 ∪ Q1 ⊢ P2 ∪ Q2.
  Proof.
    intros HP HQ.
    iApply ltl_until_mono.
    iApply HP.
    iApply HQ.
  Qed.

  Lemma ltl_until_mono' P1 P2 Q1 Q2 :
    □ (P1 → P2) ∧ □ (Q1 → Q2) ⊢
    P1 ∪ Q1 → P2 ∪ Q2.
  Proof.
    iIntros "[#HP #HQ] HPQ".
    iApply (ltl_until_ind with "[] HPQ").
    iModIntro.
    iDestruct 1 as "[H|H]".
    { rewrite ltl_until_unfold. iLeft. by iApply "HQ". }
    iEval (rewrite ltl_until_unfold). iRight.
    iDestruct "H" as "[H IH]".
    iSplit.
    - by iApply "HP".
    - iDestruct "IH" as "[_ $]".
  Qed.

  Lemma ltl_until_and (P Q1 Q2 : tProp) :
    (P ∪ (Q1 ∧ Q2)) ⊢ (P ∪ Q1) ∧ (P ∪ Q2).
  Proof.
    rewrite ltl_until_unfold.
    iIntros "[H|H]".
    { iDestruct "H" as "[H1 H2]".
      rewrite (ltl_until_unfold _ Q1).
      rewrite (ltl_until_unfold _ Q2).
      iSplit; by iLeft. }
    iSplit.
    - iEval (rewrite ltl_until_unfold).
      iRight. iDestruct "H" as "[$ H]".
      iModIntro. iApply (ltl_until_mono with "[] [] H").
      + eauto.
      + iIntros "!>[$ _]".
    - iEval (rewrite ltl_until_unfold).
      iRight. iDestruct "H" as "[$ H]".
      iModIntro. iApply (ltl_until_mono with "[] [] H").
      + eauto.
      + iIntros "!>[_ $]".
  Qed.

  Lemma ltl_until_next_comm (P Q : tProp) :
    (○ P ∪ ○ Q) ⊣⊢ ○ (P ∪ Q).
  Proof.
    iSplit.
    - iApply ltl_until_ind.
      iIntros "!>H".
      iDestruct "H" as "[HQ|H]".
      + iModIntro. rewrite ltl_until_unfold. by iLeft.
      + iModIntro. iEval (rewrite ltl_until_unfold). iRight.
        iDestruct "H" as "[$ [HP HQ]]". iModIntro. done.
    - iIntros "H".
      iEval (rewrite ltl_until_unfold).
      rewrite ltl_next_and.
      iEval (rewrite (ltl_next_or Q)).
      iModIntro.
      iApply (ltl_until_ind with "[] H").
      iIntros "!>H".
      iDestruct "H" as "[H|H]".
      { iLeft. done. }
      iRight.
      iDestruct "H" as "[$ [_ H]]".
      rewrite {2}ltl_until_unfold.
      rewrite ltl_next_and ltl_next_or.
      iModIntro.
      iDestruct "H" as "[H|H]".
      { iLeft. done. }
      iRight.
      done.
  Qed.

  (* Derived *)

  Lemma ltl_until_idemp (P Q : tProp) :
    (P ∪ (P ∪ Q)) ⊣⊢ (P ∪ Q).
  Proof.
    iSplit.
    - iApply ltl_until_ind.
      iIntros "!> [H|(?&?&?)]".
      { done. }
      iEval (rewrite ltl_until_unfold). iRight. iFrame.
    - iApply ltl_until_ind.
      iIntros "!> [H|(?&?&?)]".
      { rewrite ltl_until_unfold. iLeft. rewrite ltl_until_unfold. iLeft. done. }
      iEval (rewrite ltl_until_unfold). iRight. iFrame.
  Qed.

  Lemma ltl_until_intro_now (P Q : tProp) :
    Q ⊢ P ∪ Q.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_until_intro_next (P Q : tProp) :
    P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof. rewrite -{2}ltl_until_intro. apply bi.or_intro_r. Qed.

  Lemma ltl_until_always_combine (P Q R : tProp) :
    (□ P ∧ Q ∪ R) ⊢ ((Q ∪ (R ∧ □ P))).
  Proof.
    iIntros "[#HP HQ]".
    iApply (ltl_until_ind with "[] HQ").
    iIntros "!> [HQ|H]".
    { iApply ltl_until_intro_now. iFrame "#∗". }
    iEval (rewrite -ltl_until_intro_next).
    iDestruct "H" as "[$ H]".
    iModIntro.
    iDestruct "H" as "[_ $]".
  Qed.

  Lemma ltl_until_and_r' (P1 P2 Q1 Q2 : tProp) :
    P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ (P1 ∧ P2) ∪ ((Q1 ∧ P2 ∪ Q2) ∨ (P1 ∪ Q1 ∧ Q2)).
  Proof.
    iIntros "[H1 H2]".
    iRevert "H2".
    iApply (ltl_until_ind with "[] H1").
    iIntros "!> H1 H2".
    rewrite {3}(ltl_until_unfold P2 Q2).
    iDestruct "H1" as "[HQ1|(HP1&HPQ1&IH)]".
    { iDestruct "H2" as "[HQ2|[HP2 HPQ2]]".
      { iEval (rewrite ltl_until_unfold). iLeft.
        iEval (rewrite ltl_until_unfold). iFrame. }
      { iEval (rewrite ltl_until_unfold). iLeft. iLeft. iFrame.
        iEval (rewrite ltl_until_unfold). iRight. iFrame. }
    }
    iDestruct "H2" as "[HQ2|[HP2 HPQ2]]".
    { iEval (rewrite ltl_until_unfold). iLeft.
      iEval (rewrite ltl_until_unfold). iRight.
      iEval (rewrite ltl_until_unfold). iFrame. iRight. iFrame. }
    iEval (rewrite ltl_until_unfold). iRight.
    iFrame. iModIntro.
    by iApply "IH".
  Qed.

  Lemma ltl_until_or (P Q1 Q2 : tProp) :
    P ∪ (Q1 ∨ Q2) ⊢ P ∪ Q1 ∨ P ∪ Q2.
  Proof.
    iApply ltl_until_ind.
    iIntros "!> [HQ|HP]".
    { iDestruct "HQ" as "[HQ1|HQ2]".
      - iLeft. by rewrite -ltl_until_intro_now.
      - iRight. by rewrite -ltl_until_intro_now.
    }
    iDestruct "HP" as "(HP&HPQ&IH)".
    rewrite -!ltl_until_next_comm.
    rewrite {1}(ltl_next_or_r (P ∪ Q1)).
    iDestruct "IH" as "[IH|IH]".
    - iLeft. iEval (rewrite ltl_until_unfold).
      iRight. iFrame.
    - iRight. iEval (rewrite ltl_until_unfold).
      iRight. iFrame.
  Qed.

  Lemma ltl_until_and_r (P1 P2 Q1 Q2 : tProp) :
    P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ ((P1 ∧ P2) ∪ (Q1 ∧ (P2 ∪ Q2))) ∨ ((P1 ∧ P2) ∪ (P1 ∪ Q1 ∧ Q2)).
  Proof. rewrite -ltl_until_or. apply ltl_until_and_r'. Qed.

  Global Instance ltl_until_proper : Proper ((≡) ==> (≡) ==> (≡)) (ltl_until).
  Proof.
    constructor.
    intros. split.
    - apply ltl_until_mono_alt; [by rewrite H|by rewrite H0].
    - apply ltl_until_mono_alt; [by rewrite H|by rewrite H0].
  Qed.

  Global Instance ltl_until_combine (P1 P2 Q1 Q2 : tProp) :
    CombineSepAs (P1 ∪ Q1) (P2 ∪ Q2) (((P1 ∧ P2) ∪ (Q1 ∧ (P2 ∪ Q2))) ∨ ((P1 ∧ P2) ∪ (P1 ∪ Q1 ∧ Q2))) | 1.
  Proof. rewrite /CombineSepAs. apply ltl_until_and_r. Qed.

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
    □ (P → Q) ⊢ ◊P → ◊Q.
  Proof. by iApply ltl_until_mono. Qed.

  Lemma ltl_eventually_mono_alt (P Q : tProp) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof. by apply ltl_until_mono_alt. Qed.

  Lemma ltl_eventually_and (P Q : tProp) :
    (◊ (P ∧ Q)) ⊢ (◊ P) ∧ (◊ Q).
  Proof. by rewrite -ltl_until_and. Qed.

  Lemma ltl_eventually_next_comm (P : tProp) :
    (◊ ○ P) ⊣⊢ (○ ◊ P).
  Proof.
    rewrite -ltl_until_next_comm.
    apply bi.equiv_entails_2.
    - apply ltl_until_mono_alt; [|done]. by apply ltl_next_taut.
    - apply ltl_until_mono_alt; [|done]. eauto.
  Qed.

  Lemma ltl_eventually_idemp (P : tProp) :
    (◊◊P) ⊣⊢ (◊P).
  Proof. apply ltl_until_idemp. Qed.

  Lemma ltl_eventually_next (P : tProp) :
    (◊ ○ P) ⊢ (◊ P).
  Proof.
    rewrite <-(ltl_eventually_idemp P).
    apply ltl_eventually_mono_alt.
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
  Proof. apply ltl_until_mono_alt; by eauto. Qed.

  Lemma ltl_eventually_ind (P Q : tProp) :
    (□ (P ∨ ○ ◊ P ∧ ○ Q → Q)) ⊢ ◊ P → Q.
  Proof.
    iIntros "#H". iApply ltl_until_ind.
    iModIntro. iIntros "[HP|HP]".
    { iApply "H". iLeft. done. }
    iApply "H". iRight. iDestruct "HP" as "[_ $]".
  Qed.

  Lemma ltl_eventually_ind_alt (P Q : tProp) :
    (P ⊢ Q) →
    ((○ ◊ P) ∧ ○ Q ⊢ Q) →
    ◊ P ⊢ Q.
  Proof.
    intros H1 H2.
    iApply ltl_eventually_ind.
    iDestruct H1 as "#H1".
    iDestruct H2 as "#H2".
    iModIntro. iIntros "[HP|HP]"; [by iApply "H1"|by iApply "H2"].
  Qed.

  Lemma ltl_always_eventually (P : tProp) :
    □ P ⊢ ◊ P.
  Proof. rewrite -ltl_eventually_intro_now. eauto. Qed.

  Lemma ltl_eventually_always_combine (P Q : tProp) :
    (□ P ∧ ◊Q) ⊢ (◊ (Q ∧ □ P)).
  Proof.
    iIntros "[#HP HQ]".
    iApply (ltl_eventually_ind with "[] HQ").
    iIntros "!> [HQ|H]".
    { iApply ltl_eventually_intro_now. iFrame "#∗". }
    iEval (rewrite -ltl_eventually_idemp).
    iEval (rewrite -ltl_eventually_intro_next).
    iModIntro.
    iDestruct "H" as "[_ $]".
  Qed.

  Global Instance into_and_eventually (P Q1 Q2 : tProp) :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof.
    rewrite /IntoAnd. simpl.
    intros HPQ.
    rewrite -ltl_eventually_and.
    by eapply ltl_eventually_mono_alt.
  Qed.

  Global Instance into_sep_eventually (P Q1 Q2 : tProp) :
    IntoSep P Q1 Q2 →
    IntoSep (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof.
    rewrite /IntoSep.
    simpl.
    rewrite !bi_sep_and.
    intros HPQ.
    rewrite -ltl_eventually_and.
    by eapply ltl_eventually_mono_alt.
  Qed.

  Global Instance into_next_eventually (P Q : tProp) :
    IntoNext false P Q →
    IntoNext false (◊ P) (◊ Q).
  Proof.
    rewrite /IntoNext. intros HPQ.
    rewrite -ltl_eventually_next_comm.
    eapply ltl_eventually_mono_alt.
    specialize HPQ. simpl in HPQ.
    done.
  Qed.

  Lemma ltl_eventually_and_r (P Q : tProp) :
    ◊ P ∧ ◊ Q ⊢ ◊ (P ∧ ◊ Q) ∨ ◊ (◊ P ∧ Q).
  Proof. by rewrite ltl_until_and_r right_id. Qed.

  Global Instance ltl_eventually_combine (P Q : tProp) :
    CombineSepAs (◊ P) (◊ Q) (◊ (P ∧ ◊ Q) ∨ ◊ (◊ P ∧ Q)) | 0.
  Proof. rewrite /CombineSepAs. apply ltl_eventually_and_r. Qed.

  Class ltl_until_equiv (P Q R : tProp) :=
    ltl_until_conv : P ≡ (Q ∪ R)%I.

  Global Instance ltl_until_equiv_refl (P Q : tProp) :
    ltl_until_equiv (P ∪ Q) P Q | 0.
  Proof. done. Qed.

  Global Instance ltl_until_equiv_next (P Q R : tProp) :
    ltl_until_equiv P Q R →
    ltl_until_equiv (○ P) (○ Q) (○ R) | 2.
  Proof.
    intros. rewrite /ltl_until_equiv. rewrite ltl_until_next_comm. by rewrite H.
  Qed.

  Global Instance ltl_eventually_equiv_next' (P Q : tProp) :
    ltl_until_equiv P True Q →
    ltl_until_equiv (○ P) True (○ Q) | 1.
  Proof.
    intros. rewrite /ltl_until_equiv.
    rewrite ltl_eventually_next_comm. rewrite H. done.
  Qed.

  Lemma envs_clear_delete_spatial_eq {PROP} i b (Δ : envs PROP) :
    envs_clear_spatial (envs_delete false i b Δ) = envs_clear_spatial Δ.
  Proof.
    destruct b.
    - by rewrite envs_delete_intuitionistic.
    - by destruct Δ.
  Qed.

  Global Instance elim_modal_until p P P' Q R R' :
    ltl_until_equiv P Q R →
    ltl_until_equiv P' Q R' →
    ElimModal True p false modality_persistently P' R' P P.
  Proof.
    intros HP HP'.
    rewrite /ElimModal.
    iIntros "_ [HP' HP]".
    destruct p; simpl.
    - rewrite HP HP'.
      iDestruct "HP'" as "#HP'".
      iDestruct "HP" as "#HP".
      iEval (rewrite -ltl_until_idemp).
      by iApply (ltl_until_mono Q Q R'); [eauto| |done].
    - rewrite HP HP'.
      iDestruct "HP" as "#HP".
      iEval (rewrite -ltl_until_idemp).
      by iApply (ltl_until_mono Q Q R'); [eauto| |done].
  Qed.

End ltl_derived_constructs.

Notation "P ∪ Q" := (ltl_until P Q%I) : bi_scope.
Notation "◊ P" := (ltl_until True P%I) (at level 20, right associativity) : bi_scope.

Tactic Notation "iModUnIntro" :=
  iEval (rewrite -ltl_until_intro_now).
