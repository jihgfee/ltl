From iris.proofmode Require Import proofmode.

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

(* TODO: Polish and move *)
Section well_formed.
  Context {S L : Type}.
  Context (R : S → L → S → Prop).

  Definition head_trace (tr : trace S L) : option S :=
    match tr with
    | Some (tr_singl s) => Some s
    | Some (tr_cons s ℓ r) => Some s
    | None => None
    end.

  (* Inductive foo {A} (P : A → SProp) : A -> SProp := *)
  (*   | Foo a : P a → foo P a. *)

  (* Lemma bar {A} (P : A → SProp) a : *)
  (*   foo P a -> P a. *)
  (* Proof. inversion 1. done. Qed. *)

  CoInductive trace_maximal : trace S L → SProp :=
  | trace_maximal_empty : trace_maximal None
  | trace_maximal_singleton c :
    (∀ oζ c', ¬ R c oζ c') → trace_maximal (Some $ tr_singl c)
  | trace_maximal_cons c oζ tr c' :
    head_trace (Some tr) = Some c' →
    R c oζ c' →
    trace_maximal (Some tr) →
    trace_maximal (Some $ tr_cons c oζ tr).

  (* Lemma foo s : trace_maximal ⟨ s ⟩ -> (∀ l s', ¬ R s l s'). *)
  (* Proof. inversion 1. *)

  (* Definition well_formed_trace : trace S L → Prop := trace_maximal. *)

End well_formed.

Record wf_trace S L R := Trace {
  tr_car : trace S L;
  tr_wf : trace_maximal R tr_car;
}.

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

Definition ltl_prop S L R := wf_trace S L R → Prop.

Bind Scope bi_scope with ltl_prop.
Bind Scope bi_scope with trace.

Section cofe.
  Context {S L : Type}.
  Context {R : S → L → S → Prop}.
  Notation ltl_prop := (@ltl_prop S L R).

  Inductive ltl_prop_equiv' (P Q : ltl_prop) : Prop :=
    { ltl_prop_in_equiv : ∀ tr, P tr ↔ Q tr }.
  Local Instance ltl_prop_equiv : Equiv ltl_prop := ltl_prop_equiv'.
  Local Instance heapProp_equivalence : Equivalence (≡@{ltl_prop}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure ltl_PropO := discreteO ltl_prop.
End cofe.

Section ltl_constructors.
  Context {S L : Type}.
  Context {R : S → L → S → Prop}.
  Notation ltl_prop := (ltl_prop S L R).
  Implicit Type P Q : ltl_prop.

  Inductive ltl_entails (P Q : ltl_prop) : Prop :=
    { ltl_in_entails : ∀ tr, P tr → Q tr }.

  (* Primitive operators *)
  Definition ltl_pure_def (P : Prop) : ltl_prop :=
    λ tr, P.
  Definition ltl_pure_aux : seal (@ltl_pure_def).
  Proof. by eexists. Qed.
  Definition ltl_pure := unseal ltl_pure_aux.
  Definition ltl_pure_unseal :
    @ltl_pure = @ltl_pure_def := seal_eq ltl_pure_aux.

  Definition ltl_or_def (P Q : ltl_prop) : ltl_prop :=
    λ tr, P tr ∨ Q tr.
  Definition ltl_or_aux : seal (@ltl_or_def).
  Proof. by eexists. Qed.
  Definition ltl_or := unseal ltl_or_aux.
  Definition ltl_or_unseal :
    @ltl_or = @ltl_or_def := seal_eq ltl_or_aux.

  Definition ltl_and_def (P Q : ltl_prop) : ltl_prop :=
    λ tr, P tr ∧ Q tr.
  Definition ltl_and_aux : seal (@ltl_and_def).
  Proof. by eexists. Qed.
  Definition ltl_and := unseal ltl_and_aux.
  Definition ltl_and_unseal :
    @ltl_and = @ltl_and_def := seal_eq ltl_and_aux.

  Definition ltl_impl_def (P Q : ltl_prop) : ltl_prop :=
    λ tr, P tr → Q tr.
  Definition ltl_impl_aux : seal (@ltl_impl_def).
  Proof. by eexists. Qed.
  Definition ltl_impl := unseal ltl_impl_aux.
  Definition ltl_impl_unseal :
    @ltl_impl = @ltl_impl_def := seal_eq ltl_impl_aux.

  Definition ltl_forall_def {A} (Ψ : A → ltl_prop) : ltl_prop :=
    λ tr, ∀ (x:A), Ψ x tr.
  Definition ltl_forall_aux : seal (@ltl_forall_def).
  Proof. by eexists. Qed.
  Definition ltl_forall {A} := unseal ltl_forall_aux A.
  Definition ltl_forall_unseal :
    @ltl_forall = @ltl_forall_def := seal_eq ltl_forall_aux.

  Definition ltl_exist_def {A} (Ψ : A → ltl_prop) : ltl_prop :=
    λ tr, ∃ (x:A), Ψ x tr.
  Definition ltl_exist_aux : seal (@ltl_exist_def).
  Proof. by eexists. Qed.
  Definition ltl_exist {A} := unseal ltl_exist_aux A.
  Definition ltl_exist_unseal :
    @ltl_exist = @ltl_exist_def := seal_eq ltl_exist_aux.

  Definition ltl_later_def (P : ltl_prop) : ltl_prop := P.
  Definition ltl_later_aux : seal (@ltl_later_def).
  Proof. by eexists. Qed.
  Definition ltl_later := unseal ltl_later_aux.
  Definition ltl_later_unseal :
    @ltl_later = @ltl_later_def := seal_eq ltl_later_aux.

  Definition ltl_internal_eq_def {A:ofe} (a1 a2 : A) : ltl_prop :=
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

  Notation ltl_prop := (ltl_prop S L Rel).
  Implicit Type P Q : ltl_prop.

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
  Lemma equiv_entails (P Q : ltl_prop) : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
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
  (* Lemma test {A} (φ : A → ltl_prop S L Rel) : ⊢ (∀ a, φ a)%ltl. *)
  Lemma pure_forall_2 {A} (φ : A → Prop) :
    ((∀ a, ⌜ φ a ⌝):ltl_prop) ⊢ ⌜ ∀ a, φ a ⌝.
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

  Lemma forall_intro {A} P (Ψ : A → ltl_prop) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n ? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → ltl_prop} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → ltl_prop} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> n ?; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → ltl_prop) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΨ; split=> n [a ?]; by apply HΨ with a. Qed.

  (** Later *)
  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof. unseal=> HP; split=>tr. rewrite /ltl_later_def.
         destruct HP as [HP]. apply HP. Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof. unseal; split=> /= HP. done. Qed.

  Lemma later_forall_2 {A} (Φ : A → ltl_prop) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; by split. Qed.
  Lemma later_exist_false {A} (Φ : A → ltl_prop) :
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
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → ltl_prop) :
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

Section ltl.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation ltl_prop := (ltl_prop S L Rel).

  Definition ltl_emp : ltl_prop := ltl_pure True.
  Definition ltl_persistently (P : ltl_prop) : ltl_prop := P.
  Definition ltl_plainly (P : ltl_prop) : ltl_prop := P.

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

  Lemma ltl_bi_persistently_mixin :
    BiPersistentlyMixin
      ltl_entails ltl_emp ltl_and
      (@ltl_exist S L Rel) ltl_and ltl_persistently.
  Proof.
    split.
    - solve_proper.
    - (* (P ⊢ Q) → <pers> P ⊢ <pers> Q *)
      done.
    - (* <pers> P ⊢ <pers> <pers> P *)
      done.
    - (* emp ⊢ <pers> emp *)
      done.
    - (* (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a) *)
      done.
    - (* <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a) *)
      done.
    - (* <pers> P ∗ Q ⊢ <pers> P *)
      apply and_elim_l.
    - (* <pers> P ∧ Q ⊢ P ∗ Q *)
      done.
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
      done.
    - (* <pers> ▷ P ⊢ ▷ <pers> P *)
      done.
    - exact: later_false_em.
  Qed.

End ltl.

Canonical Structure ltlI {S L : Type} {Rel} : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (ltl_prop S L Rel);
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

  Global Instance ltl_persistent (P : ltl_prop S L Rel) : Persistent P.
  Proof. done. Qed.

End ltl.

Global Hint Immediate ltl_affine : core.

(** extra BI instances *)

(** Re-state/export soundness lemmas *)

Module ltl_prop.
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
End ltl_prop.

Section ltl_primitives.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation ltl_prop := (ltl_prop S L Rel).

  (* Notation "⟨ ⟩" := (Trace None trace_maximal_empty) : trace_scope. *)

  (* Lemma tr_singl_wf : trace_maximal Rel ⟨⟩. *)
  (* Proof. constructor. Qed. *)

  Arguments Trace {_ _ _} _ _.
  Arguments tr_car {_ _ _} _.
  Arguments tr_wf {_ _ _} _.
  Arguments trace_maximal_empty {_ _ _}.
  Arguments trace_maximal_singleton {_ _ _} _ _.

  (* LTL Operators *)
  (* Primitive operators *)
  Inductive ltl_now_def (P : option (S * option L) → Prop) : ltl_prop :=
  | ltl_now_empty tr : tr_car tr = ⟨⟩ → P None → ltl_now_def P tr
  | ltl_now_single s tr : tr_car tr = ⟨s⟩ → P (Some (s, None)) → ltl_now_def P tr
  | ltl_now_cons s l tr' tr : tr_car tr = (s -[ l ]-> tr') → P (Some (s,Some l)) → ltl_now_def P tr.
  Definition ltl_now_aux : seal (@ltl_now_def).
  Proof. by eexists. Qed.
  Definition ltl_now := unseal ltl_now_aux.
  Definition ltl_now_unseal :
    @ltl_now = @ltl_now_def := seal_eq ltl_now_aux.

  (* Lemma trace_maximal_tail (tr : wf_trace S L Rel) s l tr' : *)
  (*   tr_car tr = Some $ tr_cons s l tr' → trace_maximal Rel (Some tr'). *)
  (* Proof. Admitted. *)

  (* Program Definition tr_tail (tr : wf_trace S L Rel) : option $ wf_trace S L Rel := *)
  (*   match tr with *)
  (*   | {| tr_car := None; tr_wf := P |} => None *)
  (*   | {| tr_car := Some (tr_singl _); tr_wf := P |} => None *)
  (*   | {| tr_car := Some (tr_cons s l tr'); tr_wf := P |} => Some (Trace (Some tr') (trace_maximal_tail tr s l tr' _)) *)
  (*   end. *)
  (* Next Obligation. *)
  (*   intros. subst. simpl. done. *)
  (* Qed. *)

  Inductive ltl_next_def (P : ltl_prop) : ltl_prop :=
  | ltl_next_empty H1 H2 : P (Trace ⟨⟩ H1) -> ltl_next_def P (Trace ⟨⟩ H2)
  | ltl_next_single s H1 H2 : P (Trace ⟨⟩ H1) -> ltl_next_def P (Trace ⟨s⟩ H2)
  | ltl_next_cons s l tr H1 H2 :
    P (Trace (Some tr) H1) →
    ltl_next_def P (Trace (s -[ l ]-> tr) H2).

  (* Inductive ltl_next_def (P : ltl_prop) : ltl_prop := *)
  (* | ltl_next_empty tr : tr_car tr = ⟨⟩ → P tr -> ltl_next_def P tr *)
  (* | ltl_next_single s tr : tr_car tr = ⟨s⟩  → P (Trace None trace_maximal_empty) -> ltl_next_def P tr *)
  (* | ltl_next_cons s l tr' tr : ∀ (H:tr_car tr = (s -[ l ]-> tr')), P (Trace (Some tr') (trace_maximal_tail tr s l tr' H)) → ltl_next_def P tr. *)
  Definition ltl_next_aux : seal (@ltl_next_def).
  Proof. by eexists. Qed.
  Definition ltl_next := unseal ltl_next_aux.
  Definition ltl_next_unseal :
    @ltl_next = @ltl_next_def := seal_eq ltl_next_aux.

  Inductive ltl_until_def (P Q : ltl_prop) : ltl_prop :=
  | ltl_until_here tr H1 H2 : Q (Trace tr H1) -> ltl_until_def P Q (Trace tr H2)
  | ltl_until_single s H1 H2 H3 : P (Trace ⟨s⟩ H1) → Q (Trace ⟨⟩ H2) → ltl_until_def P Q (Trace ⟨s⟩ H3)
  | ltl_until_cons s l tr H1 H2 H3 : P (Trace (s -[l]-> tr) H1) → ltl_until_def P Q (Trace (Some tr) H2) → ltl_until_def P Q (Trace (s -[l]-> tr) H3).
  Definition ltl_until_aux : seal (@ltl_until_def).
  Proof. by eexists. Qed.
  Definition ltl_until := unseal ltl_until_aux.
  Definition ltl_until_unseal :
    @ltl_until = @ltl_until_def := seal_eq ltl_until_aux.

  Notation ltl_eventually P := (ltl_until True P).

  Notation "tr @ tr_wf" := (Trace tr tr_wf) (at level 100).

  CoInductive ltl_always_def (P : ltl_prop) : ltl_prop :=
  | ltl_always_def_empty H1 H2 : P (⟨⟩ @ H1) → ltl_always_def P (Trace ⟨⟩ H2)
  | ltl_always_def_singl s H1 H2 H3 : P (Trace ⟨ s ⟩ H1) → P (Trace ⟨⟩ H2) → ltl_always_def P (Trace ⟨s⟩ H3)
  | ltl_always_def_cons s l tr H1 H2 H3 : P (s -[l]-> tr @ H1) → ltl_always_def P (Some tr @ H2) → ltl_always_def P (s -[l]-> tr @ H3).
  Definition ltl_always_aux : seal (@ltl_always_def).
  Proof. by eexists. Qed.
  Definition ltl_always := unseal ltl_always_aux.
  Definition ltl_always_unseal :
    @ltl_always = @ltl_always_def := seal_eq ltl_always_aux.

End ltl_primitives.

Global Instance: Params (@ltl_now) 2 := {}.
Global Instance: Params (@ltl_next) 2 := {}.
Global Instance: Params (@ltl_until) 2 := {}.
Global Instance: Params (@ltl_always) 2 := {}.

Notation "○ P" := (ltl_next P%I) (at level 20, right associativity) : bi_scope.
Notation "□ P" := (ltl_always P%I) (at level 20, right associativity) : bi_scope.
Notation "◊ P" := (ltl_until True P%I) (at level 20, right associativity) : bi_scope.
Notation "P ∪ Q" := (ltl_until P Q%I) : bi_scope.
Notation "↓ P" := (ltl_now P) (at level 20, right associativity) : bi_scope.

Notation "□^ P" := (bi_intuitionistically P) (at level 20, right associativity).
Notation "'□^?' p P" := (bi_intuitionistically_if p P) (at level 20, p at level 9, P at level 20,
   right associativity, format "'□^?' p  P").

Section ltl_lemmas.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation ltl_prop := (ltl_prop S L Rel).

  Definition ltl_unseal' :=
    (@ltl_pure_unseal S L, @ltl_and_unseal S L, @ltl_or_unseal S L,
       @ltl_impl_unseal S L, @ltl_forall_unseal S L, @ltl_exist_unseal S L,
         @ltl_later_unseal S L, @ltl_internal_eq_unseal S L,
    @ltl_next_unseal S L, @ltl_now_unseal S L, @ltl_always_unseal S L,
    @ltl_until_unseal S L).

  Ltac ltl_unseal := rewrite !ltl_unseal' /=.

  Import ltl_prop.

  (* Lemma ltl_next_adequacy (P : ltl_prop) (tr : trace S L) : *)
  (*   (⊢ ○ P) → P (after 1 tr). *)
  (* Proof. *)
  (*   ltl_unseal. intros [HP]. *)
  (*   assert (ltl_next_def P tr). *)
  (*   { apply HP. unseal. done. } *)
  (*   inversion H. *)
  (*   - done. *)
  (*   - done. *)
  (*   - done. *)
  (* Qed. *)

  (* Lemma ltl_eventually_adequacy (P : ltl_prop) (tr : trace S L) : *)
  (*   (⊢ ◊ P) → ∃ n, P (after n tr). *)
  (* Proof. *)
  (*   ltl_unseal. intros [HP]. *)
  (*   assert (ltl_until_def True P tr) as HP'. *)
  (*   { apply HP. unseal. done. } *)
  (*   clear HP. *)
  (*   induction HP'. *)
  (*   - exists 0. done.  *)
  (*   - exists 1. simpl. done.  *)
  (*   - destruct IHHP' as [n HP'']. *)
  (*     exists (1+n). simpl. done. *)
  (* Qed. *)

  (* Definition get_state (tr : trace S L) : option (S * option L) := *)
  (*   match tr with *)
  (*   | ⟨⟩ => None *)
  (*   | ⟨s⟩ => Some (s,None) *)
  (*   | s -[ ℓ ]-> tr => Some (s,Some ℓ) *)
  (*   end. *)

  (* Lemma ltl_now_adequacy P (tr : trace S L) : *)
  (*   (⊢ ↓ P) → P $ get_state tr. *)
  (* Proof. *)
  (*   ltl_unseal. intros [HP]. *)
  (*   assert (ltl_now_def P tr) as HP'. *)
  (*   { apply HP. unseal. done. } *)
  (*   revert HP'. destruct tr as [[]|]; by inversion 1. *)
  (* Qed. *)

  (* Lemma ltl_eventually_now_adequacy P (tr : trace S L) : *)
  (*   (⊢ ◊ ↓ P) → ∃ n, P $ get_state $ after n tr. *)
  (* Proof. *)
  (*   intros H. *)
  (*   apply (ltl_eventually_adequacy _ tr) in H as [n HP]. *)
  (*   exists n. *)
  (*   revert HP. ltl_unseal. *)
  (*   destruct (after n tr) as [[]|]; by inversion 1. *)
  (* Qed. *)

  (* Lemma ltl_always_adequacy P (tr : trace S L) : *)
  (*   (⊢ □ P) → ∀ n, P $ after n tr. *)
  (* Proof. *)
  (*   ltl_unseal. intros HP. *)
  (*   assert (ltl_always_def P tr) as HP'. *)
  (*   { apply HP. unseal. done. } *)
  (*   clear HP. *)
  (*   intros n. *)
  (*   revert tr HP'. *)
  (*   induction n; intros tr HP'. *)
  (*   { simpl. by inversion HP'. } *)
  (*   simpl. *)
  (*   inversion HP'; [done|done|]. *)
  (*   simplify_eq. *)
  (*   apply IHn. done. *)
  (* Qed. *)

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

  Lemma excl_false (P : ltl_prop) :
    P ∧ ¬ P ⊢ False.
  Proof.
    constructor. unseal.
    intros tr [H1 H2].
    by apply H2.
  Qed.

  Lemma ltl_not_not (P :ltl_prop) :
    P ⊢ ¬ ¬ P.
  Proof.
    constructor.
    intros tr HP.
    unseal.
    intros H1. apply H1. done.
  Qed.

  Lemma foo (P Q : ltl_prop) :
    (⊢ P → Q) → (P ⊢ Q).
  Proof. iIntros (HPQ) "HP". by iApply HPQ. Qed.

  Lemma bar (P Q : ltl_prop) :
    (P ⊢ Q) → (⊢ P → Q).
  Proof. iIntros (HPQ) "HP". by rewrite HPQ. Qed.

  (** ltl_next lemmas *)

  (* N○ *)
  Lemma ltl_next_taut (P : ltl_prop) :
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
  Lemma ltl_next_mono_strong (P Q : ltl_prop) :
    ○ (P → Q) ⊢ ○ P → ○ Q.
  Proof.
    constructor. ltl_unseal. unseal.
    intros tr HPQ HP.
    inversion HP; inversion HPQ; simplify_eq; econstructor; naive_solver.
  Qed.

  Lemma ltl_next_or_r (P Q : ltl_prop) :
    ○ (P ∨ Q) ⊢ (○ P) ∨ (○ Q).
  Proof.
    ltl_unseal. unseal. constructor.
    intros tr. inversion 1; simplify_eq.
    + inversion H0; simplify_eq; [left|right]; by econstructor.
    + inversion H0; simplify_eq; [left|right]; by econstructor.
    + inversion H0; simplify_eq; [left|right]; by econstructor.
  Qed.

  (** ltl_until lemmas *)

  Lemma ltl_until_intro (P Q : ltl_prop) :
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

  Lemma ltl_until_ind (P Q R : ltl_prop) :
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

  Lemma ltl_until_mono (P1 P2 Q1 Q2 : ltl_prop) :
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

  Lemma ltl_until_idemp (P Q : ltl_prop) :
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

  Lemma ltl_until_and (P Q1 Q2 : ltl_prop) :
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

  (* Lemma baz (tr1 tr2 : trace S L) (H : trace_maximal Rel tr1) : *)
  (*   tr1 = tr2 → *)
  (*   (∃ (H' : trace_maximal Rel tr2), Trace _ _ _ tr1 H = Trace _ _ _ tr2 H'). *)

  Lemma ltl_until_next_comm (P Q : ltl_prop) :
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

  (* Lemma ltl_until_and_r (P1 P2 Q1 Q2 : ltl_prop) : *)
  (*   P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ ((P1 ∧ P2) ∪ (Q1 ∧ P2 ∪ Q2)) ∨ ((P1 ∧ P2) ∪ (P1 ∪ Q1 ∧ Q2)). *)
  (* Proof. Admitted. *)
  (*   constructor. *)
  (*   unseal. *)
  (*   intros tr [HPQ1 HPQ2]. *)
  (*   rewrite ltl_untilI in HPQ1. *)
  (*   rewrite ltl_untilI in HPQ2. *)
  (*   destruct HPQ1 as (n&trPQ1&HtrPQ1&HP1&HQ1). *)
  (*   destruct HPQ2 as (m&trPQ2&HtrPQ2&HP2&HQ2). *)
  (*   destruct (decide (n < m)). *)
  (*   { left. *)
  (*     rewrite ltl_untilI. *)
  (*     exists n, trPQ1. *)
  (*     split; [done|]. *)
  (*     split. *)
  (*     { intros. split; [by eapply HP1|eapply HP2; [|done]]. lia. } *)
  (*     split; [done|]. *)
  (*     rewrite ltl_untilI. *)
  (*     assert (∃ k, m = k+n) as [k ->]. *)
  (*     { exists (m-n). lia. } *)
  (*     exists k,trPQ2. *)
  (*     split. *)
  (*     { rewrite after_sum in HtrPQ2. *)
  (*       rewrite HtrPQ1 in HtrPQ2. *)
  (*       done. } *)
  (*     split; [|done]. *)
  (*     intros. eapply (HP2 (i+n)). *)
  (*     { lia. } *)
  (*     rewrite after_sum. rewrite HtrPQ1. done. } *)
  (*   right. *)
  (*   rewrite ltl_untilI. *)
  (*   exists m, trPQ2. *)
  (*   split; [done|]. *)
  (*   split. *)
  (*   { intros. split; [eapply HP1; [|done]|by eapply HP2]. lia. } *)
  (*   split; [|done]. *)
  (*   rewrite ltl_untilI. *)
  (*   assert (∃ k, n = k+m) as [k ->]. *)
  (*   { exists (n-m). lia. } *)
  (*   exists k, trPQ1. *)
  (*   split. *)
  (*   { rewrite after_sum in HtrPQ1. *)
  (*     rewrite HtrPQ2 in HtrPQ1. *)
  (*     done. } *)
  (*   split. *)
  (*   { intros. eapply (HP1 (i+m)). *)
  (*     { lia. } *)
  (*     rewrite after_sum. rewrite HtrPQ2. done. } *)
  (*   done. *)
  (* Qed. *)

  (* Maybe make this the main lemma *)
  (* Lemma ltl_until_and_r' (P1 P2 Q1 Q2 : ltl_prop) : *)
  (*   P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ (P1 ∧ P2) ∪ ((Q1 ∧ P2 ∪ Q2) ∨ ((P1 ∪ Q1 ∧ Q2))). *)
  (* Proof. *)
  (*   rewrite ltl_until_and_r. *)
  (*   apply or_elim. *)
  (*   - apply ltl_until_mono; [done|]. apply or_intro_l. *)
  (*   - apply ltl_until_mono; [done|]. apply or_intro_r. *)
  (* Qed. *)

  (* TODO: Might not really need this lemma, as [ltl_until_and_r is strictly stronger. *)
  (* Lemma ltl_eventually_and_r (P Q : ltl_prop) : *)
  (*   ◊ P ∧ ◊ Q ⊢ ◊ (P ∧ ◊ Q) ∨ ◊ (◊ P ∧ Q). *)
  (* Proof. by rewrite ltl_until_and_r !ltl_until_eventually. Qed. *)

  (** ltl_always lemmas *)

  Lemma ltl_always_taut (P : ltl_prop) :
    (⊢ P) → (⊢ □ P).
  Proof.
    intros [HP].
    constructor. ltl_unseal. intros tr _. revert tr.
    cofix IH.
    intros tr.
    destruct tr as [[[]|]].
    { econstructor.
      - apply HP; unseal. done.
      - apply HP; unseal. done. }
    - econstructor.
      + apply HP. unseal. done.
      + done.
    - econstructor.
      apply HP. unseal. done.
    Unshelve. all: eauto.
    { apply trace_maximal_empty. } 
    { inversion tr_wf0. done. }
  Qed.

  Lemma ltl_always_intro (P : ltl_prop) :
    □(P → ○ P) ⊢ P → □P.
  Proof.
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

  Lemma ltl_always_elim (P : ltl_prop) :
    (□P) ⊢ P.
  Proof.
    constructor. ltl_unseal. intros tr Htr. 
    inversion Htr; simplify_eq; try done. 
  Qed.

  Lemma ltl_always_mono_strong (P Q : ltl_prop) :
    □ (P → Q) ⊢ □ P → □ Q.
  Proof. 
    constructor. ltl_unseal. unseal.
    cofix IH.
    intros tr Htr HP.
    inversion Htr; simplify_eq; inversion HP; simplify_eq.
    { econstructor. by apply H. }
    - econstructor.
      + apply H. done.
      + apply H0. done.
    - econstructor.
      + apply H. done.
      + eapply IH; done.
  Qed.

  (* TODO: Check: Needs to be axiom? *)
  Lemma ltl_always_idemp (P : ltl_prop) :
    (□ P) ⊣⊢ (□ □ P).
  Proof.
    constructor.
    split.
    - ltl_unseal.
      revert tr. cofix IH.
      intros tr Htr.
      inversion Htr; simplify_eq.
      + econstructor. done.
      + econstructor.
        * done.
        * econstructor. done.
      + econstructor.
        * done.
        * apply IH. done.
    - ltl_unseal.
      intros Htr.
      inversion Htr; simplify_eq.
      + done.
      + done.
      + done.
   Unshelve. done.
  Qed.

  Lemma ltl_always_next (P : ltl_prop) :
    □ P ⊢ ○ □ P.
  Proof.
    constructor. ltl_unseal. intros tr Halways.
    destruct tr as [[[]|]]; inversion Halways.
    - econstructor. econstructor. done.
    - econstructor. done.
    - econstructor. done.
      Unshelve. done.
  Qed.

  Lemma ltl_always_next_comm (P : ltl_prop) :
    □ ○ P ⊢ ○ □ P.
  Proof.
    constructor. ltl_unseal. intros tr Halways.
    destruct tr as [[[]|]].
    - econstructor. inversion Halways. inversion H4. inversion H5. econstructor. done.
    - assert (trace_maximal Rel (Some r)) as Hwf.
      { inversion tr_wf0. done. }
      econstructor.
      
      instantiate (1:=Hwf). 
      (* inversion Halways. simplify_eq. clear H8 H6. *)
      (* revert s ℓ r tr_wf0 Halways H0 H1 H2 H4 H9. cofix IH. *)
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
    - inversion Halways. inversion H. econstructor. econstructor. done.
      Unshelve.
      all: eauto.
      { constructor. }
      { inversion Hwf. done. }
  Qed.

  (** LTL Now (TBD) *)

  (* Lemma ltl_now_false (P Q : option (S* option L) → Prop) : *)
  (*   (∀ osl, P osl → Q osl → False) → ↓ P -∗ ↓ Q -∗ False. *)
  (* Proof. unseal. ltl_unseal. *)
  (*        intros HPQ. constructor. *)
  (*        intros tr _ HP HQ. *)
  (*        destruct tr as [[]|]; eapply (HPQ); simpl in *. *)
  (*        - by inversion HP. *)
  (*        - by inversion HQ. *)
  (*        - by inversion HP. *)
  (*        - by inversion HQ. *)
  (*        - by inversion HP. *)
  (*        - by inversion HQ. *)
  (* Qed. *)

  (* Lemma ltl_now_mono P Q : *)
  (*   (∀ osl, P osl → Q osl) → ↓ P ⊢ (↓ Q):ltl_prop. *)
  (* Proof. *)
  (*   intros HPQ. *)
  (*   ltl_unseal. constructor. *)
  (*   intros [[]|]; inversion 1; try constructor; by apply HPQ. *)
  (* Qed. *)

  (** LTL Exists (TBD) *)

  Lemma ltl_next_exists {A} (P : A → ltl_prop) :
    (○ ∃ x, P x)%I ⊢ ∃ x, ○ P x.
  Proof.
    unseal. ltl_unseal.
    constructor. intros tr Hnext. inversion Hnext.
    - simplify_eq. destruct H as [a H]. exists a. econstructor. apply H.
    - simplify_eq. destruct H as [a H]. exists a. econstructor. apply H.
    - simplify_eq. destruct H as [a H]. exists a. econstructor. apply H.
  Qed.

  (** DERIVED RULES *)

  Lemma ltl_next_mono (P Q : ltl_prop) :
    (P ⊢ Q) → (○ P ⊢ ○ Q).
  Proof.
    intros HPQ.
    apply foo.
    rewrite -ltl_next_mono_strong.
    apply ltl_next_taut.
    apply bar.
    apply HPQ.
  Qed.

  Lemma ltl_next_and (P Q : ltl_prop) :
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

  Lemma ltl_next_or (P Q : ltl_prop) :
    (○ P) ∨ (○ Q) ⊣⊢ ○ (P ∨ Q).
  Proof.
    apply bi.equiv_entails_2.
    - apply bi.or_elim.
      + apply ltl_next_mono. apply bi.or_intro_l.
      + apply ltl_next_mono. apply bi.or_intro_r.
    - apply ltl_next_or_r.
  Qed.

  Lemma ltl_until_intro_now (P Q : ltl_prop) :
    Q ⊢ P ∪ Q.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_until_intro_next (P Q : ltl_prop) :
    P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof. rewrite -{2}ltl_until_intro. apply bi.or_intro_r. Qed.

  (* TODO: Is this needed? *)
  Lemma ltl_until_unfold (P Q : ltl_prop) :
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

  Lemma ltl_eventually_intro (P : ltl_prop) :
    P ∨ ○ ◊ P ⊢ ◊ P.
  Proof.
    rewrite -{2}(ltl_until_intro True P).
    iIntros "[HP|HP]".
    { by iLeft. }
    iRight. by iFrame.
  Qed.

  Lemma ltl_eventually_intro_now (P : ltl_prop) :
    P ⊢ ◊ P.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_eventually_intro_next (P : ltl_prop) :
    (○ P) ⊢ (◊ P).
  Proof. rewrite -ltl_eventually_intro. 
         etrans; [|apply bi.or_intro_r]. apply ltl_next_mono.
         apply ltl_eventually_intro_now.
  Qed.

  Lemma ltl_eventually_mono (P Q : ltl_prop) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof. by apply ltl_until_mono. Qed.

  Lemma ltl_eventually_and (P Q : ltl_prop) :
    (◊ (P ∧ Q)) ⊢ (◊ P) ∧ (◊ Q).
  Proof. by rewrite -ltl_until_and. Qed.

  Lemma ltl_eventually_next_comm (P : ltl_prop) :
    (◊ ○ P) ⊣⊢ (○ ◊ P).
  Proof.
    rewrite -ltl_until_next_comm.
    apply bi.equiv_entails_2.
    - apply ltl_until_mono; [|done]. by apply ltl_next_taut.
    - apply ltl_until_mono; [|done]. eauto.
  Qed.

  Lemma ltl_eventually_idemp (P : ltl_prop) :
    (◊◊P) ⊣⊢ (◊P).
  Proof. apply ltl_until_idemp. Qed.

  Lemma ltl_eventually_next (P : ltl_prop) :
    (◊ ○ P) ⊢ (◊ P).
  Proof.
    rewrite <-(ltl_eventually_idemp P).
    apply ltl_eventually_mono.
    apply ltl_eventually_intro_next.
  Qed.

  Lemma ltl_next_eventually (P : ltl_prop) :
    (○ ◊ P) ⊢ (◊ P).
  Proof. rewrite -{2}ltl_eventually_next ltl_eventually_next_comm. done. Qed.

  Lemma ltl_until_eventually_equiv (P : ltl_prop) :
    (True ∪ P) ⊣⊢ (◊ P).
  Proof. done. Qed.

  Lemma ltl_until_eventually (P Q : ltl_prop) :
    (P ∪ Q) ⊢ (◊ Q).
  Proof. apply ltl_until_mono; by eauto. Qed.

  Lemma ltl_eventually_ind (P Q : ltl_prop) :
    (P ⊢ Q) →
    ((○ ◊ P) ∧ ○ Q ⊢ Q) →
    ◊ P ⊢ Q.
  Proof.
    intros. apply ltl_until_ind; [done|].
    rewrite -{2}H0.
    iIntros "(?&?&?)". iFrame.
  Qed.

  Lemma ltl_always_mono (P Q : ltl_prop) :
    (P ⊢ Q) → (□P) ⊢ (□Q).
  Proof.
    intros HPQ.
    iIntros "HP". iApply (ltl_always_mono_strong with "[] HP").
    iApply ltl_always_taut. iApply HPQ.
  Qed.

  Lemma ltl_always_and (P Q : ltl_prop) :
    (□ (P ∧ Q))%I ⊣⊢ (□ P) ∧ (□ Q).
  Proof.
    apply bi.equiv_entails_2.
    - apply bi.and_intro.
      + apply ltl_always_mono. apply bi.and_elim_l.
      + apply ltl_always_mono. apply bi.and_elim_r.
    - apply bi.impl_elim_r'.
      rewrite -ltl_always_mono_strong.
      apply foo.
      rewrite -ltl_always_mono_strong.
      apply ltl_always_taut.
      eauto.
  Qed.

  Lemma ltl_always_eventually (P : ltl_prop) :
    □ P ⊢ ◊ P.
  Proof. rewrite ltl_always_elim. rewrite -ltl_eventually_intro_now. done. Qed.

  Lemma ltl_next_always_combine (P Q : ltl_prop) :
    (□ P ∧ ○ Q) ⊢ (○ (Q ∧ □ P)).
  Proof.
    rewrite bi.and_comm.
    rewrite {1}ltl_always_next. rewrite ltl_next_and. 
    done.
  Qed.

  Lemma baz (P Q : ltl_prop) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. done. Qed.

  Lemma ltl_eventually_always_combine (P Q : ltl_prop) :
    (□ P ∧ ◊Q) ⊢ (◊ (Q ∧ □ P)).
  Proof.
    apply bi.impl_elim_r'.
    apply ltl_until_ind.
    { iIntros "HQ HP". iApply ltl_eventually_intro_now. iFrame. }
    iIntros "[H1 [H2 _]] HP".
    iDestruct (ltl_next_always_combine with "[HP H2]") as "#H".
    { iSplitL "HP"; by done. }
    iDestruct "H" as "-#H".
    iClear "HP".
    iEval (rewrite -ltl_eventually_idemp).
    iEval (rewrite -ltl_eventually_intro_next).
    iStopProof. rewrite !baz. rewrite !ltl_next_and.
    apply ltl_next_mono.
    iIntros "(H1&H2&[_ H3])". by iApply "H2".
  Qed.

  Lemma ltl_until_always_combine (P Q R : ltl_prop) :
    (□ P ∧ (Q ∪ R)) ⊢ ((□ P ∧ Q) ∪ ((□ P) ∧ R)).
  Proof.
    apply bi.impl_elim_r'.
    apply ltl_until_ind.
    { iIntros "HQ HP". iApply ltl_until_intro_now. iFrame. }
    iIntros "[H1 [H2 H3]] HP".
    iDestruct (ltl_next_always_combine with "[HP H2]") as "#H".
    { iSplitL "HP"; by done. }
    iDestruct "H" as "-#H".
    iEval (rewrite -ltl_until_idemp).
    iEval (rewrite -ltl_until_intro_next).
    iFrame.
    iStopProof. rewrite !baz. rewrite !ltl_next_and.
    apply ltl_next_mono.
    iIntros "(H1&H2&[_ H3])".
    rewrite ltl_until_idemp.
    by iApply "H2".
  Qed.

  Lemma ltl_not_always_eventually_not (P : ltl_prop) :
     (□ P) ⊢ ¬ ◊ ¬ P.
  Proof.
    constructor. ltl_unseal. unseal.
    intros tr Htr Htr'.
    induction Htr'.
    { apply H. apply ltl_always_elim. ltl_unseal. done. }
    { apply H0. inversion Htr. done. }
    { inversion Htr. simplify_eq.
      apply IHHtr'. done. }
  Qed.
  
  Lemma ltl_not_eventually_always_not (P : ltl_prop) :
     (◊ P) ⊢ ¬ □ ¬ P.
  Proof.
    constructor. ltl_unseal. unseal.
    intros tr Htr Htr'.
    induction Htr.
    { pose proof (ltl_always_elim).
      revert H0. ltl_unseal. intros H0.
      apply H0 in Htr'. apply Htr'. done. }
    { inversion Htr'. subst. apply H10. done. }
    { inversion Htr'. simplify_eq.
      apply IHHtr. done. }
  Qed.

  (** Proofmode stuff *)

  Lemma bi_persistently_id (P : ltl_prop) :
    <pers> P ⊣⊢ P.
  Proof. constructor. intros tr. unseal. done. Qed.

  Lemma bi_intuitionistically_id (P : ltl_prop) :
    □^ P ⊣⊢ P.
  Proof.
    rewrite -{2}(bi_persistently_id P).
    iSplit; by iIntros "H".
  Qed.

  Lemma bi_sep_and (P Q : ltl_prop) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. constructor. intros tr. unseal. done. Qed.
  Lemma bi_wand_impl (P Q : ltl_prop) :
    (P -∗ Q) ⊣⊢ (P → Q).
  Proof. constructor. intros tr. unseal. done. Qed.

End ltl_lemmas.

Section ltl_proofmode.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation ltl_prop := (ltl_prop S L Rel).

  Import ltl_prop.

  Global Instance into_wand_next p (P Q R : ltl_prop) :
    IntoWand p p R P Q → IntoWand p p (○ R)%I (○ P)%I (○ Q)%I.
  Proof.
    rewrite /IntoWand.
    destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros HR. iIntros "HR HP".
      iAssert (○ (R ∧ P))%I with "[HR HP]" as "H".
      { iApply ltl_next_and. iSplit; iFrame. }
      iApply (ltl_next_mono with "H").
      rewrite HR.
      iIntros "[HPQ HP]". by iApply "HPQ".
    - intros HR. iIntros "HR HP".
      iAssert (○ (R ∧ P))%I with "[HR HP]" as "H".
      { iApply ltl_next_and. iSplit; iFrame. }
      iApply (ltl_next_mono with "H").
      rewrite HR.
      iIntros "[HPQ HP]". by iApply "HPQ".
  Qed.
  Global Instance into_wand_always p (P Q R : ltl_prop) :
    IntoWand p p R P Q → IntoWand p p (□ R)%I (□ P)%I (□ Q)%I.
  Proof.
    rewrite /IntoWand.
    destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros HR.
      etrans.
      { iApply ltl_always_mono. apply HR. }
      iIntros "HPQ HP".
      iAssert (□ ((P -∗ Q) ∧ P))%I with "[HPQ HP]" as "HP'".
      { iApply ltl_always_and. by iSplit. }
      iStopProof. eapply ltl_always_mono.
      iIntros "[HPQ HP]". by iApply "HPQ".
    - intros HR.
      etrans.
      { iApply ltl_always_mono. apply HR. }
      iIntros "HPQ HP".
      iAssert (□ ((P -∗ Q) ∧ P))%I with "[HPQ HP]" as "HP'".
      { rewrite ltl_always_and. by iSplit. }
      iStopProof. eapply ltl_always_mono.
      iIntros "[HPQ HP]". by iApply "HPQ".
  Qed.

  Global Instance into_and_always b (P Q1 Q2 : ltl_prop) :
    IntoAnd b P Q1 Q2 →
    IntoAnd b (□ P)%I (□ Q1)%I (□ Q2)%I.
  Proof.
    destruct b; simpl.
    - rewrite /IntoAnd. simpl. rewrite !bi_intuitionistically_id.
      intros HPQ.
      rewrite -(ltl_always_and Q1 Q2).
      by eapply ltl_always_mono.
    - rewrite /IntoAnd. simpl.
      intros HPQ.
      rewrite -(ltl_always_and Q1 Q2).
      by eapply ltl_always_mono.
  Qed.

  Global Instance into_sep_always (P Q1 Q2 : ltl_prop) :
    IntoSep P Q1 Q2 →
    IntoSep (□ P)%I (□ Q1)%I (□ Q2)%I.
  Proof.
    rewrite /IntoSep.
    simpl. rewrite !bi_sep_and.
    intros HPQ.
    rewrite -(ltl_always_and Q1 Q2).
    by eapply ltl_always_mono.
  Qed.

  Global Instance into_and_eventually b (P Q1 Q2 : ltl_prop) :
    IntoAnd b P Q1 Q2 →
    IntoAnd b (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof.
    destruct b; simpl.
    - rewrite /IntoAnd. simpl. rewrite !bi_intuitionistically_id.
      intros HPQ.
      rewrite -ltl_eventually_and.
      by eapply ltl_eventually_mono.
    - rewrite /IntoAnd. simpl.
      intros HPQ.
      rewrite -ltl_eventually_and.
      by eapply ltl_eventually_mono.
  Qed.

  Global Instance into_sep_eventually (P Q1 Q2 : ltl_prop) :
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

  Global Instance elim_modal_always p (P Q : ltl_prop) :
    @ElimModal ltlI True%type p p (□ P)%I P Q Q.
  Proof.
    rewrite /ElimModal; destruct p; simpl; [rewrite !bi_intuitionistically_id|].
    - intros _. iIntros "[HP HPQ]". iApply "HPQ". by rewrite ltl_always_elim.
    - intros _. iIntros "[HP HPQ]". iApply "HPQ". by rewrite ltl_always_elim.
  Qed.
  Class IntoEventually (P Q : ltl_prop) :=
    into_eventually (p:bool) : □?p P ⊢ ◊ Q.
  Global Arguments IntoEventually _%I _%I : simpl never.
  Global Arguments into_eventually _%I _%I {_}.
  Global Hint Mode IntoEventually ! - : typeclass_instances.

  Global Instance into_eventually_eventually (P : ltl_prop) :
    IntoEventually (◊ P) P.
  Proof.
    rewrite /IntoEventually. intros p.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Global Instance into_eventually_next (P Q : ltl_prop) :
    IntoEventually P Q →
    IntoEventually (○ P) (○ Q).
  Proof.
    rewrite /IntoEventually. intros HPQ p.
    destruct p; simpl.
    - rewrite ltl_eventually_next_comm.
      iIntros "#HP".
      specialize (HPQ true). simpl in HPQ.
      iApply (ltl_next_mono with "HP"). rewrite -HPQ.
      by rewrite bi_intuitionistically_id.
    - rewrite ltl_eventually_next_comm.
      iIntros "#HP".
      specialize (HPQ true). simpl in HPQ.
      iApply (ltl_next_mono with "HP"). rewrite -HPQ.
      by rewrite bi_intuitionistically_id.
  Qed.

  Class IntoNext (P Q : ltl_prop) :=
    into_next (p:bool) : □?p P ⊢ ○ Q.
  Global Arguments IntoNext _%I _%I : simpl never.
  Global Arguments into_next _%I _%I {_}.
  Global Hint Mode IntoNext ! - : typeclass_instances.

  Global Instance into_next_next (P : ltl_prop) :
    IntoNext (○ P) P.
  Proof.
    rewrite /IntoNext. intros p.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Global Instance into_next_and (P1 P2 Q1 Q2 : ltl_prop) :
    IntoNext P1 P2 →
    IntoNext Q1 Q2 →
    IntoNext (P1 ∧ Q1) (P2 ∧ Q2).
  Proof.
    rewrite /IntoNext. intros HP HQ p.
    destruct p; simpl; [rewrite bi_intuitionistically_id|].
    - rewrite -ltl_next_and.
      rewrite -(HP true).
      rewrite -(HQ true). simpl.
      rewrite !bi_intuitionistically_id. done.
    - rewrite -ltl_next_and.
      rewrite -(HP true).
      rewrite -(HQ true). simpl.
      rewrite !bi_intuitionistically_id. done.
  Qed.

  Global Instance into_next_eventually (P Q : ltl_prop) :
    IntoNext P Q →
    IntoNext (◊ P) (◊ Q).
  Proof.
    rewrite /IntoNext. intros HPQ p.
    destruct p; simpl; [rewrite bi_intuitionistically_id|].
    - rewrite -ltl_eventually_next_comm.
      eapply ltl_eventually_mono.
      specialize (HPQ true). simpl in HPQ.
      rewrite bi_intuitionistically_id in HPQ.
      done.
    - rewrite -ltl_eventually_next_comm.
      eapply ltl_eventually_mono.
      specialize (HPQ true). simpl in HPQ.
      rewrite bi_intuitionistically_id in HPQ.
      done.
  Qed.

  Global Instance into_next_always (P : ltl_prop) :
    IntoNext (□ P) (□ P) | 1.
  Proof.
    rewrite /IntoNext. intros p.
    destruct p; simpl; [rewrite bi_intuitionistically_id|].
    - apply ltl_always_next.
    - apply ltl_always_next.
  Qed.

  Global Instance into_next_always' (P : ltl_prop) :
    IntoNext (□ ○ P) (□ P) | 0.
  Proof.
    rewrite /IntoNext. intros p.
    destruct p; simpl; [rewrite bi_intuitionistically_id|].
    - apply ltl_always_next_comm.
    - apply ltl_always_next_comm.
  Qed.

  Lemma modality_next_mixin : modality_mixin (ltl_next)
    (MIEnvTransform IntoNext) (MIEnvTransform IntoNext).
  Proof.
    split; simpl; eauto.
    - split.
      + intros P Q H. iIntros "H".
        rewrite /IntoNext in H. iDestruct (H true with "H") as "H".
        iApply (ltl_next_mono with "H").
        by rewrite bi_intuitionistically_id.
      + iIntros (P Q) "[HP HQ]".
        iApply ltl_next_and. by iSplit.
    - intros P Q H. iIntros "H".
      rewrite /IntoNext in H. iDestruct (H false with "H") as "H".
      by iApply (ltl_next_mono with "H").
    - by apply ltl_next_taut.
    - by apply ltl_next_mono.
    - iIntros (P Q) "[HP HQ]". iApply ltl_next_and. by iSplit.
  Qed.
  Definition modality_next := Modality (@ltl_next S L Rel) modality_next_mixin.
  Global Instance from_modal_next (P : ltl_prop) :
    @FromModal ltlI ltlI _ True%type modality_next (○ P) (○ P) (P).
  Proof. rewrite /FromModal /=. done. Qed.

  Class IntoAlways (P Q : ltl_prop) :=
    into_always (p:bool) : □?p P ⊢ □ Q.
  Global Arguments IntoAlways _%I _%I : simpl never.
  Global Arguments into_always _%I _%I {_}.
  Global Hint Mode IntoAlways ! - : typeclass_instances.

  Global Instance into_always_always (P : ltl_prop) :
    IntoAlways (□ P) (□ P).
  Proof.
    rewrite /IntoAlways. intros p.
    destruct p; simpl; [rewrite bi_intuitionistically_id|];
      by rewrite <-ltl_always_idemp.
  Qed.

  Lemma modality_always_mixin : modality_mixin (ltl_always)
    (MIEnvTransform IntoAlways) (MIEnvTransform IntoAlways).
  Proof.
    split; simpl; eauto.
    - split.
      + intros P Q H. iIntros "H".
        rewrite /IntoAlways in H. iDestruct (H true with "H") as "H".
        iApply (ltl_always_mono with "H").
        by rewrite bi_intuitionistically_id.
      + iIntros (P Q) "[HP HQ]".
        iApply ltl_always_and. by iSplit.
    - intros P Q H. iIntros "H".
      rewrite /IntoAlways in H. iDestruct (H false with "H") as "H".
      by iApply (ltl_always_mono with "H").
    - iIntros "_". iApply ltl_always_taut. done.
    - by apply ltl_always_mono.
    - iIntros (P Q) "[HP HQ]". iApply ltl_always_and. by iSplit.
  Qed.

  Definition modality_always := Modality (@ltl_always S L Rel) modality_always_mixin.
  Global Instance from_modal_always (P : ltl_prop) :
    @FromModal ltlI ltlI _ True%type modality_always (□ P) (□ P) (P).
  Proof. rewrite /FromModal /=. done. Qed.

  Global Instance ltl_next_combine (P Q : ltl_prop) :
    CombineSepAs (○ P) (○ Q) (○ (P ∧ Q)).
  Proof. by rewrite /CombineSepAs bi_sep_and ltl_next_and. Qed.

  Global Instance ltl_next_always_combine' (P Q : ltl_prop) :
    CombineSepAs (○ P) (□ Q) (○ (P ∧ □ Q)).
  Proof.
    rewrite /CombineSepAs.
    rewrite bi.sep_comm.
    apply ltl_next_always_combine.
  Qed.

  Global Instance ltl_eventually_always_combine' (P Q : ltl_prop) :
    CombineSepAs (◊ P) (□ Q) (◊ (P ∧ □ Q)).
  Proof.
    rewrite /CombineSepAs.
    rewrite bi.sep_comm.
    apply ltl_eventually_always_combine.
  Qed.

  Global Instance ltl_until_always_combine' (P Q R : ltl_prop) :
    CombineSepAs (P ∪ Q) (□ R) ((□ R ∧ P) ∪ (□ R ∧ Q)) | 100.
  Proof.
    rewrite /CombineSepAs.
    rewrite bi.sep_comm.
    apply ltl_until_always_combine.
  Qed.

  (* Global Instance ltl_until_combine (P1 P2 Q1 Q2 : ltl_prop) : *)
  (*   CombineSepAs (P1 ∪ Q1) (P2 ∪ Q2) ((P1 ∧ P2) ∪ (Q1 ∧ (P2 ∪ Q2)) ∨ (P1 ∧ P2) ∪ ((P1 ∪ Q1) ∧ Q2)). *)
  (* Proof. rewrite /CombineSepAs. apply ltl_until_and_r. Qed. *)

  (* Global Instance ltl_until_combine' (P1 P2 Q1 Q2 : ltl_prop) : *)
  (*   CombineSepAs (P1 ∪ Q1) (P2 ∪ Q2) ((P1 ∧ P2) ∪ ((Q1 ∧ (P2 ∪ Q2)) ∨ ((P1 ∪ Q1) ∧ Q2))). *)
  (* Proof. rewrite /CombineSepAs. apply ltl_until_and_r'. Qed. *)

End ltl_proofmode.

Tactic Notation "iModEv" "with" constr(pat) :=
  iApply ltl_eventually_idemp; iApply (ltl_eventually_mono with pat); try iIntros pat.
Tactic Notation "iModEv" "with" constr(pat1) "as" constr(pat2) :=
  iApply ltl_eventually_idemp; iApply (ltl_eventually_mono with pat1); try iIntros pat2.
