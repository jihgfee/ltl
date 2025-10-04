From iris.proofmode Require Import proofmode.

Axiom ExcludedMiddle : ∀ (P : Prop), P ∨ ¬ P.

Delimit Scope trace_scope with trace.

CoInductive trace (S L: Type) :=
| tr_singl (s: S)
| tr_cons (s: S) (ℓ: L) (r: trace S L).
Bind Scope trace_scope with trace.

Arguments tr_singl {_} {_}, _.
Arguments tr_cons {_} {_} _ _ _%trace.
Notation "⟨ s ⟩" := (tr_singl s) : trace_scope.
Notation "s -[ ℓ ]->  r" := (tr_cons s ℓ r) (at level 33) : trace_scope.
Open Scope trace.

Section trace.
  Context {St L: Type}.

  Fixpoint after (n: nat) (t: trace St L) : option (trace St L):=
    match n with
    | 0 => Some t
    | Datatypes.S n =>
        match t with
        | ⟨ s ⟩ => None
        | s -[ ℓ ]-> xs => after n xs
        end
    end.

  Lemma after_sum m: forall k (tr: trace St L),
    after (k+m) tr =
    match after m tr with
    | None => None
    | Some tr' => after k tr'
    end.
  Proof.
    induction m.
    - intros k tr. by have ->: k+0=k by lia.
    - intros k tr. simpl.
      have -> /=: (k + S m) = S (k+m) by lia.
      destruct tr as [s|s l r]; simpl; auto.
  Qed.

  Lemma after_sum' m: forall k (tr: trace St L),
    after (k+m) tr =
    match after k tr with
    | None => None
    | Some tr' => after m tr'
    end.
  Proof. intros. rewrite Nat.add_comm. apply after_sum. Qed.

  Definition pred_at (tr: trace St L) (n: nat) (P: St -> option L -> Prop): Prop :=
    match after n tr with
    | None => False
    | Some ⟨s⟩ => P s None
    | Some (s -[ℓ]-> _) => P s (Some ℓ)
    end.

End trace.

Definition ltl_prop S L := trace S L → Prop.

Bind Scope bi_scope with ltl_prop.
Bind Scope bi_scope with trace.

Section cofe.
  Context {S L : Type}.

  Notation ltl_prop := (@ltl_prop S L).
  
  Inductive ltl_prop_equiv' (P Q : ltl_prop) : Prop :=
    { ltl_prop_in_equiv : ∀ tr, P tr ↔ Q tr }.
  Local Instance ltl_prop_equiv : Equiv ltl_prop := ltl_prop_equiv'.
  Local Instance heapProp_equivalence : Equivalence (≡@{ltl_prop}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure ltl_PropO := discreteO ltl_prop.
End cofe.

Section ltl_constructors.
  Context {S L : Type}.
  Notation ltl_prop := (ltl_prop S L).
  Implicit Type P Q : ltl_prop.

  Inductive ltl_entails (P Q : ltl_prop) : Prop :=
    { ltl_in_entails : ∀ tr, P tr → Q tr }.
  
  (* Primitive operators *)
  Local Definition ltl_pure_def (P : Prop) : ltl_prop :=
    λ tr, P.
  Local Definition ltl_pure_aux : seal (@ltl_pure_def).
  Proof. by eexists. Qed.
  Definition ltl_pure := unseal ltl_pure_aux.
  Local Definition ltl_pure_unseal :
    @ltl_pure = @ltl_pure_def := seal_eq ltl_pure_aux.

  Local Definition ltl_or_def (P Q : ltl_prop) : ltl_prop :=
    λ tr, P tr ∨ Q tr.
  Local Definition ltl_or_aux : seal (@ltl_or_def).
  Proof. by eexists. Qed.
  Definition ltl_or := unseal ltl_or_aux.
  Local Definition ltl_or_unseal :
    @ltl_or = @ltl_or_def := seal_eq ltl_or_aux.  

  Local Definition ltl_and_def (P Q : ltl_prop) : ltl_prop :=
    λ tr, P tr ∧ Q tr.
  Local Definition ltl_and_aux : seal (@ltl_and_def).
  Proof. by eexists. Qed.
  Definition ltl_and := unseal ltl_and_aux.
  Local Definition ltl_and_unseal :
    @ltl_and = @ltl_and_def := seal_eq ltl_and_aux.  

  Local Definition ltl_impl_def (P Q : ltl_prop) : ltl_prop :=
    λ tr, P tr → Q tr.
  Local Definition ltl_impl_aux : seal (@ltl_impl_def).
  Proof. by eexists. Qed.
  Definition ltl_impl := unseal ltl_impl_aux.
  Local Definition ltl_impl_unseal :
    @ltl_impl = @ltl_impl_def := seal_eq ltl_impl_aux.  

  Local Definition ltl_forall_def {A} (Ψ : A → ltl_prop) : ltl_prop :=
    λ tr, ∀ (x:A), Ψ x tr.
  Local Definition ltl_forall_aux : seal (@ltl_forall_def).
  Proof. by eexists. Qed.
  Definition ltl_forall {A} := unseal ltl_forall_aux A.
  Local Definition ltl_forall_unseal :
    @ltl_forall = @ltl_forall_def := seal_eq ltl_forall_aux.  

  Local Definition ltl_exist_def {A} (Ψ : A → ltl_prop) : ltl_prop :=
    λ tr, ∃ (x:A), Ψ x tr.
  Local Definition ltl_exist_aux : seal (@ltl_exist_def).
  Proof. by eexists. Qed.
  Definition ltl_exist {A} := unseal ltl_exist_aux A.
  Local Definition ltl_exist_unseal :
    @ltl_exist = @ltl_exist_def := seal_eq ltl_exist_aux.  

  Local Definition ltl_later_def (P : ltl_prop) : ltl_prop := P.
  Local Definition ltl_later_aux : seal (@ltl_later_def).
  Proof. by eexists. Qed.
  Definition ltl_later := unseal ltl_later_aux.
  Local Definition ltl_later_unseal :
    @ltl_later = @ltl_later_def := seal_eq ltl_later_aux.  

  Local Definition ltl_internal_eq_def {A:ofe} (a1 a2 : A) : ltl_prop :=
    λ tr, a1 ≡ a2.
  Local Definition ltl_internal_eq_aux : seal (@ltl_internal_eq_def).
  Proof. by eexists. Qed.
  Definition ltl_internal_eq {A} := unseal ltl_internal_eq_aux A.
  Local Definition ltl_internal_eq_unseal :
    @ltl_internal_eq = @ltl_internal_eq_def := seal_eq ltl_internal_eq_aux.  

End ltl_constructors.

Module ltl_primitive.

Section primitive.
  Context {S L : Type}.
  
  Implicit Type P : ltl_prop S L.

  Definition ltl_unseal :=
    (@ltl_pure_unseal S L, @ltl_and_unseal S L, @ltl_or_unseal S L,
       @ltl_impl_unseal S L, @ltl_forall_unseal S L, @ltl_exist_unseal S L,
         @ltl_later_unseal S L, @ltl_internal_eq_unseal S L).

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
  Lemma entails_po : PreOrder (@ltl_entails S L).
  Proof.
    split.
    - intros P; by split=> i.
    - intros P Q Q' HP HQ; split=> i ?; by apply HQ, HP.
  Qed.
  Lemma entails_anti_symm : AntiSymm (≡) (@ltl_entails S L).
  Proof. intros P Q HPQ HQP; split=> n; by split; [apply HPQ|apply HQP]. Qed.
  Lemma equiv_entails (P Q : ltl_prop S L) : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros HPQ; split; split=> i; apply HPQ.
    - intros [??]. by apply entails_anti_symm.
  Qed.

  (** Non-expansiveness and setoid morphisms *)
  Lemma pure_ne n : Proper (iff ==> dist n) (@ltl_pure S L).
  Proof. intros φ1 φ2 Hφ. by unseal. Qed.
  Lemma and_ne : NonExpansive2 (@ltl_and S L).
  Proof.
    intros n P P' HP Q Q' HQ; unseal; split=> ?.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  Qed.
  Lemma or_ne : NonExpansive2 (@ltl_or S L).
  Proof.
    intros n P P' HP Q Q' HQ; split=> ?.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  Qed.
  Lemma impl_ne : NonExpansive2 (@ltl_impl S L).
  Proof.
    intros n P P' HP Q Q' HQ; split=> ?.
    unseal; split; intros HPQ ?; apply HQ, HPQ, HP; auto with lia.
  Qed.
  Lemma forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@ltl_forall S L A).
  Proof.
     by intros Ψ1 Ψ2 HΨ; unseal; split=> x; split; intros HP a; apply HΨ.
  Qed.
  Lemma exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@ltl_exist S L A).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    unseal; split=> ?; split; intros [a ?]; exists a; by apply HΨ.
  Qed.
  Lemma later_ne : NonExpansive (@ltl_later S L).
  Proof. unseal; intros n P Q HPQ. rewrite /ltl_later_def. done. Qed.

  (** Introduction and elimination rules *)
  Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
  Proof. intros ?. unseal; by split. Qed.
  Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
  Proof. unseal=> HP; split=> n ?. by apply HP. Qed.
  (* Lemma test {A} (φ : A → ltl_prop S L) : ⊢ (∀ a, φ a)%ltl. *)
  Lemma pure_forall_2 {A} (φ : A → Prop) :
    ((∀ a, ⌜ φ a ⌝):ltl_prop S L) ⊢ ⌜ ∀ a, φ a ⌝.
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

  Lemma forall_intro {A} P (Ψ : A → ltl_prop S L) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n ? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → ltl_prop S L} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → ltl_prop S L} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> n ?; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → ltl_prop S L) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΨ; split=> n [a ?]; by apply HΨ with a. Qed.

  (** Later *)
  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof. unseal=> HP; split=>tr. rewrite /ltl_later_def.
         destruct HP as [HP]. apply HP. Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof. unseal; split=> /= HP. done. Qed.

  Lemma later_forall_2 {A} (Φ : A → ltl_prop S L) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; by split. Qed.
  Lemma later_exist_false {A} (Φ : A → ltl_prop S L) :
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
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → ltl_prop S L) :
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

  Definition ltl_emp : ltl_prop S L := ltl_pure True.
  Definition ltl_persistently {S L} (P : ltl_prop S L) : ltl_prop S L := P.
  Definition ltl_plainly {S L} (P : ltl_prop S L) : ltl_prop S L := P.
  
  Local Existing Instance entails_po.

  Lemma ltl_bi_mixin :
    BiMixin
      ltl_entails ltl_emp ltl_pure ltl_and ltl_or ltl_impl
      (@ltl_forall S L) (@ltl_exist S L) ltl_and ltl_impl.
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
      (@ltl_exist S L) ltl_and ltl_persistently.
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
      (@ltl_forall S L) (@ltl_exist S L) ltl_and ltl_persistently ltl_later.
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

Canonical Structure ltlI {S L : Type} : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (ltl_prop S L);
    bi_bi_mixin := ltl_bi_mixin;
    bi_bi_persistently_mixin := ltl_bi_persistently_mixin;
    bi_bi_later_mixin := ltl_bi_later_mixin |}.

Section ltl.
  Context {S L : Type}.

  Global Instance ltl_pure_forall : BiPureForall (@ltlI S L).
  Proof. exact: @pure_forall_2. Qed.

  Global Instance ltl_affine : BiAffine (@ltlI S L) | 0.
  Proof. intros P. exact: pure_intro. Qed.
  (* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)

  Global Instance ltl_persistent (P : ltl_prop S L) : Persistent P.
  Proof. done. Qed.

End ltl.

Global Hint Immediate ltl_affine : core.

(** extra BI instances *)

(** Re-state/export soundness lemmas *)

Module ltl_prop.
Section restate.
  Context {S L : Type}.

  (** We restate the unsealing lemmas so that they also unfold the BI layer. The *)
(*   sealing lemmas are partially applied so that they also work under binders. *)
  Local Lemma ltl_emp_unseal : bi_emp = @ltl_pure_def S L True.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Local Lemma ltl_pure_unseal : bi_pure = @ltl_pure_def S L.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Local Lemma ltl_and_unseal : bi_and = @ltl_and_def S L.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Local Lemma ltl_or_unseal : bi_or = @ltl_or_def S L.
  Proof. by rewrite -ltl_or_unseal. Qed.
  Local Lemma ltl_impl_unseal : bi_impl = @ltl_impl_def S L.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Local Lemma ltl_forall_unseal : @bi_forall _ = @ltl_forall_def S L.
  Proof. by rewrite -ltl_forall_unseal. Qed.
  Local Lemma ltl_exist_unseal : @bi_exist _ = @ltl_exist_def S L.
  Proof. by rewrite -ltl_exist_unseal. Qed.
  Local Lemma ltl_sep_unseal : bi_sep = @ltl_and_def S L.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Local Lemma ltl_wand_unseal : bi_wand = @ltl_impl_def S L.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Local Lemma ltl_persistently_unseal : bi_persistently = @ltl_persistently S L.
  Proof. done. Qed.
  Local Lemma ltl_later_unseal : bi_later = @ltl_later_def S L.
  Proof. by rewrite -ltl_later_unseal. Qed.

  Local Definition ltl_unseal :=
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

  Notation ltl_prop := (ltl_prop S L).

  (* LTL Operators *)
  (* Primitive operators *)
  Local Definition ltl_now_def (P : S → option L → Prop) : ltl_prop :=
    λ tr, pred_at tr 0 P.
  Local Definition ltl_now_aux : seal (@ltl_now_def).
  Proof. by eexists. Qed.
  Definition ltl_now := unseal ltl_now_aux.
  Local Definition ltl_now_unseal :
    @ltl_now = @ltl_now_def := seal_eq ltl_now_aux.

  Local Definition ltl_next_def (P : ltl_prop) : ltl_prop :=
    λ tr, ∃ tr', after 1 tr = Some tr' ∧ P tr'.
  Local Definition ltl_next_aux : seal (@ltl_next_def).
  Proof. by eexists. Qed.
  Definition ltl_next := unseal ltl_next_aux.
  Local Definition ltl_next_unseal :
    @ltl_next = @ltl_next_def := seal_eq ltl_next_aux.

  Inductive ltl_until_def (P Q : ltl_prop) : ltl_prop :=
  | ltl_until_here tr : Q tr -> ltl_until_def P Q tr
  | ltl_until_cons s l tr : P (s -[l]-> tr) → ltl_until_def P Q tr → ltl_until_def P Q (s -[l]-> tr).
  Local Definition ltl_until_aux : seal (@ltl_until_def).
  Proof. by eexists. Qed.
  Definition ltl_until := unseal ltl_until_aux.
  Local Definition ltl_until_unseal :
    @ltl_until = @ltl_until_def := seal_eq ltl_until_aux.

  Notation ltl_eventually P := (ltl_until True P).

  Local Definition ltl_always_def (P:ltl_prop) : ltl_prop := (¬ ltl_eventually (¬ P)).
  Local Definition ltl_always_aux : seal (@ltl_always_def).
  Proof. by eexists. Qed.
  Definition ltl_always := unseal ltl_always_aux.
  Local Definition ltl_always_unseal :
    @ltl_always = @ltl_always_def := seal_eq ltl_always_aux.

End ltl_primitives.

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

  Notation ltl_prop := (ltl_prop S L).

  Local Definition ltl_unseal' :=
    (@ltl_pure_unseal S L, @ltl_and_unseal S L, @ltl_or_unseal S L,
       @ltl_impl_unseal S L, @ltl_forall_unseal S L, @ltl_exist_unseal S L,
         @ltl_later_unseal S L, @ltl_internal_eq_unseal S L,
    @ltl_next_unseal S L, @ltl_now_unseal S L, @ltl_always_unseal S L,
    @ltl_until_unseal S L).

  Ltac ltl_unseal := rewrite !ltl_unseal' /=.

  Import ltl_prop.

  Tactic Notation "unseal_apply" constr(pat) :=
    let H := fresh in
    pose proof pat as H;
    revert H; ltl_unseal; intros H; apply H; clear H.

  Tactic Notation "unseal_eapply" constr(pat) :=
    let H := fresh in
    pose proof pat as H;
    revert H; ltl_unseal; intros H; eapply H; clear H.

  Definition trace_suffix_of (tr1 tr2 : trace S L) : Prop :=
    ∃ n, after n tr2 = Some tr1.

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

  (** ltl_not lemmas *)

  Lemma excl_false (P : ltl_prop) :
    P ∧ ¬ P ⊢ False.
  Proof.
    constructor. unseal.
    intros tr [H1 H2].
    by apply H2.
  Qed.

  Lemma ltl_not_not (P :ltl_prop) :
    P ⊣⊢ ¬ ¬ P.
  Proof.
    constructor.
    split.
    - intros HP.
      unseal.
      intros H1. apply H1. done.
    - unseal.
      intros H1.
      assert (P tr ∨ ¬ P tr).
      { apply ExcludedMiddle. }
      destruct H; [done|].
      exfalso. apply H1. intros H2.
      done.
  Qed.

  Lemma ltl_not_always_eventually_not (P : ltl_prop) :
    (¬ □ P) ⊣⊢ ◊ ¬ P.
  Proof.
    rewrite ltl_always_unseal /ltl_always_def.
    rewrite -ltl_not_not. done.
  Qed.

  (** ltl_next lemmas *)

  Lemma ltl_next_intro (P : ltl_prop) s l (tr : trace S L) :
    P tr → (○ P)%I (s -[l]-> tr).
  Proof. intros ?. ltl_unseal. exists tr. simpl in *. by simplify_eq. Qed.

  Lemma ltl_next_elim (P : ltl_prop) s l tr :
    (○ P)%I (s -[l]-> tr) → P tr.
  Proof. ltl_unseal. inversion 1. naive_solver. Qed.

  Lemma ltl_next_mono (P Q : ltl_prop) :
    (P ⊢ Q) → (○ P ⊢ ○ Q).
  Proof.
    intros [HPQ]. constructor. ltl_unseal.
    intros tr HP. 
    destruct HP as [tr' [Htr' HP]].
    destruct tr; [done|]. simpl in *.
    simplify_eq.
    exists tr'. split; [done|].
    by apply HPQ.
  Qed.

  Lemma ltl_next_and (P Q : ltl_prop) :
    (○ P) ∧ (○ Q) ⊣⊢ ○ (P ∧ Q).
  Proof.
    ltl_unseal. unseal. constructor.
    split.
    - intros [[tr' [Hafter H1]] [tr'' [Hafter' H2]]]. exists tr'.
      split.
      + simplify_eq. done. 
      + simplify_eq. done. 
    - intros [tr' [Hafter [H1 H2]]]. split.
      + exists tr'. done.
      + exists tr'. done.
  Qed.

  (** ltl_until lemmas *)

  Lemma ltl_untilI_alt (P Q : ltl_prop) tr :
    (P ∪ Q)%I tr ↔ (∃ n tr',
                       after n tr = Some tr' ∧
                       (∀ i tr'', i < n → after i tr = Some tr'' → P tr'') ∧
                       (P ∪ Q)%I tr').
  Proof.
    split.
    - ltl_unseal.
      intros Heventually.
      induction Heventually.
      { exists 0, tr. split; [done|].
        split; [|by constructor 1].
        intros. lia. }
      destruct IHHeventually as [n [tr' [Hsuffix [HP HQ]]]].
      exists (Datatypes.S n), tr'.
      repeat split; [done| |done].
      intros.
      destruct i.
      { simpl in *. simplify_eq. done. }
      eapply (HP i); [lia|done].
    - intros [n [tr' [Hafter [HP Htr']]]].
      rewrite ltl_until_unseal.
      rewrite ltl_until_unseal in Htr'.
      revert n tr Hafter HP.
      induction Htr'; intros n tr0 Hafter HP.
      { revert tr tr0 Hafter HP H.
        induction n; intros tr tr0 Hafter HP' HP.
        { simpl in *. simplify_eq. by constructor. }
        destruct tr0; [done|].
        constructor 2.
        { eapply (HP' 0); [lia|]. done. }
        eapply IHn; [done| |done].
        intros. eapply (HP' (Datatypes.S i)). lia. done.
      }
      revert tr0 Hafter HP.
      induction n; intros tr0 Hafter HP.
      { simpl in *. simplify_eq.
        eapply (IHHtr' 1); try done.
        intros. destruct i; [|lia].
        simpl in *. simplify_eq. done. }
      simpl in *.
      destruct tr0; [done|]. simpl in *.
      constructor 2.
      { eapply (HP 0); [lia|]. done. }
      eapply IHn; try done.
      intros. eapply (HP (Datatypes.S i)); [lia|]. done.
  Qed.

  Lemma ltl_untilI (P Q : ltl_prop) tr :
    (P ∪ Q)%I tr ↔ (∃ n tr',
                       after n tr = Some tr' ∧
                       (∀ i tr'', i < n → after i tr = Some tr'' → P tr'') ∧
                       Q tr').
  Proof.
    split.
    - ltl_unseal.
      intros Heventually.
      induction Heventually.
      { exists 0, tr. split; [done|]. split; [|done].
        intros. lia. }
      destruct IHHeventually as [n [tr' [Hsuffix [HP HQ]]]].
      exists (Datatypes.S n), tr'.
      repeat split; [done| |done].
      intros.
      destruct i.
      { simpl in *. simplify_eq. done. }
      eapply (HP i); [lia|done].
    - intros [n [tr' [Hsuffix [HP HQ]]]].
      apply ltl_untilI_alt. exists n, tr'.
      repeat split; [done..|].
      rewrite ltl_until_unseal. by constructor 1.
  Qed.

  Lemma ltl_until_intro (P Q : ltl_prop) :
    Q ⊢ P ∪ Q.
  Proof.
    rewrite ltl_until_unseal.
    constructor.
    intros.
    by constructor 1.
  Qed.

  Lemma ltl_until_next_intro (P Q : ltl_prop) :
    P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof.
    rewrite ltl_until_unseal.
    constructor.
    unseal.
    intros tr [H1 H2].
    destruct tr.
    { revert H2. ltl_unseal. intros H2.
      destruct H2 as [tr' [Htr' H]]. done. }
    apply ltl_next_elim in H2.
    by constructor 2.
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
    apply H0.
    unseal.
    repeat split.
    - rewrite ltl_next_unseal /ltl_next_def.
      eexists tr. simpl. rewrite ltl_until_unseal. done.
    - rewrite ltl_next_unseal /ltl_next_def.
      eexists _. done.
    - done.
  Qed.

  Lemma ltl_until_mono (P1 P2 Q1 Q2 : ltl_prop) :
    (P1 ⊢ P2) → (Q1 ⊢ Q2) → (P1 ∪ Q1) ⊢ (P2 ∪ Q2).
  Proof.
    intros HP HQ. constructor. intros tr.
    rewrite !ltl_untilI. intros [n [tr' [Htr' [HP' HQ']]]].
    exists n, tr'. split; [done|]. split; [|by apply HQ].
    intros. apply HP. by eapply HP'.
  Qed.

  Lemma ltl_until_idemp (P Q : ltl_prop) :
    (P ∪ (P ∪ Q)) ⊣⊢ (P ∪ Q).
  Proof.
    constructor.
    split.
    - ltl_unseal. intros Htr. induction Htr; [done|].
      by constructor 2.
    - rewrite ->!ltl_untilI.
      intros [n [tr' [Htr' [HP HQ]]]].
      exists n, tr'. split; [done|].
      rewrite ->!ltl_untilI.
      split.
      { done. }
      exists 0, tr'. split; [done|]. split; [by intros;lia|done].
  Qed.

  (** ltl_eventually lemmas *)

  Lemma ltl_eventually_intro (P : ltl_prop) :
    P ⊢ ◊ P.
  Proof. ltl_unseal. by constructor; constructor 1. Qed.

  Lemma ltl_eventually_next_intro (P : ltl_prop) :
    (○ P) ⊢ (◊ P).
  Proof.
    constructor. ltl_unseal. intros tr Hnext.
    induction Hnext.
    { destruct tr; [inversion H; naive_solver|].
      unseal.
      constructor 2; [done|]. constructor.
      eapply (ltl_next_elim _ s ℓ). ltl_unseal.
      rewrite /ltl_next_def. simpl.
      exists tr. simpl in *. inversion H. simplify_eq. done. }
  Qed.
  
  Lemma ltl_eventuallyI_alt (P : ltl_prop) tr :
    (◊ P)%I tr ↔ (∃ tr', trace_suffix_of tr' tr ∧ (◊ P)%I tr').
  Proof.
    split.
    - intros. apply ltl_untilI_alt in H.
      destruct H as (n&tr'&Htr'&HP&HQ).
      eexists _. split; [eexists _; done|done].
    - intros. apply ltl_untilI_alt.
      destruct H as (tr'&[n Htr']&HP).
      eexists _, _.
      split; [done|].
      split; [|done]. intros. unseal. done.
  Qed.

  Lemma ltl_eventuallyI (P : ltl_prop) tr :
    (◊ P)%I tr ↔ (∃ tr', trace_suffix_of tr' tr ∧ P tr').
  Proof.
    split.
    - ltl_unseal.
      intros Heventually.
      induction Heventually.
      { exists tr. split; [apply trace_suffix_of_refl|]. done. }
      destruct IHHeventually as [tr' [Hsuffix HP]].
      exists tr'.
      split; [|done].
      by apply trace_suffix_of_cons_r.
    - intros [tr' [Hsuffix Htr']].
      apply ltl_eventuallyI_alt. exists tr'. split=>//.
      by apply ltl_eventually_intro.
  Qed.

  Lemma ltl_eventually_idemp (P : ltl_prop) :
    (◊◊P) ⊣⊢ (◊P).
  Proof.
    constructor.
    split.
    - ltl_unseal. intros Htr. induction Htr; [done|].
      by constructor 2.
    - rewrite ->!ltl_eventuallyI.
      intros [tr' [Htr' HP]].
      exists tr'. split; [done|].
      rewrite ->!ltl_eventuallyI.
      exists tr'. split; [apply trace_suffix_of_refl|done].
  Qed.

  Lemma ltl_eventually_and (P Q : ltl_prop) :
    (◊ (P ∧ Q)) ⊢ (◊ P) ∧ (◊ Q).
  Proof.
    ltl_unseal.
    constructor. unseal.
    intros tr Hconj.
    induction Hconj.
    { destruct H as [H1 H2].
      split; by constructor. }
    destruct IHHconj as [H1 H2].
    split.
    - by constructor 2.
    - by constructor 2.
  Qed.

  Lemma ltl_eventually_mono (P Q : ltl_prop) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof.
    intros HPQ. constructor. intros tr.
    rewrite !ltl_eventuallyI. intros [tr' [Htr' HP]].
    exists tr'. split; [done|]. by apply HPQ.
  Qed.

  Lemma ltl_eventually_elim_l (P Q : ltl_prop) :
    (∀ tr, P tr → (◊ Q)%I tr) → (∀ tr, (◊P)%I tr → (◊ Q)%I tr).
  Proof.
    intros HPQ tr HP.
    apply ltl_eventually_idemp.
    revert HP.
    apply ltl_eventually_mono.
    constructor. apply HPQ.
  Qed.

  Lemma ltl_eventually_next (P : ltl_prop) :
    (◊ ○ P) ⊢ (◊ P).
  Proof.
    rewrite <-(ltl_eventually_idemp P).
    apply ltl_eventually_mono.
    apply ltl_eventually_next_intro.
  Qed.

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

  Lemma ltl_eventually_next_comm (P : ltl_prop) :
    (◊ ○ P) ⊣⊢ (○ ◊ P).
  Proof.
    constructor; intros tr.
    split.
    - ltl_unseal.
      intros Hnext.
      induction Hnext.
      { revert H.
        unseal_apply ltl_next_mono. constructor.
        intros tr' HP. by constructor 1. }
      unseal_apply ltl_next_intro.
      unseal_apply ltl_eventually_next.
      done.
    - intros Hnext.
      apply ltl_eventuallyI.
      revert Hnext. ltl_unseal. intros Hnext.
      destruct tr; [inversion Hnext; naive_solver|].
      destruct Hnext as [tr' [Htr' Hnext]].
      subst.
      assert (trace_suffix_of tr' (s -[ ℓ ]-> tr)).
      { exists 1. done. }
      simpl in *. simplify_eq.
      pose proof ltl_eventuallyI as H'. revert H'. ltl_unseal. intros H'.
      apply H' in Hnext as [tr'' [Hsuff Htr']].
      assert (∃ s'' l'' tr''', tr''' = s'' -[ l'' ]-> tr'' ∧
                               trace_suffix_of tr''' ((s -[ ℓ ]-> tr')))
        as (?&?&tr'''&Heq&Hsuff').
      { by apply trace_suffix_of_cons_l_inv. }
      exists tr'''.
      subst.
      split.
      + done.
      + by unseal_apply ltl_next_intro.
  Qed.

  Lemma ltl_next_eventually (P : ltl_prop) :
    (○ ◊ P) ⊢ (◊ P).
  Proof. rewrite -{2}ltl_eventually_next ltl_eventually_next_comm. done. Qed.

  Lemma ltl_eventually_suffix_of (P : ltl_prop) tr1 tr2 :
    trace_suffix_of tr1 tr2 → (◊P)%I tr1 → (◊P)%I tr2.
  Proof. intros Hsuffix HP. apply ltl_eventuallyI_alt. by exists tr1. Qed.

  Lemma ltl_until_eventually_equiv (P : ltl_prop) :
    (True ∪ P) ⊣⊢ (◊ P).
  Proof. done. Qed.

  Lemma ltl_until_eventually (P Q : ltl_prop) :
    (P ∪ Q) ⊢ (◊ Q).
  Proof. apply ltl_until_mono; by eauto. Qed.

  (** ltl_always lemmas *)

  Lemma ltl_always_cons (P : ltl_prop) s l (tr : trace S L) :
    (□ P)%I (s -[l]-> tr) → (□ P)%I tr.
  Proof.
    ltl_unseal. rewrite /ltl_always_def. unseal.
    intros Htr Htr'. apply Htr. clear Htr. 
    revert Htr'. ltl_unseal. by constructor 2.
  Qed.


  Lemma ltl_alwaysI_alt (P : ltl_prop) tr :
    (□P)%I tr ↔ (∀ tr', trace_suffix_of tr' tr → (□ P)%I tr').
  Proof.
    ltl_unseal. rewrite /ltl_always_def. unseal.
    rewrite /ltl_impl_def /ltl_pure_def.
    ltl_unseal.
    split.
    - intros Htr tr' Hsuffix Htr'.
      apply Htr.
      induction Htr'.
      { unseal_apply ltl_untilI_alt.
        destruct Hsuffix as [n Hsuffix].
        exists n,tr0. split; [done|]. split; [done|].
        by unseal_apply ltl_until_intro. }
      apply IHHtr'. by eapply trace_suffix_of_cons_l.
    - intros Htr' Htr.
      induction Htr.
      { specialize (Htr' tr). apply Htr'.
        { apply trace_suffix_of_refl. }
        by unseal_apply ltl_until_intro. }
      apply IHHtr. intros tr' Htsuffix. apply Htr'.
      by eapply trace_suffix_of_cons_r.
  Qed.

  Lemma ltl_always_suffix_of (P : ltl_prop) tr1 tr2 :
    trace_suffix_of tr2 tr1 → (□P)%I tr1 → (□P)%I tr2.
  Proof. rewrite (ltl_alwaysI_alt _ tr1). intros Hsuffix HP. by eapply HP. Qed.

  Lemma ltl_always_elim (P : ltl_prop) :
    (□P) ⊢ P.
  Proof.
    constructor. ltl_unseal. rewrite /ltl_always_def. unseal.
    rewrite /ltl_impl_def /ltl_pure_def.
    intros tr Htr.
    assert (P tr ∨ ¬ P tr) as [|HP] by apply ExcludedMiddle; [done|].
    assert (¬ (¬ P)%I tr).
    { unseal. intros Htr'. apply Htr. apply ltl_until_intro. done. }
    revert HP H. unseal. intros HP H.
    exfalso.
    apply H. apply HP.
  Qed.

  Lemma ltl_alwaysI (P : ltl_prop) tr :
    (□P)%I tr ↔ (∀ tr', trace_suffix_of tr' tr → P tr').
  Proof.
    split.
    - intros HP tr' Hsuff. rewrite ltl_alwaysI_alt in HP.
      apply ltl_always_elim. eauto.
    - ltl_unseal. rewrite /ltl_always_def. unseal. rewrite /ltl_impl_def /ltl_pure_def.
      intros H Habs. apply ltl_untilI in Habs as (n&tr'&Hsuff&?&?).
      apply H1. apply H. exists n. done.
  Qed.

  Lemma ltl_always_intro' (P : ltl_prop) :
    (⊢ P) → (⊢ □ P).
  Proof.
    intros [HP].
    constructor.
    intros tr _. apply ltl_alwaysI.
    intros tr' Hsuff. apply HP.
    unseal. done.
  Qed.

  Lemma ltl_always_idemp (P : ltl_prop) :
    (□ P) ⊣⊢ (□ □ P).
  Proof.
    constructor.
    split.
    - ltl_unseal. rewrite /ltl_always_def. unseal.
      rewrite /ltl_impl_def /ltl_pure_def.
      ltl_unseal.
      intros Htr Htr'.
      induction Htr' as [|s l tr HP HQ IHHtr']; [by apply H|].
      apply IHHtr'.
      pose proof ltl_always_cons.
      revert H. ltl_unseal. rewrite /ltl_always_def. unseal. rewrite /ltl_impl_def.
      ltl_unseal.
      intros H.
      by eapply H.
    - apply ltl_always_elim.
  Qed.

  Lemma ltl_always_mono (P Q : ltl_prop) :
    (P ⊢ Q) → (□P) ⊢ (□Q) .
  Proof.
    intros HPQ. constructor. ltl_unseal. rewrite /ltl_always_def.
    unseal.
    intros tr HP HQ.
    apply HP. eapply ltl_until_mono; [done| |done].
    clear HP HQ.
    constructor. intros tr' HP HQ. apply HP. apply HPQ. done.
  Qed.

  Lemma ltl_always_and (P Q : ltl_prop) :
    (□ (P ∧ Q))%I ⊣⊢ (□ P) ∧ (□ Q).
  Proof.
    constructor.
    intros tr. rewrite !ltl_alwaysI. unseal.
    split.
    - intros HPQ.
      split.
      + rewrite ltl_alwaysI.
        intros tr' Hsuff. apply HPQ in Hsuff.
        by destruct Hsuff as [HP _].
      + rewrite ltl_alwaysI.
        intros tr' Hsuff. apply HPQ in Hsuff.
        by destruct Hsuff as [_ HQ].
    - intros [H1 H2] tr' Hsuff. split.
      + rewrite ltl_alwaysI in H1. by apply H1.
      + rewrite ltl_alwaysI in H2. by apply H2.
  Qed.

  Lemma ltl_always_eventually (P : ltl_prop) :
    (□ P) ⊢ (◊ P).
  Proof. rewrite -ltl_eventually_intro. apply ltl_always_elim. Qed.

  Lemma ltl_always_intro (P Q : ltl_prop) :
    (P ⊢ Q) → (Q ⊢ (○ Q)) → (P ⊢ (□ Q)).
  Proof.
    intros HPQ IHQ.
    constructor.
    intros tr HP.
    apply ltl_alwaysI.
    intros tr' [n Hsuff].
    revert tr tr' Hsuff HP.
    induction n; intros tr tr' Hsuff HP.
    { simpl in *. simplify_eq. by apply HPQ. }
    destruct tr; [done|].
    replace (Datatypes.S n) with (n + 1) in Hsuff by lia.
    rewrite after_sum' in Hsuff.
    destruct (after n (s -[ ℓ ]-> tr)) eqn:Heqn; [|done].
    eapply IHn in HP; [|done].
    assert ((○ Q)%I t) as Hnext.
    { by apply IHQ. }
    revert Hnext. ltl_unseal. intros Hnext.
    destruct Hnext as [? [H' H'']].
    simplify_eq. done.
  Qed.

  Lemma ltl_eventually_always_combine (P Q : ltl_prop) :
    (□ P ∧ ◊Q) ⊢ (◊ (Q ∧ □ P)).
  Proof.
    constructor. ltl_unseal. unseal.
    intros tr [HP HQ].
    pose proof ltl_untilI as H. revert H. ltl_unseal. intros H.
    apply H in HQ as (n&tr'&Htr'&HP'&HQ).
    unseal_apply ltl_untilI.
    exists n,tr'. split; [done|].
    split; [done|].
    split.
    - apply HQ.
    - unseal_eapply ltl_always_suffix_of; [by exists n|done].
  Qed.

  Lemma ltl_next_always_combine (P Q : ltl_prop) :
    (□ P ∧ ○ Q) ⊢ (○ (Q ∧ □ P)).
  Proof.
    constructor. ltl_unseal. unseal.
    intros tr [HP HQ].
    destruct HQ as [tr' [Htr' HQ]].
    exists tr'. split; [done|].
    split.
    - apply HQ.
    - unseal_eapply ltl_always_suffix_of; [|done].
      exists 1. done.
  Qed.

  (** Misc *)

  Lemma ltl_until_and_r (P1 P2 Q1 Q2 : ltl_prop) :
    P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ ((P1 ∧ P2) ∪ (Q1 ∧ P2 ∪ Q2)) ∨ ((P1 ∧ P2) ∪ (P1 ∪ Q1 ∧ Q2)).
  Proof.
    constructor.
    unseal.
    intros tr [HPQ1 HPQ2].
    rewrite ltl_untilI in HPQ1.
    rewrite ltl_untilI in HPQ2.
    destruct HPQ1 as (n&trPQ1&HtrPQ1&HP1&HQ1).
    destruct HPQ2 as (m&trPQ2&HtrPQ2&HP2&HQ2).
    destruct (decide (n < m)).
    { left.
      rewrite ltl_untilI.
      exists n, trPQ1.
      split; [done|].
      split.
      { intros. split; [by eapply HP1|eapply HP2; [|done]]. lia. }
      split; [done|].
      rewrite ltl_untilI.
      assert (∃ k, m = k+n) as [k ->].
      { exists (m-n). lia. }
      exists k,trPQ2.
      split.
      { rewrite after_sum in HtrPQ2.
        rewrite HtrPQ1 in HtrPQ2.
        done. }
      split; [|done].
      intros. eapply (HP2 (i+n)).
      { lia. }
      rewrite after_sum. rewrite HtrPQ1. done. }
    right.
    rewrite ltl_untilI.
    exists m, trPQ2.
    split; [done|].
    split.
    { intros. split; [eapply HP1; [|done]|by eapply HP2]. lia. }
    split; [|done].
    rewrite ltl_untilI.
    assert (∃ k, n = k+m) as [k ->].
    { exists (n-m). lia. }
    exists k, trPQ1.
    split.
    { rewrite after_sum in HtrPQ1.
      rewrite HtrPQ2 in HtrPQ1.
      done. }
    split.
    { intros. eapply (HP1 (i+m)).
      { lia. }
      rewrite after_sum. rewrite HtrPQ2. done. }
    done.
  Qed.

  (* Maybe make this the main lemma *)
  Lemma ltl_until_and_r' (P1 P2 Q1 Q2 : ltl_prop) :
    P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ (P1 ∧ P2) ∪ ((Q1 ∧ P2 ∪ Q2) ∨ ((P1 ∪ Q1 ∧ Q2))).
  Proof.
    rewrite ltl_until_and_r.
    apply or_elim.
    - apply ltl_until_mono; [done|]. apply or_intro_l.
    - apply ltl_until_mono; [done|]. apply or_intro_r.
  Qed.

  (* TODO: Might not really need this lemma, as [ltl_until_and_r is strictly stronger. *)
  Lemma ltl_eventually_and_r (P Q : ltl_prop) :
    ◊ P ∧ ◊ Q ⊢ ◊ (P ∧ ◊ Q) ∨ ◊ (◊ P ∧ Q).
  Proof. by rewrite ltl_until_and_r !ltl_until_eventually. Qed.

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
  
  Notation ltl_prop := (ltl_prop S L).
  
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
    - iIntros "_". iApply ltl_always_intro'. done.
    - by apply ltl_always_mono.
    - iIntros (P Q) "[HP HQ]". iApply ltl_always_and. by iSplit.
  Qed.

  Definition modality_always := Modality (@ltl_always S L) modality_always_mixin.
  Global Instance from_modal_always (P : ltl_prop) :
    @FromModal ltlI ltlI _ True%type modality_always (□ P) (□ P) (P).
  Proof. rewrite /FromModal /=. done. Qed.

  Global Instance ltl_next_combine (P Q : ltl_prop) :
    CombineSepAs (○ P) (○ Q) (○ (P ∧ Q)).
  Proof. by rewrite /CombineSepAs bi_sep_and ltl_next_and. Qed.

  Global Instance ltl_next_always_combine' (P Q : ltl_prop) :
    CombineSepAs (○ P) (□ Q) (○ (P ∧ □ Q)).
  Proof.
    rewrite /CombineSepAs. rewrite bi.sep_comm.
    apply ltl_next_always_combine.
  Qed.

  Global Instance ltl_eventually_always_combine' (P Q : ltl_prop) :
    CombineSepAs (◊ P) (□ Q) (◊ (P ∧ □ Q)).
  Proof.
    rewrite /CombineSepAs. rewrite bi.sep_comm.
    apply ltl_eventually_always_combine.
  Qed.

  (* Global Instance ltl_until_combine (P1 P2 Q1 Q2 : ltl_prop) : *)
  (*   CombineSepAs (P1 ∪ Q1) (P2 ∪ Q2) ((P1 ∧ P2) ∪ (Q1 ∧ (P2 ∪ Q2)) ∨ (P1 ∧ P2) ∪ ((P1 ∪ Q1) ∧ Q2)). *)
  (* Proof. rewrite /CombineSepAs. apply ltl_until_and_r. Qed. *)

  Global Instance ltl_until_combine' (P1 P2 Q1 Q2 : ltl_prop) :
    CombineSepAs (P1 ∪ Q1) (P2 ∪ Q2) ((P1 ∧ P2) ∪ ((Q1 ∧ (P2 ∪ Q2)) ∨ ((P1 ∪ Q1) ∧ Q2))).
  Proof. rewrite /CombineSepAs. apply ltl_until_and_r'. Qed.

End ltl_proofmode.


Tactic Notation "iModNext" "with" constr(pat) :=
  iApply (ltl_next_mono with pat); try iIntros pat.
Tactic Notation "iModNext" "with" constr(pat1) "as" constr(pat2) :=
  iApply (ltl_next_mono with pat1); try iIntros pat2.
Tactic Notation "iModEv" "with" constr(pat) :=
  iApply ltl_eventually_idemp; iApply (ltl_eventually_mono with pat); try iIntros pat.
Tactic Notation "iModEv" "with" constr(pat1) "as" constr(pat2) :=
  iApply ltl_eventually_idemp; iApply (ltl_eventually_mono with pat1); try iIntros pat2.
