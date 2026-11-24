(* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

From Corelib Require
   Import Relation_Definitions
         RelationClasses
         Setoid
         Morphisms.

(** Notations **)

Declare Scope ctx_scope.
Open Scope ctx_scope.
Delimit Scope ctx_scope with ctx.

Declare Scope ty_scope.
Open Scope ty_scope.
Delimit Scope ty_scope with ty.

Declare Scope subs_scope.
Open Scope subs_scope.
Delimit Scope subs_scope with subs.

Declare Scope term_scope.
Open Scope term_scope.
Delimit Scope term_scope with term.


Reserved Notation "[ ⊢ Γ 'Cx' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"     (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]" (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y ~ Γ ]" (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A1 == A2 'type' ]" (at level 0, no associativity) .
Reserved Notation "[ Γ ⊢ a '==' b @ A ]" (at level 0, no associativity) .
Reserved Notation "[ Δ ⊢ y == y' ~ Γ ]" (at level 0, no associativity).

(* Reserved Notation "1" (at level 0). *)
Reserved Notation "Γ # A"  (at level 1, left associativity, format "Γ # A").

Reserved Notation "'base'" (at level 0).
(* Reserved Notation "A * B". *)
Reserved Notation "A --> B"  (at level 55).
Reserved Notation "A [ y ]" (at level 1, left associativity).

Reserved Notation "'q'".
Reserved Notation "( a , b )" (at level 20, no associativity).
Reserved Notation "'fst' p"  (at level 0).
Reserved Notation "'snd' p"  (at level 20).
Reserved Notation "'λ' ( b )"  (at level 20).
Reserved Notation "app( f , a )" (at level 0).

(* Reserved Notation "a [ y ]"(at level 1). *)
Reserved Notation "'conv' e"  (at level 20).

Reserved Notation "'Id'".
Reserved Notation "'p'".
Reserved Notation "!" (at level 0).
Reserved Notation "y1 ∘ y0" (at level 1, left associativity).
Reserved Notation "y # a" (at level 1, left associativity, format "y # a").

(** End Notations **)

(** Judgments **)

Inductive  ContextJG : Prop :=
   | context_empty :
      [ ⊢ 1 Cx ]
   | context_extend {Γ : preContext} {A : preType} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ A type ]
      -> [ ⊢  Γ # A Cx]

with TypeJG : preContext -> preType -> Prop :=
   | type_base {Γ} :
      [ ⊢ Γ Cx ]
      -> [ Γ ⊢ base type ]
   | type_prod {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
      -> [ Γ ⊢ (A * B) type ]
   | type_func {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
      -> [ Γ ⊢ A --> B type ]
   | type_subs {Δ Γ} {y} {A} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
      -> [ Δ ⊢ A [y] type ]

with TermJG : preContext -> preType -> preTerm -> Prop :=
   | term_qar {Γ A} :
      [ Γ ⊢ A type ]
      -> [ Γ # A ⊢ q @ A [p] ]
     (* The q term is a "generic element" of the type A, which can be substituted by any term of type A. *)
   | term_pair {Γ A B a b} :
      [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
      -> [ Γ ⊢ (a, b) @ (A * B) ]
   | term_fst {Γ A B p} :
      [ Γ ⊢ p @ (A * B) ]
      -> [ Γ ⊢ fst p @ A ]
   | term_snd {Γ A B p} :
      [ Γ ⊢ p @ (A * B) ]
       -> [ Γ ⊢ snd p @ B ]
   | term_abs {Γ A B b} :
      [ Γ ⊢ B type ] -> [ Γ # A ⊢ b @ B ]
      -> [ Γ ⊢ λ (b) @ (A --> B) ]
   | term_app {Γ A B f a} :
      [ Γ ⊢ a @ A ] -> [ Γ ⊢ B type ] -> [ Γ ⊢ f @ (A --> B) ]
      -> [ Γ ⊢ app(f, a) @ B ]
   | term_subs {Δ Γ} {y} {A} {a} :
      [ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
      -> [ Δ ⊢ (a [y]) @ (A [y]) ]
   | term_conv {Γ} {A B} {e} :
      [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ]
      -> [ Γ ⊢ conv e @ B ]

with SubsJG : preContext -> preContext -> preSubs -> Prop :=
   | subs_id {Γ} :
      [ ⊢ Γ Cx ]
      -> [ Γ ⊢ Id ~ Γ ]
   | subs_comp {Γ0 Γ1 Γ2} {y0 y1} :
      [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ]
      ->[ Γ2 ⊢ (y0 ∘ y1) ~ Γ0 ]
   | subs_weak {Γ A} :
      [ Γ ⊢ A type ]
      -> [ Γ # A ⊢ p ~ Γ ]
   | subs_Bang {Γ} :
      [ ⊢ Γ Cx ]
      -> [ Γ ⊢ ! ~ 1 ]
   | subs_ext {Δ Γ} {y} {a A} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A[y] ]
      ->  [ Δ ⊢ (y # a) ~ (Γ # A) ]

with eq_type : preContext -> relation (preType) :=
(** Enforce equivalence **)
| eq_type_refl {Γ A} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A == A type ]
| eq_type_sym {Γ} {A B} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == A type ]
| eq_type_trans {Γ} {A B C} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == C type ]
   -> [ Γ ⊢ A == C type ]
(** Enforce compatibility with type constructors **)
| eq_type_prod {Γ} {A1 A2 B1 B2} :
   [ Γ ⊢ A1 == A2 type ] -> [ Γ ⊢ B1 == B2 type ]
   -> [ Γ ⊢ A1 * B1 == A2 * B2 type ]
| eq_type_func {Γ} {A1 A2 B1 B2} :
   [ Γ ⊢ A1 == A2 type ] -> [ Γ ⊢ B1 == B2 type ]
   -> [ Γ ⊢ A1 --> B1 == A2 --> B2 type ]
| eq_type_subs {Δ Γ} {y1 y2} {A1 A2} :
   [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Γ ⊢ A1 == A2 type ]
   -> [ Δ ⊢ A1 [y1] == A2 [y2] type ]%ty
(** Enforce distributivity of substitution over type constructors **)
| eq_subst_prod {Δ Γ A B y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A * B) [ y ] == A [y] * B [y] type ]%ty
| eq_subst_func {Δ Γ A B y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A --> B) [ y ] == A [y] --> B [y] type ]%ty
(** Enforce compatibility with substitution **)
| eq_subst_id_type {Γ A} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A [ Id ] == A type ]%ty
| eq_subst_comp_type {Γ Γ1 Γ0} {A} {y1} {y0} :
   [ Γ ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]%ty

with eq_term : preContext -> preType -> relation (preTerm) :=
(** Enforce equivalence **)
| eq_term_refl {Γ A} e :
   [ Γ ⊢ e @ A ]
   -> [ Γ ⊢ e == e @ A ]
| eq_term_sym {Γ A} e1 e2 :
   [ Γ ⊢ e1 == e2 @ A ]
   -> [ Γ ⊢ e2 == e1 @ A ]
| eq_term_trans {Γ} {A} e1 e2 e3 :
   [ Γ ⊢ e1 == e2 @ A ] -> [ Γ ⊢ e2 == e3 @ A ]
   -> [ Γ ⊢ e1 == e3 @ A ]
(** Enforce compatibility with term constructors **)
| eq_term_pair {Γ} {A B} {a1 a2 b1 b2} :
   [ Γ ⊢ a1 == a2 @ A ] -> [ Γ ⊢ b1 == b2 @ B ]
   -> [ Γ ⊢ (a1, b1) == (a2, b2) @ A * B ]
| eq_term_func {Γ} {A B} {b1 b2} :
   [ Γ # A ⊢ b1 == b1 @ B [p] ]
   -> [ Γ ⊢ λ (b1) == λ (b2) @ A --> B ]
(** Compatibility for substitution **)
| eq_term_id {Γ} {A a} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ Id ] == a @ A ]
| eq_term_comp {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1] == a [y0] [y1] @ A [y0 ∘ y1] ]
(** βη-equivalence for pairs **)
| eq_term_beta_fst {Γ} {A B} a b :
   [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ fst (a, b) == a @ A ]
| eq_term_beta_snd {Γ} {A B} a b :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ snd (a, b) == b @ B ]
| eq_term_eta_pair {Γ} {A B} p :
   [ Γ ⊢ p @ A * B ]
   -> [ Γ ⊢ p == (fst p, snd p) @ A * B ]
(** βη-equivalence for abstractions **)
| eq_term_beta_app {Γ} {A B} {a b} :
   [Γ ⊢ B type] -> [ Γ # A ⊢ b @ B ] -> [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ app( λ (b) , a ) == b [Id # a] @ B [Id # a] ]
| eq_term_eta_app {Γ} {A B} {f} :
   [ Γ ⊢ B type] -> [ Γ ⊢ A type ] -> [ Γ ⊢ f @ (A --> B) ]
   -> [ Γ ⊢ f == (λ (app(f, q))) @ (A --> B) ]
(** βη-equivalence for substitution extension **)
| eq_beta_quar {Δ} {Γ} {y} {A} {a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ]

with eq_subs : preContext -> preContext -> relation (preSubs) :=
(** Enforce equivalence **)
| eq_subs_refl {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ y == y ~ Γ ]
| eq_subs_sym {Δ Γ} {y1 y2} :
   [ Δ ⊢ y1 == y2 ~ Γ ]
   -> [ Δ ⊢ y2 == y1 ~ Γ ]
| eq_subs_trans {Δ Γ} {y1 y2 y3} :
   [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ]
   -> [ Δ ⊢ y1 == y3 ~ Γ ]
(** Compatibility with composition **)
| eq_subs_left_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ Id ∘ y == y ~ Γ ]
| eq_subs_right_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ y ∘ Id == y ~ Γ ]
| eq_subs_comp_assoc {Γ3 Γ2 Γ1 Γ0} {y0 y1 y2} :
   [ Γ3 ⊢ y2 ~ Γ2 ] -> [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0]
   -> [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ0 ]
(** Unicity of bang **)
| eq_subs_bang {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ]
   -> [ Γ ⊢ ! == δ ~ 1 ]
(** βη-equivalence for substitution extension **)
| eq_subs_beta {Δ Γ A a y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ p ∘ (y # a) == y ~ Γ ]
| eq_subs_eta {Δ Γ A y} :
   [ Γ ⊢ A type ] -> [ Δ ⊢ y ~ Γ # A ]
   -> [ Δ ⊢ y == ((p ∘ y) # (q[y])) ~ (Γ # A) ]

where "[ ⊢ Γ 'Cx' ]"       := (ContextJG Γ) : ctx_scope
and "[ Γ ⊢ A 'type' ]"     := (TypeJG Γ A) : ty_scope
and "[ Γ ⊢ a @ A ]" := (TermJG Γ A a): term_scope
and "[ Δ ⊢ y ~ Γ ]" := (SubsJG Δ Γ y): subs_scope
and "[ Γ ⊢ A1 == A2 'type' ]" := (eq_type Γ A1 A2) : ty_scope
and "[ Γ ⊢ a '==' b @ A ]" := (eq_term Γ A a b) : term_scope
and "[ Δ ⊢ y == y' ~ Γ ]" := (@eq_subs Δ Γ y y') : subs_scope

and "1" := pctx_one : ctx_scope
and "Γ # A" := (pctx_ext Γ A) : ctx_scope

and "base" := ptyp_base : ty_scope
and "A * B" := (ptyp_prod A B) : ty_scope
and "A --> B" := (ptyp_func A B) : ty_scope
and "A [ y ]" := (ptyp_subs A y) : ty_scope

and "'q'" := ptrm_qar : term_scope
and "( a , b )" := (ptrm_pair a b) : term_scope
and "'fst' p" := (ptrm_fst p) : term_scope
and "'snd' p" := (ptrm_snd p) : term_scope
and "'λ' ( b )" := (ptrm_lam b) : term_scope
and "app( f , a )" := (ptrm_app f a) : term_scope
and "a [ y ]" := (ptrm_subs a y) : term_scope
and "'conv' e" := (ptrm_conv e) : term_scope

and "'Id'" := psub_id : subs_scope
and "'p'"  := psub_weak : subs_scope
and "!" := psub_Bang (at level 0) : subs_scope
and "y1 ∘ y0" := (psub_comp y1 y0)  : subs_scope
and "y # a" := (psub_ext y a) : subs_scope

.


(** End Jugements *)

#[add_top] Bind Scope ctx_scope with preContext preType.
#[add_top] Bind Scope ty_scope with preType preSubs preContext.
#[add_top] Bind Scope term_scope with preTerm.

Check (1).


Check (base).
Check (1 # base).
Check (base * base --> base).
Check ( (base * base --> base) [ psub_id ] ).


Check ( q ).
Print Visibility term_scope.
Check (q, q).
Check ( fst ( q , q ) ).
Check ( snd ( q , q ) ).
(* Check ( λ ( q ) ). *)
(* Check ( app( λ ( q ) , q ) ). *)

#[add_top] Bind Scope subs_scope with preSubs.

Check ( Id ).
Check ( p ).
Check ( ! ).
Check ( Id ∘ p ).
Check ( Id # q ).
Example Ex1 : ([1 ⊢ base * base --> base type ]).
Proof.
   apply type_func.
   - apply type_prod; apply type_base; apply context_empty.
   - apply type_base. apply context_empty.
Qed.

(** Quotient and Notations coherences **)


Add Parametric Relation Γ : (preType) (eq_type Γ)
   symmetry proved by (@eq_type_sym Γ)
   transitivity proved by (@eq_type_trans Γ)
   as eq_pretype_rel.

Add Parametric Morphism Γ : (eq_type Γ)
   with signature (eq_type Γ ==> eq_type Γ ==> iff)
   as eq_type_mor.
Proof.
   intros A1 B1 H_eq1 A2 B2 H_eq2.
   split; intro;
   eapply eq_type_trans;
   try (eassumption);
   eapply eq_type_trans;
   try (eassumption);
   apply eq_type_sym;
   assumption.
Qed.

Theorem type_coherence :
   forall {Γ A}, [ Γ ⊢ A type ] -> [ ⊢ Γ Cx ].
Proof.
   intros.
   induction H.
   - assumption.
   - assumption.
   - assumption.
   - generalize dependent A.
       induction H; intros; try (assumption).
       + specialize (IHSubsJG2 IHTypeJG A H1).
       specialize (IHSubsJG1 IHSubsJG2 (A [y0])%ty ).
       apply IHSubsJG1.
       eapply type_subs;
       eassumption.
      + apply context_extend; assumption.
      + inversion IHTypeJG; subst.
        apply (IHSubsJG H5 A H6).
Qed.

Lemma type_prod_injective Γ A1 A2 B1 B2 :
   [ Γ ⊢ A1 * B1 == A2 * B2 type ]
   -> [ Γ ⊢ A1 == A2 type ] /\ [ Γ ⊢ B1 == B2 type ].
Proof.
   intros H.
   induction H; subst.
   - inversion H3; subst.
   split; apply eq_type_refl; assumption.
   -

Lemma typing_unicity Γ A B a :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ B ]
   -> [ Γ ⊢ A == B type ].
Proof.
   generalize dependent B.
   generalize dependent A.
   generalize dependent Γ.
   induction a;
   intros Γ A B HA HB;
   inversion HA; subst;
   inversion HB; subst.
   - constructor.
      econstructor.
      econstructor.
      assumption.
      assumption.
   - specialize (IHa1 _ _ _ H3 H5) as IHeq1.
      specialize (IHa2 _ _ _ H4 H6) as IHeq2.
      apply eq_type_prod; assumption.
   -  specialize (IHa _ _ _ H2 H3) as IHeq.
      inversion IHeq; subst.
      +  constructor.
         inversion H4; subst.
         assumption.
      +
      inversion HA.
      induction H.
      split. constructor.
      apply term_coherence in HC.
   apply EqTransType with A.
   apply EqSymType. apply EqReflType.
   apply EqTransType with B; assumption.
   assumption.

Lemma subs_codomain_unicity :
   forall {Δ Γ1 Γ2 y}, [ Δ ⊢ y ~ Γ1 ] -> [ Δ ⊢ y ~ Γ2 ] -> Γ1 = Γ2.
Proof.
   intros Δ Γ1 Γ2 y.
   generalize dependent Γ2.
   generalize dependent Γ1.
   generalize dependent Δ.
   induction y; intros Δ Γ1 Γ2 H1 H2; inversion H1; inversion H2; subst.
   - reflexivity.
   - specialize (IHy2 _ _ _ H5 H11); subst.
      specialize (IHy1 _ _ _ H6 H12); subst.
      reflexivity.
   - inversion H5. reflexivity.
   - reflexivity.
   - apply f_equal2.
      eapply IHy; eassumption.
      (** type unicity **)

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as preType_mor.
Proof.
   intros.
   induction H.
   - apply iff_refl.
   - apply iff_sym. assumption.
   - eapply iff_trans. apply IHeq_type1. assumption.
   - split; intro;
      inversion H1; subst;
      apply IHeq_type1 in H5;
      apply IHeq_type2 in H6;
      constructor; assumption.
   - split; intro;
      inversion H1; subst;
      apply IHeq_type1 in H5;
      apply IHeq_type2 in H6;
      constructor; assumption.
   - induction H.
      + split; intro.
         inversion H1; subst.
         apply IHeq_type in H5;
         constructor; assumption.
      + split; intro;
         inversion H1; subst;
         apply IHeq_type in H5;
      inversion H1; subst.
      apply IHeq_type in H5;
      apply IHeq_type2 in H6;
      constructor; assumption.
   - split.
      + intro.
      assumption.
      + intro. apply (@type_subs Γ Γ).
         apply subs_id.
         apply (type_coherence H).
         assumption.
   - split; intro.
      +  apply (type_subs H).
         apply (type_subs H0).
         assumption.
      +  apply (@type_subs Γ Γ0).
         apply (subs_comp H H0).
         assumption.
   - split; intro ; inversion H1; subst;
         apply IHeq_type1 in H5;
         apply IHeq_type2 in H6;
         constructor; assumption.
Qed.

Theorem eq_type_coherence :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
   intros.
   induction H.
   - tauto.
   - apply and_comm. assumption.
   - destruct IHeq_type1 as [H_A1 H_A2].
      destruct IHeq_type2 as [H_A2' H_A3].
      split ; assumption.
   - split.
      eapply type_subs.
      apply subs_id.
      apply (type_coherence H).
      assumption.
      assumption.
   - split.
      eapply type_subs.
      apply (subs_comp H H0).
      assumption.
      apply (type_subs H).
      apply (type_subs H0).
      assumption.
   - destruct IHeq_type1 as [H_A1 H_B1].
      destruct IHeq_type2 as [H_A2 H_B2].
      split; constructor; assumption.
Qed.

Add Parametric Relation Γ A : (preTerm) (eq_term Γ A)
   symmetry proved by (@eq_term_sym Γ A)
   transitivity proved by (@eq_term_trans Γ A)
   as eq_preTerm_rel.

Add Parametric Morphism Γ A : (eq_term Γ A)
   with signature (eq_term Γ A ==> eq_term Γ A ==> iff)
   as eq_term_mor.
Proof.
   intros a1 b1 H_eq1 a2 b2 H_eq2.
   split; intro;
   eapply eq_term_trans;
   try (eassumption);
   eapply eq_term_trans;
   try (eassumption);
   apply eq_term_sym;
   assumption.
Qed.

Add Parametric Relation Δ Γ : (preSubs) (eq_subs Δ Γ)
   symmetry proved by (@eq_subs_sym Δ Γ)
   transitivity proved by (@eq_subs_trans Δ Γ)
   as eq_preSubs_rel.

Add Parametric Morphism Δ Γ : (eq_subs Δ Γ)
   with signature (eq_subs Δ Γ ==> eq_subs Δ Γ ==> iff)
   as eq_subs_mor.
Proof.
   intros y1 y2 H_eq1 y3 y4 H_eq2.
   split; intro;
   eapply eq_subs_trans;
   try (eassumption);
   eapply eq_subs_trans;
   try (eassumption);
   apply eq_subs_sym;
   assumption.
Qed.

Lemma subst_morphism  {Δ Γ} {y} {A B}:
   [ Δ ⊢ y ~ Γ ] ->
   [ Γ ⊢ A == B type ] ->
   [ Δ ⊢ A [ y ] == B [ y ] type ]%ty.
   generalize dependent B.
   generalize dependent A.
   generalize dependent Γ.
   generalize dependent Δ.
   induction y; intros Δ Γ A B H_subs H_types;
   apply (eq_type_coherence) in H_types as H2;
   destruct H2 as [H_A H_B];
   inversion H_subs; subst.
   - apply (eq_type_coherence) in H_types as H2.
      apply EqTransType with (A2 := B);
      [rewrite <- H_types | symmetry];
      apply EqSubstIdType; assumption.
   - rewrite (EqSubstCompType H3 H4 H_A).
      rewrite (EqSubstCompType H3 H4 H_B).
      apply IHy2 with (Γ := Γ1).
      assumption.
      eapply IHy1;
      eassumption.
   -

Lemma subst_distributive {Δ Γ} {y} {A B}:
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A * B type ] ->
   [ Δ ⊢ (A * B) [y] == A [y] * B [y] type ]%ty.
Proof.
   generalize dependent B.
   generalize dependent A.
   generalize dependent Γ.
   generalize dependent Δ.
   induction y; intros Δ Γ A B H_subs H_types;
   inversion H_subs; subst.
   - rewrite (EqSubstIdType H_types).
      inversion H_types; subst.
      apply EqProd;
      apply EqSymType;
      apply EqSubstIdType; assumption.
   - rewrite (EqSubstCompType H3 H4 H_types).
      specialize (IHy1 _ _ _ _ H4 H_types) as H_eq1.
      inversion H_types; subst.
      apply EqProd;
      apply EqSubstCompType; assumption.

Lemma term_unconv {Γ A} {e} :
   [ Γ ⊢ e @ A [ Id ] ]  -> [ Γ ⊢ e @ A ].
Proof.
   generalize dependent A.
   induction e; intros A H;
   inversion H; subst.
   inversion H; subst.
   apply term_conv with A; assumption.

Add Parametric Morphism Γ : (TermJG Γ)
   with signature (@eq_type Γ ==> eq  ==> iff)
   as term_jg_eq_type_mor.
Proof.
   intros A B H_eq a.
   split; intro.
   2: symmetry in H_eq.
   all : apply (term_conv H) in H_eq;
      apply (term_unconv H_eq).

Theorem subst_coherence :
   forall Δ Γ y, [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ Cx ] /\ [ ⊢ Γ Cx ].
Proof.
   intros.
   induction H; try (assumption).
   - tauto.
   - tauto.
   - apply type_coherence in H as H2.
      split. apply context_extend.
      all: assumption.
   - split. assumption.
      apply context_empty.
   - inversion IHSubsJG; subst.
      split. assumption.
      apply context_extend; assumption.
Qed.

Theorem term_coherence :
   forall Γ A a, [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intros.
   induction H.
   - eapply type_subs.
      apply subs_weak.
      assumption.
      assumption.
   - constructor.
      assumption.
      assumption.
   - inversion IHTermJG; subst.
      assumption.
   - inversion IHTermJG; subst.
      assumption.
   - inversion IHTermJG; subst.
      apply subst_coherence in H4 as [H6 _].
      inversion H6; subst.
      constructor;
      assumption.
   - inversion IHTermJG1; subst.
       assumption.
   - econstructor.
      eassumption.
      assumption.
   - rewrite <- H0.
   (* - induction B; subst. *)
      assumption.
   - assumption.
Qed.

Add Parametric Morphism Γ A: (TermJG Γ A)
   with signature (@eq_term Γ A ==> iff)
   as type_jg_eq_term_mor.
Proof.
   intros a b H_eq.
   induction H_eq; subst.
   - apply iff_refl.
   - apply (iff_sym IHH_eq).
   - apply (iff_trans IHH_eq1 IHH_eq2).
   - split; intro.
      inversion H0; subst.
      inversion H4; subst.
      assumption.
      inversion H1; subst.
      eapply term_fst.
      apply term_pair;
      eassumption.
   - split; intro.
      inversion H0; subst.
      inversion H4; subst.
      assumption.
      eapply term_snd.
      apply term_pair;
      eassumption.
   - split; intro.
      apply term_pair.
      eapply term_fst; eassumption.
      eapply term_snd; eassumption.
      assumption.
   - split; intro.
      assumption.
      assert ([Γ ⊢ Id ~ Γ] )%subs as H_subs.
      {
         apply subs_id.
         apply term_coherence in H as H_ty.
         apply type_coherence in H_ty as H_ctx.
         assumption.
      }
      apply (term_subs H_subs)  in H.

Add Parametric Morphism Γ : (TermJG Γ)
   with signature (@eq_type Γ ==> eq  ==> iff)
   as term_jg_eq_type_mor.
Proof.
   intros A B H_eq.
   induction H_eq; intro a.
   - apply iff_refl.
   - apply (iff_sym (IHH_eq a)).
   - apply (iff_trans (IHH_eq1 a) (IHH_eq2 a)).
   - split; intro.
      induction H0; subst.
         + apply term_qar.
            inversion H4; subst.
            assumption.
         + eapply term_fst.
            apply term_pair.
            assumption.
            eassumption.
      generalize dependent Γ.
      induction a; intros; try (assumption).
      + split; intro.
         inversion H; subst.
         assert (exists B, A [Id] = B [ p ])%preType as H_eq.
         replace (A [Id]) with (B [p]).
         inversion H; subst.
         assumption.
      + eapply term_fst.
         apply term_pair.
         assumption.

Add Parametric Morphism Δ Γ : (SubsJG Δ Γ)
   with signature (eq_subs Δ Γ ==> iff)
   as preSubs_mor.
Proof.
   intros y1 y2 H_eq.
   induction H_eq; subst.
   - apply iff_refl.
   - apply (iff_sym IHH_eq).
   - apply (iff_trans IHH_eq1 IHH_eq2).
   - split; intro.
      assumption.
      eapply subs_comp. apply H.
      apply subs_id.
      apply subst_coherence in H.
      destruct H as [H1 H2].
      assumption.
   - split; intro.
      assumption.
      eapply subs_comp.
      apply subs_id.
      apply subst_coherence in H.
      destruct H as [H1 H2].
      assumption.
      assumption.
   - split; intro;
      eapply subs_comp;
      try (eassumption);
      eapply subs_comp;
       eassumption.
   - split; intro.
      assumption.
      apply subs_Bang.
      apply subst_coherence in H as [H1 H2].
      assumption.
   - split; intro. assumption.
      eapply subs_comp.
      eapply subs_ext.
      apply H.
      apply H0.
      apply H1.
      apply subs_weak.
      assumption.
   -  split; intro. 2: assumption.
      apply subs_ext.
      eapply subs_comp.
      apply H0.
      apply subs_weak.
      apply H.
      apply H.
      assert ([Δ ⊢ A [p ∘ y] == A [p] [y] type ])%ty as H_eq.
      {
         eapply EqSubstCompType.
         apply H0.
         apply subs_weak.
         apply H.
         apply H.
      }
      rewrite H_eq.
      assumption.



Theorem eq_term_coherence :
   forall {Γ A a b}, [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
Admitted.
(** End Notation Coherence **)

(** Quotientization **)
Add Parametric Morphism {Γ} : (TermJG Γ)
   with signature (eq_pretype ==> eq_preTerm Γ ==> iff)
   as preTerm_mor.
Proof.
   intros A B H.
   induction H.
   - intros a b H.
      induction H.
      + tauto.
      + apply (iff_sym IHeq_preTerm).
      + apply (iff_trans IHeq_preTerm1 IHeq_preTerm2).
      + split;intro.
         inversion H0; subst.
         inversion H4; subst.
         assumption.
         eapply term_fst.
         apply term_pair.
         assumption.
         eassumption.
      + split; intro.
         inversion H0; subst.
         inversion H4; subst.
         assumption.
         eapply term_snd.
         apply term_pair.
         eassumption.
         assumption.
      + apply iff_sym.
        split.
        * intros.
         inversion H0; subst.
         inversion H; subst.
         eapply term_pair; assumption.
         inversion H6; subst.
         inversion H5; subst.
         inversion H7; subst.
         inversion H9; subst.
         inversion H0; subst.
         inversion H8; subst.
         apply term_fst; assumption.
         apply term_snd; assumption.

      inversion H; subst.
         --  split; intros;
         inversion H0; subst.
            apply term_pair.
            apply (term_fst H0).
            apply (term_snd H0).
            inversion H7; subst.
            inversion H8; subst.
            inversion H6; subst.
            inversion H9; subst.
            apply term_pair; assumption.
         --

         generalize dependent p.
         generalize dependent B.
         generalize dependent A0.
         induction A.
         *
         intros.
         split. intro.
         generalize dependent B.
         generalize dependent A0.
         induction p; intros.
         inversion H; subst.
         inversion H0; subst.
         --
         -- inversion H0.
         -- split;
         intros; inversion H1.
         -- inversion H; subst.
            apply term_pair.
            apply (term_fst H0).
            apply (term_snd H0).
         * inversion H0; subst.
         specialize (IHp _ _ H4).
         inversion H4; subst.
           apply term_pair.
            apply (term_fst H0).
            apply (term_snd H0).
         *
            inversion H0; subst.
            inversion H5; subst.
            inversion H6; subst.
            inversion H4; subst.
            inversion H7; subst.
            assumption.
         generalize dependent A.
         induction p.
         *
         split; intro; inversion H0; subst.
         apply term_pair.
            apply (term_fst H0).
            apply (term_snd H0).
            inversion H5; subst.
            inversion H6; subst.
            inversion H4; subst.
            inversion H7; subst.
            apply term_pair;
            assumption.
         *
         inversion H; subst.
         generalize dependent A0.
         generalize dependent B.
         * intros.
         inversion H; subst.
         * intros.
         apply term_pair.
            apply (term_fst H0).
            apply (term_snd H0).
            inversion H5; subst.
            inversion H6; subst.
            inversion H4; subst.
            inversion H7; subst.
            apply term_pair;
            assumption.
         * intros. split. intros.
         inversion H; subst.
            inversion H0; subst.
            specialize (IHp _ _ H5) as H20.
            eapply H5  in H4.

         apply term_fst in H as H_fst.
         generalize dependent p.
         induction p; intros.
         * split; intros;
            inversion H0; subst;
            apply term_pair.
            apply (term_fst H0).
            apply (term_snd H0).
            inversion H5; subst.
            inversion H4; subst.
            assumption.
            inversion H6; subst.
            inversion H4; subst.
            assumption.
         * inversion H; subst.
         apply IHTermJG in H0.
            inversion H0; subst.
            apply term_pair; assumption.
         inversion H4; subst.
         induction A.
         inversion H0; subst.
         inversion H0; subst.
         apply term_pair.
         apply (term_fst H0).
         apply (term_snd H0).
         inversion H7; subst.
         inversion H6; subst.
         inversion H8; subst.
         inversion H9; subst.
         apply term_pair;
         assumption.
         * split; intros.
         inversion H1; subst.
         inversion H5; subst.
         inversion H0; subst.
         apply (IH H4) in H4.
         apply term_pair.
         apply (term_fst H0).
         apply (term_snd H0).
         inversion H4; subst.
         inversion H6; subst.
         inversion H7; subst.
         apply term_pair;
         assumption.


      apply H.
   - split; intro.
      assumption.
Qed.


Add Parametric Morphism {Γ} : (TermJG Γ)
   with signature (@eq_type Γ ==> eq ==> iff)
   as preTerm_mor.
Proof.
   intros A B H.
   eq_type_destruct H.
   induction H_eq; intro a.
   - tauto.
   - apply (iff_sym (IHH_eq H_B H_A a)).
   - assert ([ Γ ⊢ A2 type ]) as H_A2 by (rewrite <- H_eq1; assumption).
      apply (iff_trans (IHH_eq1 H_A H_A2 a) (IHH_eq2 H_A2 H_B a)).
   -
      generalize dependent A.
      generalize dependent Γ.
      induction a; intros.
      + split; intro.
         inversion H; subst.
         assert (exists B, A [Id] = B [ p ])%preType as H_eq.
         replace (A [Id]) with (B [p]).
         inversion H; subst.
         assumption.
      + eapply term_fst.
         apply term_pair.




Add Parametric Morphism {Δ Γ} : (SubsJG Δ Γ)
   with signature (@eq_preSubs Δ Γ  ==> iff)
   as SubsJG_mor.
Proof.
   intros y1 y2 H_eq.
   induction H_eq; subst.
   - tauto.
   - apply (iff_sym IHH_eq).
   - apply (iff_trans IHH_eq1 IHH_eq2).
   - split; intro.
      + inversion H; subst.
         inversion H5; subst.
         assumption.
      + eapply subs_comp. eapply H.
         apply subs_id.
         apply subst_coherence in H.
         destruct H as [H1 H2].
         assumption.
   - split; intro.
      + inversion H; subst.
         inversion H4; subst.
         assumption.
      + eapply subs_comp. apply subs_id.
         apply subst_coherence in H.
         destruct H as [H1 H2].
         assumption.
         apply H.
   - split; intro.
      + apply (subs_comp H).
         apply (subs_comp H0).
         assumption.
      + eapply subs_comp.
         2: apply H1.
         apply (subs_comp H).
         assumption.
   - split; intro.
      + apply subs_Bang.
         apply subst_coherence in H.
         destruct H as [H1 H2].
         assumption.
      +  assumption.
   - split; intro. assumption.
      eapply subs_comp.
      eapply subs_ext.
      apply H.
      apply H0.
      apply H1.
      apply subs_weak.
      assumption.
   - split; intro. 2: assumption.
      apply subs_ext.
      eapply subs_comp.
      apply H0.
      apply subs_weak.
      apply H.
      apply H.
      assumption.






Add Parametric Morphism {Γ} {A} : (TermJG Γ A)
   with signature (@eq_preTerm Γ A  ==> iff)
   as TermSubst_mor.
Proof.
   intros.
   induction H;
   try (assumption).
   - tauto.
   - apply (iff_sym IHeq_preTerm).
   - apply (iff_trans IHeq_preTerm1 IHeq_preTerm2).
   - split; intro.
      + inversion H; subst.
         inversion H3; subst.
         assumption.
      + eapply term_fst.
         inversion H; subst.
         apply (term_subs H).
         assumption.

Add Parametric Morphism {Γ} : (TermJG Γ)
   with signature (@eq_pretype Γ ==> eq  ==> iff)
   as TermSubst_mor.
Proof.
   intros.
   induction H;
   try (assumption).
   - tauto.
   - apply (iff_sym IHeq_pretype).
   - apply (iff_trans IHeq_pretype1 IHeq_pretype2).
   - split; intro.




Add Parametric Morphism (Δ Γ : wfCtx) : (@SubsJG Δ Γ)
   with signature (@eq_subs Δ Γ  ==> Basics.impl)
   as SubsEqJG_mor.
Proof.
   intros.
   unfold Basics.impl.
   induction H;
   try (intro; assumption).
   - intro. eapply subs_comp. eapply H.
      eapply subs_comp. eapply H0.
      assumption.
   - intro. eapply (subs_ext _ H).
         rewrite EqSubstCompType.
   - intro. apply EqCompAssoc; assumption.
   - intro. apply EqBang. assumption.
Add Parametric Morphism Γ Δ : (SubsJG Γ Δ)
   with signature (@eq_preSubs Γ Δ  ==> iff)
   as TypeEqJG_mor.
Proof.
   intros y1 y2 H_eq.
   induction H_eq; subst.
   - tauto.
   - apply (iff_sym IHH_eq).
   - apply (iff_trans IHH_eq1 IHH_eq2).
   - split; intro.
       + inversion H; subst.
          inversion H5; subst.
          assumption.
      + apply (subs_comp H).
         apply subs_id.
         apply subst_coherence in H.
         destruct H as [H1 H2].
         assumption.
   - split; intro.
       + inversion H; subst.
          inversion H4; subst.
          assumption.
      + eapply subs_comp.
         apply subs_id.
         apply subst_coherence in H.
         destruct H as [H1 H2].
         assumption.
         assumption.
   - split; intro.
       + inversion H2; subst.
          inversion H7; subst.
          apply (subs_comp H9).
          apply (subs_comp H10).
          assumption.
       + inversion H2; subst.
          inversion H8; subst.
          eapply subs_comp.
          apply (subs_comp H7).
          apply H9.
            assumption.
   - split; intro.
      apply subs_Bang.
      apply subst_coherence in H.
      destruct H as [H1 H2].
      all: assumption.
   - split; intro.
     assumption.
      eapply subs_comp.
      eapply subs_ext.
      apply H.
      apply H0.
      apply H1.
      apply subs_weak.
      apply H0.
   - split; intro.
      2 : assumption.
      eapply subs_ext.
      eapply subs_comp.
      apply H0.
      apply subs_weak.
      apply H.
      apply H.
      apply term_subs.
Qed.

