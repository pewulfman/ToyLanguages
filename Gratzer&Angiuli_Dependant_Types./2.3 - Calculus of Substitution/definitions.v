   (* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

From Corelib Require Import
      Relation_Definitions
      RelationClasses
      Setoid
      Morphisms.

From Stdlib Require Import
      Relation_Operators
      Program.Equality.
(** Pre-syntax definitions **)

(** Convention For syntax sorts. On the left is fonction parameters, on the right construction to stay true to the textbook
   Contexts ctx: greek uppercase letters: 𝚪, Δ, ...
   Types t : uppercase letters: A, B, ...
   Terms e : lowercase letters: a, b, ...
   Substitutions g :  greak lowercase :γ, δ, μ ...
**)

Inductive preContext : Set :=
| pctx_one : preContext
| pctx_ext (Γ : preContext) (A : preType) : preContext

with preType : Set :=
| ptyp_base : preType
| ptyp_prod (A B : preType) : preType
| ptyp_func (A B : preType) : preType
| ptyp_subs (A : preType) (y : preSubs) : preType

with preTerm : Set :=
| ptrm_qar : preTerm
| ptrm_pair (a b : preTerm) : preTerm
| ptrm_fst  (p : preTerm) : preTerm
| ptrm_snd  (p : preTerm) : preTerm
| ptrm_abs  (b : preTerm) : preTerm
| ptrm_app  (f a : preTerm) : preTerm
| ptrm_subs (a : preTerm) (y : preSubs) : preTerm
| ptrm_conv (e : preTerm) : preTerm

with preSubs : Set :=
| psub_id   : preSubs
| psub_comp (y1 y2 : preSubs) : preSubs
| psub_weak : preSubs
| psub_Bang : preSubs
| psub_ext  (y : preSubs) (a : preTerm) : preSubs
.

(** End Syntax definitions **)


(** Notations **)

Declare Scope ctx_scope.
Open Scope ctx_scope.
Delimit Scope ctx_scope with ctx.

Notation "1" := pctx_one.
Notation "Γ # A" := (pctx_ext Γ A) (at level 1, left associativity, format "Γ # A") : ctx_scope.

#[add_top] Bind Scope ctx_scope with preContext preType.

Check (1).

Declare Scope ty_scope.
Open Scope ty_scope.
Delimit Scope ty_scope with ty.

Notation base := ptyp_base.
Infix "*"      := ptyp_prod (at level 40,left associativity): ty_scope.
Infix "-->"     := ptyp_func : ty_scope.
Notation "A [ y ]" := (ptyp_subs A y) : ty_scope.

#[add_top] Bind Scope ty_scope with preType preSubs preContext.

Check (base).
Check (1 # base).
Check (base * base --> base).
Check ( (base * base --> base) [ psub_id ] ).

Declare Scope term_scope.
Open Scope term_scope.
Delimit Scope term_scope with term.

Notation q := ptrm_qar.
Notation "( a , b )" := (ptrm_pair a b) (no associativity): term_scope.
Notation "'fst' p" := (ptrm_fst p) (at level 20): term_scope.
Notation "'snd' p" := (ptrm_snd p) (at level 20): term_scope.
Notation "'λ' ( b )" := (ptrm_abs b) (at level 20): term_scope.
Notation "app( f , a )" := (ptrm_app f a) (at level 20): term_scope.
Notation "a [ y ]" := (ptrm_subs a y)(at level 1): term_scope.
Notation "'conv' e" := (ptrm_conv e) (at level 20): term_scope.

#[add_top] Bind Scope term_scope with preTerm.

Check ( q ).
Print Visibility term_scope.
Check (q, q).
Check ( fst ( q , q ) ).
Check ( snd ( q , q ) ).
Check ( λ ( q ) ).
Check ( app( λ ( q ) , q ) ).

Declare Scope subs_scope.
Open Scope subs_scope.
Delimit Scope subs_scope with subs.

Notation Id := psub_id.
Notation p  := psub_weak.
Notation "!" := psub_Bang (at level 0).
Notation "y1 ∘ y0" := (psub_comp y1 y0) (at level 1, left associativity) : subs_scope.
Notation "y # a" := (psub_ext y a)(at level 1, left associativity, format "y # a") : subs_scope.

#[add_top] Bind Scope subs_scope with preSubs.

Check ( Id ).
Check ( p ).
Check ( ! ).
Check ( Id ∘ p ).
Check ( Id # q ).

(** End Notations **)

Reserved Notation "[ ⊢ Γ 'Cx' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"     (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]" (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y ~ Γ ]" (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A1 == A2 'type' ]" (at level 0, no associativity) .
Reserved Notation "[ Γ ⊢ a '==' b @ A ]" (at level 0, no associativity) .
Reserved Notation "[ Δ ⊢ y == y' ~ Γ ]" (at level 0, no associativity).


(** Judgments **)
Inductive  ContextJG : preContext -> Prop :=
   | context_empty :
      [ ⊢ 1 Cx ]
   | context_extend {Γ : preContext} {A : preType} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ A type ]
      -> [ ⊢  Γ # A Cx]

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
   | subs_bang {Γ} :
      [ ⊢ Γ Cx ]
      -> [ Γ ⊢ ! ~ 1 ]
   | subs_ext {Δ Γ} {y} {a A} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A[y] ]
      ->  [ Δ ⊢ (y # a) ~ (Γ # A) ]

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
      (* [ Γ ⊢ B type ] -> *)
      [ Γ # A ⊢ b @ B [p] ]
      -> [ Γ ⊢ λ (b) @ (A --> B) ]
   | term_app {Γ A B f a} :
      (* [ Γ ⊢ B type ] ->  *)
      [ Γ ⊢ f @ (A --> B) ] -> [ Γ ⊢ a @ A ]
      -> [ Γ ⊢ app(f, a) @ B ]
   | term_subs {Δ Γ} {y} {A} {a} :
      [ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
      -> [ Δ ⊢ (a [y]) @ (A [y]) ]
   (* TODO : Maybe provable using that 1 ⊢ A == B type, 1.A = 1.B, so A [Id] == B *)
   | term_conv {Γ} {A B} {e} :
      [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ]
      -> [ Γ ⊢ e @ B ]
   | term_equiv {Γ} {A} {a b} :
      [ Γ ⊢ a @ A ] -> [ Γ ⊢ a == b @ A ]
      -> [ Γ ⊢ b @ A ]

(*** Equivalence Relations ***)
(**** Substitution Equivalence ****)
with eq_subs : preContext -> preContext -> relation (preSubs) :=
(** Symmetric Transitive Closure **)
| eq_subs_sym {Δ Γ} {y1 y2} : [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y1 ~ Γ ]
| eq_subs_trans {Δ Γ} {y1 y2 y3} : [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ] -> [ Δ ⊢ y1 == y3 ~ Γ ]
(** Enforce composition properties (unital + associative) p.31 **)
| eq_subs_left_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ Id ∘ y == y ~ Γ ]
| eq_subs_right_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y ∘ Id == y ~ Γ ]
| eq_subs_comp_assoc {Γ3 Γ2 Γ1 Γ0} {y0 y1 y2} :
   [ Γ3 ⊢ y2 ~ Γ2 ] -> [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0]
   -> [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ0 ]
(** βη-equivalence for substitution p.34 **)
| eq_subs_beta {Δ Γ A a y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ p ∘ (y # a) == y ~ Γ ]
| eq_subs_eta {Δ Γ A y} :
   [ Γ ⊢ A type ] -> [ Δ ⊢ y ~ Γ # A ]
   -> [ Δ ⊢ y == ((p ∘ y) # (q[y])) ~ (Γ # A) ]
(** Unicity of bang p.34 **)
| eq_subs_bang {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ]
   -> [ Γ ⊢ ! == δ ~ 1 ]

(**** Type Equivalence ****)
with eq_type : preContext -> relation (preType) :=
(** Symmetric Transitive Closure **)
| eq_type_sym {Γ} {A B} :  [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == A type ]
| eq_type_trans {Γ} {A B C} : [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == C type ]   -> [ Γ ⊢ A == C type ]
(** Compatibility with substitution p.32 **)
| eq_type_subs {Δ Γ} {y} {A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A == B type ]
   -> [ Δ ⊢ A [y]%ty == B [y]%ty type ]
| eq_type_subs_id {Γ A} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A [ Id ] == A type ]%ty
| eq_type_subs_comp {Γ Γ1 Γ0} {A} {y1} {y0} :
   [ Γ ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]%ty

with eq_term : preContext -> preType -> relation (preTerm) :=
(** Symmetric Transitive Closure **)
| eq_term_sym {Γ A} {a b} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == a @ A ]
| eq_term_trans {Γ A} {a b c} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == c @ A ] -> [ Γ ⊢ a == c @ A ]
(** Compatibility with substitution p.32 **)
(* | eq_term_subs {Δ Γ} {y d} {A} {a b} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ a == b @ A ]
   -> [ Δ ⊢ a [y] == b [d] @ A[y] ] *)
| eq_term_subs_id {Γ} {A a} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ Id ] == a @ A ]
| eq_term_subs_comp {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1] == a [y0] [y1] @ A [y0 ∘ y1] ]
(** βη-equivalence for pairs p.22 **)
| eq_term_beta_fst {Γ} {A B} a b :
   [ Γ ⊢ a @ A] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ fst (a, b) == a @ A ]
| eq_term_beta_snd {Γ} {A B} a b :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ snd (a, b) == b @ B ]
| eq_term_eta_pair {Γ} {A B} p :
   [ Γ ⊢ p @ A * B ]
   -> [ Γ ⊢ p == (fst p, snd p) @ A * B ]
(** βη-equivalence for abstractions p.22 **)
| eq_term_beta_app {Γ} {A B} {a b} :
   [ Γ # A ⊢ b @ B [p] ] -> [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ app( λ (b) , a ) == b [ Id # a] @ B ]
| eq_term_eta_app {Γ} {A B} {f} :
   [ Γ ⊢ f @ (A --> B) ]
   -> [ Γ ⊢ f == (λ (app(f [p], q))) @ (A --> B) ]
(** βη-equivalence for substitution extension p.34 **)
| eq_term_beta_quar {Δ} {Γ} {y} {A} {a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ]

where "[ ⊢ Γ 'Cx' ]"       := (ContextJG Γ) : ctx_scope
and "[ Γ ⊢ A 'type' ]"     := (TypeJG Γ A) : ty_scope
and "[ Γ ⊢ a @ A ]" := (TermJG Γ A a): term_scope
and "[ Δ ⊢ y ~ Γ ]" := (SubsJG Δ Γ y): subs_scope
and "[ Γ ⊢ A1 == A2 'type' ]" := (eq_type Γ A1 A2) : ty_scope
and "[ Γ ⊢ a '==' b @ A ]" := (eq_term Γ A a b) : term_scope
and "[ Δ ⊢ y == y' ~ Γ ]" := (eq_subs Δ Γ y y') : subs_scope
.
(** End Jugements *)

(** Context Equality p.31, not sure what to do there **)
Axiom context_equality :
forall Γ, [ ⊢ Γ Cx ] ->
(forall A B, [ Γ ⊢ A == B type ] -> Γ # A = Γ # B)%ctx.

Fixpoint eq_context Γ Δ : Prop :=
match Γ, Δ with
| 1, 1 => True
| Γ' # A%ctx, Δ' # B%ctx  => eq_context Γ' Δ' /\ [Γ' ⊢ A == B type]
| _, _ => False
end.

(** End Context Equality **)

Example Ex1 : ([1 ⊢ base * base --> base type ]).
Proof.
   apply type_func.
   - apply type_prod; apply type_base; apply context_empty.
   - apply type_base. apply context_empty.
Qed.

(** Setoid declarations **)
(**** Register relations ****)
Add Parametric Relation Δ Γ : (preSubs) (eq_subs Δ Γ)
   symmetry proved by (@eq_subs_sym Δ Γ)
   transitivity proved by (@eq_subs_trans Δ Γ)
   as eq_subs_rel.

Add Parametric Morphism Δ Γ : (eq_subs Δ Γ)
   with signature (eq_subs Δ Γ ==> eq_subs Δ Γ ==> iff)
   as eq_subs_mor.
Proof.
   intros y1 y2 H_eq1 y3 y4 H_eq2;
   split; intro H; [symmetry in H_eq1 | symmetry in H_eq2];
   apply (eq_subs_trans H_eq1 (eq_subs_trans H H_eq2)).
Qed.

Add Parametric Relation Γ : (preType) (eq_type Γ)
   symmetry proved by (@eq_type_sym Γ)
   transitivity proved by (@eq_type_trans Γ)
   as eq_type_rel.

Add Parametric Morphism Γ : (eq_type Γ)
   with signature (eq_type Γ ==> eq_type Γ ==> iff)
   as eq_type_mor.
Proof.
   intros A1 B1 H_eq1 A2 B2 H_eq2.
   split; intro H; [symmetry in H_eq1 | symmetry in H_eq2];
   apply (eq_type_trans H_eq1 (eq_type_trans H H_eq2)).
Qed.

Add Parametric Relation Γ A : (preTerm) (eq_term Γ A)
   symmetry proved by (@eq_term_sym Γ A)
   transitivity proved by (@eq_term_trans Γ A)
   as eq_term_rel.

Add Parametric Morphism Γ A : (eq_term Γ A)
   with signature (eq_term Γ A ==> eq_term Γ A ==> iff)
   as eq_term_mor.
Proof.
   intros a1 b1 H_eq1 a2 b2 H_eq2.
   split; intro; [symmetry in H_eq1 | symmetry in H_eq2];
   apply (eq_term_trans H_eq1 (eq_term_trans H H_eq2)).
Qed.
(**** End relations registration ****)

(** Reflexivity lemmas **)
Lemma eq_type_refl {Γ A} : [ Γ ⊢ A type ] -> [ Γ ⊢ A == A type ].
Proof.
   intro H.
   rewrite <- (eq_type_subs_id H) at 1.
   apply (eq_type_subs_id H).
Qed.

Lemma eq_term_refl {Γ A a} : [ Γ ⊢ a @ A ] -> [ Γ ⊢ a == a @ A ].
Proof.
   intro H.
   rewrite <- (eq_term_subs_id H) at 1.
   apply (eq_term_subs_id H).
Qed.

Lemma eq_subs_refl {Δ Γ y} : [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y == y ~ Γ ].
Proof.
   intro H.
   rewrite <- (eq_subs_left_id H) at 1.
   apply (eq_subs_left_id H).
Qed.
(** End reflexivity lemmas **)


(*** Fundamental property ***)
Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_jug_eq_type_mor.
Proof.
   intros A B Heq e.
   split; intro; [ | symmetry in Heq];
   apply (term_conv H Heq).
Qed.

Add Parametric Morphism Γ A : (TermJG Γ A)
   with signature (eq_term Γ A ==> iff)
   as term_jug_eq_term_mor.
Proof.
   intros a b Heq.
   split; intro; [ | symmetry in Heq];
    apply (term_equiv H Heq).
Qed.

Lemma eq_term_eq_type_mor' {Γ} {A B : preType} {a b : preTerm} :
[Γ ⊢ a == b @ A] ->
[Γ ⊢ A == B type ] ->  [Γ ⊢ a == b @ B].
Proof.
   intros Heq_term Heq_type.
   dependent induction Heq_term generalizing B; try (tauto).
   - symmetry. apply (IHHeq_term _ Heq_type).
   - transitivity b; [apply (IHHeq_term1 _ Heq_type) | apply (IHHeq_term2 _ Heq_type)].
   - apply (eq_term_subs_id). apply (term_conv H Heq_type).
   - apply (term_subs(subs_comp H H0)) in H1 as H2.
      rewrite Heq_type in H2.
      inversion H2; subst.
      inversion H7; subst.
      apply (eq_term_subs_comp H9 H10 H8).
      + admit.
      + admit. (** Check in Derive inversion Pattern **)
   -  rewrite Heq_type in H.
      apply (eq_term_beta_fst _ _ H H0).
   -  rewrite Heq_type in H0.
      apply (eq_term_beta_snd _ _ H H0).
   - apply (eq_term_eta_pair) in H as Heta.
      remember H as H1; clear HeqH1.
      rewrite Heta in H.
      rewrite Heq_type in H.
      inversion H; subst.
      rewrite Heq_type in H1.
      apply (eq_term_eta_pair _ H1).
         admit. (** Check in Derive inversion Pattern **)
         admit. (** Check in Derive inversion Pattern **)
   - eapply (eq_term_beta_app).
      2: apply H0.
      eapply (eq_type_subs _) in Heq_type.
      rewrite Heq_type in H.
      apply H.
      Unshelve.
      admit.
   - apply (eq_term_eta_app) in H as Heta.
      remember H as Hf; clear HeqHf.
      rewrite Heta in H.
      rewrite Heq_type in H.
      inversion H; subst.
      rewrite Heq_type in Hf.
      apply (eq_term_eta_app Hf).
         admit. (** Check in Derive inversion Pattern **)
         admit. (** Check in Derive inversion Pattern **)
   - apply (eq_term_beta_quar H H0) in H1 as Hbeta.
      remember H1 as H2; clear HeqH2.
      rewrite <- Hbeta in H1.
      rewrite Heq_type in H1.
         admit. (** Check in Derive inversion Pattern **)
Admitted.



Add Parametric Morphism Γ : (eq_term Γ)
   with signature (eq_type Γ ==> eq ==> eq ==> iff)
   as eq_term_eq_type_mor.
Proof.
   intros A B HeqT a b.
   split; intro Heq.
      apply (eq_term_eq_type_mor' Heq HeqT).
      symmetry in HeqT.
      apply (eq_term_eq_type_mor' Heq HeqT).
Qed.

(** "Presupositions" Theorems **)
Theorem type_pres {Γ A}:
   [ Γ ⊢ A type ] -> [ ⊢ Γ Cx ].
Proof.
   intros.
   dependent induction H; try (tauto).
   dependent induction H generalizing A; intros; try (tauto).
   - apply (IHSubsJG1 (A [y0]%ty) (type_subs H0 H1)
            (IHSubsJG2 A H1 IHTypeJG )).
   - apply (context_extend IHTypeJG H).
   - inversion IHTypeJG; subst.
      apply (IHSubsJG A0 H0 H5).
Qed.

(**** helper ****)
Corollary ctx_ext {Γ A} :
   [ Γ ⊢ A type ] -> [ ⊢ Γ # A Cx ].
Proof.
   intro H.
   apply type_pres in H as H_ctx.
   apply context_extend; assumption.
Qed.

Corollary type_weak {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ # A ⊢ A [p] type ].
Proof. apply (fun H => type_subs (subs_weak H) H). Qed.

Corollary type_id {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A [Id] type ]%ty.
Proof. apply (fun H => type_subs  (subs_id (type_pres H)) H). Qed.

(**** End Helpers ****)

Theorem eq_type_pres :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
   intros.
   dependent induction H; try (tauto).
   split; apply (type_subs H); apply IHeq_type.
   split; [apply (type_id H) | apply H].
   split.
      apply (type_subs (subs_comp H H0) H1).
      apply (type_subs H (type_subs H0 H1)).
Qed.

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as preType_mor.
Proof.
   intros A B Heq.
   apply eq_type_pres in Heq as [H_A H_B].
   tauto.
Qed.

Theorem term_pres {Γ A a}:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intros H.
   dependent induction H.
   apply (type_weak H).
   apply type_prod; [apply IHTermJG1 | apply IHTermJG2].
   inversion IHTermJG; assumption.
   inversion IHTermJG; assumption.
   inversion IHTermJG; inversion H3; apply (type_func H8 H4).
   inversion IHTermJG1; assumption.
   apply (type_subs H IHTermJG).
   rewrite <- H0. assumption.
   assumption.
Qed.

Corollary term_pres_ctx {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ ⊢ Γ Cx ].
Proof. apply (fun H => type_pres (term_pres H)). Qed.

Corollary term_subs_compose {Δ Γ A a y1 y0} :
   [ Δ ⊢ y0 ~ Γ ]
   -> [ Γ ⊢ a @ A [y1] ]
   -> [ Δ ⊢ a [y0] @ A [y1 ∘ y0] ].
Proof.
   intros H_y0 H_a.
   remember (term_pres H_a) as HA.
   inversion HA; subst.
   rewrite (eq_type_subs_comp H_y0 H2 H3).
   apply (term_subs H_y0 H_a).
Qed.

Corollary term_id {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a [Id] @ A ].
Proof.
   intro H.
   rewrite <- (eq_type_subs_id (term_pres H)).
   apply (term_subs (subs_id (term_pres_ctx H)) H).
Qed.

Corollary term_id_type {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ A [Id] ].
Proof.
   intro H.
   rewrite (eq_type_subs_id (term_pres H)).
   apply H.
Qed.

Theorem subs_pres {Δ Γ y}:
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ Cx ] /\ [ ⊢ Γ Cx ].
Proof.
   intros.
   dependent induction H; try(tauto).
   split; [apply (ctx_ext H) | apply (type_pres H)].
   split; [tauto | constructor].
   split; [tauto | apply (ctx_ext H0)].
Qed.

Theorem eq_subs_pres {Δ Γ y1 y0}:
   [ Δ ⊢ y1 == y0 ~ Γ ] -> [ Δ ⊢ y1 ~ Γ ] /\ [ Δ ⊢ y0 ~ Γ ].
Proof.
   intros.
   dependent induction H; try (tauto).
   -  split. 2:assumption.
      apply subs_pres in H as H1.
      destruct H1 as [HΔ HΓ].
      apply (subs_comp H (subs_id HΓ)).
   -  split. 2:assumption.
      apply subs_pres in H as H1.
      destruct H1 as [HΔ HΓ].
      apply (subs_comp (subs_id (HΔ)) H).
   -  split.
      apply (subs_comp (subs_comp H H0) H1).
      apply (subs_comp H (subs_comp H0 H1)).
   -  split. 2:assumption.
      apply (subs_comp
         (subs_ext H H0 H1)
         (subs_weak H0)).
   -  split. assumption.
      apply (subs_ext (subs_comp H0 (subs_weak H)) H).
      apply (term_subs_compose H0 (term_qar H)).
   - split. 2:assumption.
      apply (subs_bang).
      apply (subs_pres H).
Qed.

Add Parametric Morphism Δ Γ : (SubsJG Δ Γ)
   with signature (eq_subs Δ Γ ==> iff)
   as subs_mor.
Proof.
   intros y d Heq.
   apply eq_subs_pres in Heq as [H_y H_d].
   tauto.
Qed.

Corollary self_extension {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ (Id # a) ~ (Γ # A) ].
Proof.
   intro H.
   apply (subs_ext
            (subs_id (term_pres_ctx H))
            (term_pres H)
            (term_id_type H)).
Qed.

Corollary eq_subs_beta_id {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ p ∘ (Id # a) == Id ~ Γ ].
Proof.
   intro H.
   apply (eq_subs_beta
         (subs_id (term_pres_ctx H))
         (term_pres H)
         (term_id_type H)).
Qed.

Theorem eq_term_pres_left {Γ A a b}:
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   rewrite <- Heq; apply IHHeq.
   apply (term_id H).
   apply (term_subs (subs_comp H H0) H1).
   apply (term_fst (term_pair H H0)).
   apply (term_snd (term_pair H H0)).
   apply (term_app (term_abs H) H0).
   rewrite (eq_term_beta_quar H H0 H1).
      apply H1.
Qed.

Theorem eq_term_pres_right {Γ A a b}:
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b @ A ].
Proof.
   intros H.
   apply (term_equiv (eq_term_pres_left H) H).
Qed.

Theorem eq_term_pres {Γ A a b}:
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
   intros H.
   split; [ apply (eq_term_pres_left H) | apply (eq_term_pres_right H) ].
Qed.
(** "Presupositions" Theorems **)

Scheme eq_subs_elim := Elimination for eq_subs Sort Prop.
Scheme eq_subs_ind2 := Induction for eq_subs Sort Prop.
Scheme eq_subs_case := Case for eq_subs Sort Prop.

Scheme eq_subs_eq_type := Minimality for eq_subs Sort Prop
   with eq_type_eq_subs := Minimality for eq_type Sort Prop.

Scheme eq_subs_eq_type_ind := Induction for eq_subs Sort Prop
   with eq_type_eq_subs_ind := Induction for eq_type Sort Prop.

Check eq_subs_eq_type.

Combined Scheme eq_subs_eq_type2 from eq_subs_eq_type_ind,eq_type_eq_subs_ind.

Check eq_subs_eq_type2.


Lemma eq_type_subs1 {Δ Γ y d A} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ A type ]
   -> [ Δ ⊢ A[y]%ty == A[d]%ty type ].
Proof.
   intros Heq H_A.
   dependent induction Heq generalizing A; try (tauto).
   - symmetry. apply (IHHeq _ H_A).
   - transitivity (A[y2]%ty).
      apply (IHHeq1 _ H_A).
      apply (IHHeq2 _ H_A).
   - rewrite (eq_type_subs_comp (H) (subs_id (type_pres H_A)) H_A).
      apply (eq_type_subs H).
      apply (eq_type_subs_id H_A).
   -  apply (subs_pres) in H as H1.
      destruct H1 as [HΔ HΓ].
      rewrite (eq_type_subs_comp (subs_id HΔ) H H_A).
      apply (eq_type_subs_id (type_subs H H_A)).
   - rewrite (eq_type_subs_comp (subs_comp H H0) H1 H_A).
      rewrite (eq_type_subs_comp H H0 (type_subs H1 H_A)).
      rewrite (eq_type_subs_comp H (subs_comp H0 H1) H_A).
      apply (eq_type_subs H).
      symmetry.
      apply (eq_type_subs_comp H0 H1 H_A).
   - admit.
Admitted.

Lemma eq_subs_ext1 {Δ Γ y d A a} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ A type ]
   -> [ Δ ⊢ (y # a) == (d # a) ~ Γ # A ].
Proof.
   intros Heq HA.
   dependent induction Heq generalizing A a; try (tauto).
   - symmetry. apply (IHHeq _ _ HA).
   - transitivity (y2 # a).
      apply (IHHeq1 _ _ HA).
Abort.

Add Parametric Morphism Δ Γ y A: (psub_ext y)
   with signature (eq_term Δ (A[y]) ==> eq_subs Δ (Γ # A))
   as term_jug_eq_term_mor'.
Proof.
   intros a1 a2 Heq.
   dependent induction Heq generalizing Γ; try (tauto).
   - symmetry. apply IHHeq. reflexivity.
   - transitivity (y # b).
      apply (IHHeq1); reflexivity.
      apply (IHHeq2); reflexivity.
- Abort.


Lemma eq_sub_ext {Δ Γ y d A a b} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Δ ⊢ a == b @ A[y] ]
   -> [ Δ ⊢ (y # a) == (d # b) ~ Γ # A ].
Admitted.


Lemma eq_subs_comp {Γ2 Γ1 Γ0} {y1 y0 d1 d0} :
   [ Γ2 ⊢ y1 == d1 ~ Γ1 ] -> [ Γ1 ⊢ y0 == d0 ~ Γ0 ]
   -> [ Γ2 ⊢ (y0 ∘ y1) == (d0 ∘ d1) ~ Γ0 ].
Admitted.

Lemma eq_term_subs {Δ Γ y A a b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a == b @ A ]
   -> [ Δ ⊢ a [y] == b [y] @ A[y] ].
Admitted.



(** Exercises **)
(*** Exercise 2.2. Show that substitutions Γ ⊢𝛾 : Γ.𝐴
satisfying p ◦𝛾= id are in bijection with terms Γ ⊢𝑎: 𝐴. ***)

(***Exercise 2.3. Show that (𝛾.𝑎)◦𝛿= (𝛾◦𝛿).𝑎[𝛿]. ***)
Lemma Exercise_2_3 {Γ2 Γ1 Γ0 A a y δ} :
   [ Γ1 ⊢ y ~ Γ0 ] -> [ Γ2 ⊢ δ ~ Γ1 ] -> [ Γ0 ⊢ A type ] -> [ Γ1 ⊢ a @ A[y] ]
   -> [ Γ2 ⊢ (y # a) ∘ δ == (y ∘ δ) # (a [δ]) ~ Γ0 # A ].
Proof.
   intros H_y H_δ H_A H_a.
   - rewrite (eq_subs_eta H_A).
      assert ([ Γ2 ⊢ p ∘ (y#a ∘ δ) == y ∘ δ ~ Γ0 ]).
      {
         rewrite (eq_subs_comp_assoc H_δ (subs_ext H_y H_A H_a) (subs_weak H_A)).
         apply (eq_subs_comp (eq_subs_refl H_δ)).
         apply (eq_subs_beta H_y H_A H_a).
      }
      apply (eq_sub_ext H).
      rewrite (eq_type_subs_comp (subs_comp H_δ (subs_ext H_y H_A H_a)) (subs_weak H_A) H_A).
      rewrite (eq_term_subs_comp H_δ (subs_ext H_y H_A H_a) (term_qar H_A)).
      rewrite (eq_type_subs_comp H_δ (subs_ext H_y H_A H_a) (type_subs(subs_weak H_A) H_A)).
      apply (eq_term_subs H_δ).
      rewrite <- (eq_type_subs_comp (subs_ext H_y H_A H_a) (subs_weak H_A) H_A).
      rewrite (eq_type_subs1 (eq_subs_beta H_y H_A H_a) H_A).
      apply (eq_term_beta_quar H_y H_A H_a).
      apply (subs_comp H_δ (subs_ext H_y H_A H_a)).
Qed.

(*** Exercise 2.4. Given Δ ⊢𝛾 : Γ and Γ ⊢ A type, construct a substitution that we will
name y.A, satisfying Δ.A[y]⊢𝛾.A: Γ.A. ***)
Lemma Exercise_2_4 {Δ Γ A y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
   -> exists yA, [ Δ # (A[y]%ty) ⊢ yA ~ (Γ # A) ].
Proof.
   intros H_subs H_type.
   remember (type_subs H_subs H_type) as A_subs.
   remember (subs_weak A_subs) as weak_subs.
   eexists (_ # _).
   eapply (subs_ext).
   eapply (subs_comp weak_subs H_subs).
   apply (H_type).
   rewrite (eq_type_subs_comp (subs_weak A_subs) H_subs H_type).
   apply (term_qar (type_subs H_subs H_type)).
Qed.

Corollary subs_yA {Δ Γ A y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
   -> [ Δ # (A[y]%ty) ⊢ (y ∘ p) # q ~ (Γ # A) ].
Proof.
   intros H_subs H_type.
   apply (subs_ext
      (subs_comp (subs_weak (type_subs H_subs H_type)) H_subs)
      H_type
      ).
   rewrite (eq_type_subs_comp (subs_weak (type_subs H_subs H_type)) H_subs H_type).
   apply (term_qar (type_subs H_subs H_type)).
Qed.

(*** Exercise 2.5. Suppose that Γ ⊢A type and ⊢Δ cx. Show that substitutions Δ ⊢𝛾 : Γ.A
are in bijection with pairs of a substitution Δ ⊢y0 : Γ and a term Δ ⊢𝑎: A[y0]. ***)

