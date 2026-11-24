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

Inductive preSubs : Type :=
| psub_weak : preSubs
| psub_id   : preSubs
| psub_comp (y1 y2 : preSubs) : preSubs
| psub_ext  (y : preSubs) (a : preTerm) : preSubs

with preType : Type :=
| ptyp_base : preType (* not really in the book but needed for logical consistency *)
| ptyp_subs (A : preType) (y : preSubs) : preType

with preTerm : Type :=
| ptrm_qar : preTerm
| ptrm_subs (a : preTerm) (y : preSubs) : preTerm
.


Inductive preCtx :  Type :=
| pctx_one : preCtx
| pctx_ext (Γ : preCtx) (A : preType) : preCtx
.

(* Coercion ctx_size (Γ : preCtx) : nat := 0. *)
(* Definition preContext : Type := forall n, preCtx n. *)
(** End Syntax definitions **)


(** Notations **)

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
#[add_top] Bind Scope ctx_scope with preCtx.

Declare Scope subs_scope.
Delimit Scope subs_scope with subs.
#[add_top] Bind Scope subs_scope with preSubs.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
#[add_top] Bind Scope ty_scope with preType.

Declare Scope term_scope.
Delimit Scope term_scope with term.
#[add_top] Bind Scope term_scope with preTerm.


Notation "1" := (pctx_one).

Notation "Γ # A" := (pctx_ext Γ A) (at level 2, left associativity) : ctx_scope.

Notation id        := psub_id.
Notation p         := psub_weak.
Notation "y1 ∘ y0" := (psub_comp y1 y0) (at level 100, right associativity) : subs_scope.
Notation "y # a"   := (psub_ext y a)(at level 2, left associativity) : subs_scope.

Notation b         := ptyp_base.
Notation "A [ y ]" := (ptyp_subs A y) (at level 1): ty_scope.

Notation q            := ptrm_qar.
Notation "a [ y ]"    := (ptrm_subs a y)(at level 1): term_scope.

Check (1 # b)%ctx.



Reserved Notation "[ ⊢ Γ 'cx' ]"          (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]"         (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y ~ Γ ]"         (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A == B 'type' ]" (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a == b @ A ]"    (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y == d ~ Γ ]"    (at level 0, no associativity).

(** End Notations **)

(** Pre-equivalence relations **)
Inductive preq_ctx : preCtx -> preCtx -> Prop :=
| preq_ctx_one : preq_ctx 1 1
| preq_ctx_ext : forall Γ Δ A B, preq_ctx Γ Δ -> preq_type A B -> preq_ctx (Γ # A) (Δ # B)

with preq_subs : preSubs -> preSubs -> Prop :=
| preq_subs_refl : forall y, preq_subs y y
| preq_subs_id_left : forall y, preq_subs (id ∘ y) y
| preq_subs_id_right : forall y, preq_subs y (y ∘ id)
| preq_subs_comp_assoc : forall y0 y1 y2, preq_subs (y0 ∘ (y1 ∘ y2)) ((y0 ∘ y1) ∘ y2)
| preq_subs_comp : forall y0 y1 y0' y1', preq_subs y0 y0' -> preq_subs y1 y1' -> preq_subs (y0 ∘ y1) (y0' ∘ y1')
| preq_subs_ext : forall y1 y2 a1 a2, preq_subs y1 y2 -> preq_term a1 a2 -> preq_subs (y1 # a1) (y2 # a2)
| preq_subs_beta : forall y a, preq_subs (p ∘ y # a) y
| preq_subs_eta : forall y, preq_subs y ((p ∘ y) # q[y])
| preq_subs_sym : forall y1 y2, preq_subs y1 y2 -> preq_subs y2 y1
| preq_subs_trans : forall y1 y2 y3, preq_subs y1 y2 -> preq_subs y2 y3 -> preq_subs y1 y3

with preq_type : preType -> preType -> Prop :=
| preq_type_refl : forall A, preq_type A A
| preq_type_subs_id {A : preType} : preq_type (A [id]) A
| preq_type_subs_comp {A : preType} {y1 y0 : preSubs} : preq_type (A [ y0 ∘ y1]) (A [y0] [y1])
| preq_type_subs_morp : forall A1 A2 y1 y2, preq_type A1 A2 -> preq_subs y1 y2 -> preq_type (A1 [y1]) (A2 [y2])
| preq_type_sym : forall A B, preq_type A B -> preq_type B A
| preq_type_trans : forall A B C, preq_type A B -> preq_type B C -> preq_type A C

with preq_term : preTerm -> preTerm -> Prop :=
| preq_term_refl : forall a, preq_term a a
| preq_term_subs_id {a : preTerm} : preq_term (a [id]) a
| preq_term_subs_comp {y1 : preSubs} {y0 : preSubs} {a : preTerm} : preq_term (a [ y0 ∘ y1 ]) (a [ y0 ] [ y1 ])
| preq_term_subs_morp : forall a1 a2 y1 y2, preq_term a1 a2 -> preq_subs y1 y2 -> preq_term (a1 [y1]) (a2 [y2])
| preq_term_beta_qar {y : preSubs} {a : preTerm} : preq_term (q [ y # a ]) a
| preq_term_sym : forall a b, preq_term a b -> preq_term b a
| preq_term_trans : forall a b c, preq_term a b -> preq_term b c -> preq_term a c
(* subs extension ? *)
.

Lemma preq_ctx_refl : forall Γ, preq_ctx Γ Γ.
Proof.
	intros Γ.
	induction Γ.
	now constructor.
	apply preq_ctx_ext.
	assumption.
	now constructor.
Qed.

Lemma preq_ctx_sym : forall Γ Δ, preq_ctx Γ Δ -> preq_ctx Δ Γ.
Proof.
	intros Γ Δ Heq.
	induction Heq.
	now constructor.
	apply preq_ctx_ext.
	assumption.
	now constructor.
Qed.

Lemma preq_ctx_trans : forall Γ Δ Θ, preq_ctx Γ Δ -> preq_ctx Δ Θ -> preq_ctx Γ Θ.
Proof.
	intros Γ Δ Θ Heq1 Heq2.
	dependent induction Heq1 generalizing Θ.
	assumption.
	inversion Heq2; subst.
	apply preq_ctx_ext.
	now apply IHHeq1.
	now apply (preq_type_trans _ _ _ H H4).
Qed.

(** End Pre-equivalence relations **)

Add Relation preCtx (preq_ctx)
	reflexivity proved by (preq_ctx_refl)
	symmetry proved by (preq_ctx_sym)
	transitivity proved by (preq_ctx_trans)
  as preq_ctx_rel.

Add Relation preSubs (preq_subs)
	reflexivity proved by (preq_subs_refl)
	symmetry proved by (preq_subs_sym)
	transitivity proved by (preq_subs_trans)
  as preq_subs_rel.

Add Relation preType (preq_type)
	reflexivity proved by (preq_type_refl)
	symmetry proved by (preq_type_sym)
	transitivity proved by (preq_type_trans)
	as preq_type_rel.

Add Relation preTerm (preq_term)
	reflexivity proved by (preq_term_refl)
	symmetry proved by (preq_term_sym)
	transitivity proved by (preq_term_trans)
	as preq_term_rel.

Add Parametric Morphism : pctx_ext
	with signature preq_ctx ==> preq_type ==> preq_ctx
as preq_ctx_ext_mor.
Proof.
	intros Γ1 Γ2 HeqΓ A1 A2 HeqA.
	now apply preq_ctx_ext.
Qed.

Add Parametric Morphism : psub_comp
	with signature preq_subs ==> preq_subs ==> preq_subs
as preq_subs_comp_mor.
Proof.
	intros y1 y1' Heq1 y2 y2' Heq2.
	now apply preq_subs_comp.
Qed.

Add Parametric Morphism : psub_ext
	with signature preq_subs ==> preq_term ==> preq_subs
as preq_subs_ext_mor.
Proof.
	intros y1 y2 Heq1 a1 a2 Heq2.
	now apply preq_subs_ext.
Qed.

Add Parametric Morphism : ptyp_subs
	with signature preq_type ==> preq_subs ==> preq_type
as preq_type_subs_mor.
Proof.
	intros A1 A2 Heq1 y1 y2 Heq2.
	now apply preq_type_subs_morp.
Qed.

Add Parametric Morphism : ptrm_subs
	with signature preq_term ==> preq_subs ==> preq_term
as preq_term_subs_mor.
Proof.
	intros a1 a2 Heq1 y1 y2 Heq2.
	now apply preq_term_subs_morp.
Qed.

Lemma preq_subs_ext_d : forall y1 y2 a, preq_subs (y1 # a ∘ y2) ((y1 ∘ y2) # a[y2]).
Proof.
	intros y1 y2 a.
	rewrite preq_subs_eta.
	rewrite preq_subs_comp_assoc.
	rewrite preq_subs_beta.
	rewrite preq_term_subs_comp.
	now rewrite preq_term_beta_qar.
Qed.

(******************************************************************************)
(** Quotients **)
Class Quotient (A : Type) (R : A -> A -> Prop) := {
	quot := A;
	q_comp : forall (x : A) (P : A -> Prop), (exists y : A, R x y /\ P y) -> P x;
}.

Instance Qctx : Quotient preCtx preq_ctx.
refine {|
	q_comp := fun x P => _;
|}.
intros [y [Heq H]].


(******************************************************************************)
(** Judgments **)

Inductive CtxJG : preCtx -> Prop :=
   | ctx_one :
      [ ⊢ 1 cx ]
   | ctx_ext {Γ : preCtx} {A : preType} :
      [ ⊢ Γ cx ] -> [ Γ ⊢ A type ]
      -> [ ⊢  Γ # A cx]

with SubsJG : preCtx -> preCtx -> preSubs -> Prop :=
   | subs_weak {Γ : preCtx} {A : preType} :
      [ Γ ⊢ A type ]
      -> [ (Γ # A)%ctx ⊢ p ~ Γ ]
   | subs_id {Γ : preCtx} :
      [ ⊢ Γ cx ]
      -> [ Γ ⊢ id ~ Γ ]
   | subs_comp {Γ2 Γ1 Γ0 : preCtx} {y1 y0 : preSubs} :
      [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ]
      ->[ Γ2 ⊢ (y0 ∘ y1) ~ Γ0 ]
   | subs_ext {Δ Γ : preCtx} {y : preSubs} {a : preTerm} {A : preType} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A[y] ]
      ->  [ Δ ⊢ (y # a) ~ (Γ # A) ]
	(** compatibility with quotient **)
	(* | subs_over_ctx_quot {Δ Γ : preCtx} {Δ' Γ' : preCtx} {y : preSubs} :
		[ Δ ⊢ y ~ Γ ] -> eq_ctx Δ Δ' -> eq_ctx Γ Γ'
		-> [ Δ' ⊢ y ~ Γ' ] *)

with TypeJG : preCtx -> preType -> Prop :=
   | type_base {Γ : preCtx} :
      [ ⊢ Γ cx ]
      -> [ Γ ⊢ b type ]
   | type_subs {Δ Γ : preCtx} {y : preSubs} {A : preType} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
      -> [ Δ ⊢ A [y] type ]
	(** compatibility with quotient **)
	(* | type_over_ctx_quot {Δ Γ : preCtx} {A : preType} :
		eq_ctx Δ Γ -> [ Δ ⊢ A type ] -> [ Γ ⊢ A type ] *)

with TermJG : preCtx -> preType -> preTerm -> Prop :=
(* The q term is a "generic element" of the type A, which can be substituted by any term of type A. *)
   | term_qar {Γ : preCtx} {A : preType} :
      [ Γ ⊢ A type ]
      -> [ Γ # A ⊢ q @ A [p] ]
   | term_subs {Δ Γ : preCtx} {y : preSubs} {A : preType} {a : preTerm} :
			[ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
			-> [ Δ ⊢ (a [y]) @ A [y] ]
	(** compatibility with quotient **)
	(* | term_over_ctx_quot {Δ Γ : preCtx} {A : preType} {a : preTerm} :
		[ Δ ⊢ a @ A ] -> eq_ctx Δ Γ -> [ Γ ⊢ a @ A ]
	| term_over_type_quot {Γ : preCtx} {A B : preType} {a : preTerm} :
		[ Γ ⊢ a @ A ] -> [ Γ ⊢ A == B type ] -> [ Γ ⊢ a @ B ] *)

(******************************************************************************)
(*** Equivalence Relations ***)
with eq_ctx : preCtx -> preCtx -> Prop :=
(* Symmetric Transitive Closure *)
(* | eq_ctx_sym {Γ Δ : preCtx} : eq_ctx Γ Δ -> eq_ctx Δ Γ *)
(* | eq_ctx_trans {Γ Δ Θ : preCtx} : eq_ctx Γ Δ -> eq_ctx Δ Θ -> eq_ctx Γ Θ *)
| eq_ctx_one : eq_ctx pctx_one pctx_one
| eq_ctx_ext :	forall (Γ Δ : preCtx) A B,
	eq_ctx Γ Δ -> [ Γ ⊢ A == B type ]
	(* -> [ Δ ⊢ A == B type ] *)
	-> eq_ctx (pctx_ext Γ A) (pctx_ext Δ B)

(**** Substitution Equivalence ****)
with eq_subs : preCtx -> preCtx -> preSubs -> preSubs -> Prop :=
(* Symmetric Transitive Closure *)
| eq_subs_sym {Δ Γ : preCtx} {y1 y2 : preSubs} :
	[ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y1 ~ Γ ]
| eq_subs_trans {Δ Γ : preCtx} {y1 y2 y3 : preSubs} :
	[ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ] -> [ Δ ⊢ y1 == y3 ~ Γ ]
(** Enforce composition properties (unital + associative) p.31 **)
| eq_subs_id_left {Δ Γ : preCtx} {y : preSubs}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ id ∘ y == y ~ Γ ]
| eq_subs_id_right {Δ Γ : preCtx} {y : preSubs}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y == y ∘ id ~ Γ ]
| eq_subs_comp_assoc {Δ Γ : preCtx} {y0 : preSubs} {y1 : preSubs} {y2 : preSubs} :
		[ Γ ⊢ y2 ~ Γ ] -> [ Γ ⊢ y1 ~ Γ ] -> [ Γ ⊢ y0 ~ Γ]
		-> [ Γ ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ ]
(** Unicity of bang p.34 **)
(* | eq_subs_bang {n : nat} {Γ : preCtx n} {δ : preSubs} :
   (* [ Γ ⊢ δ  ~ 1 ] *)
   (* -> [ Γ ⊢ ! == δ ~ 1 ] *)
	SubsJG n 0 Γ 1 δ -> eq_subs n 0 Γ 1 ! δ *)
(** βη-equivalence for substitution p.34 **)
| eq_subs_beta {Δ Γ : preCtx} {A : preType} {a : preTerm} {y : preSubs} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ p ∘ y # a == y ~ Γ ]
| eq_subs_eta {Δ Γ : preCtx} {A : preType} {y : preSubs} :
   [ Γ ⊢ A type ] -> [ Δ ⊢ y ~ Γ # A ]
   -> [ Δ ⊢ y == (p ∘ y) # q[y] ~ (Γ # A) ]

(**** Type Equivalence ****)
with eq_type : preCtx -> preType -> preType -> Prop :=
(* Symmetric Transitive Closure *)
| eq_type_sym {Γ : preCtx} {A B : preType} :
	[ Γ ⊢ A == B type ] -> [ Γ ⊢ B == A type ]
| eq_type_trans {Γ : preCtx} {A B C : preType} :
	[ Γ ⊢ A == B type ] -> [ Γ ⊢ B == C type ]   -> [ Γ ⊢ A == C type ]
(** Compatibility with substitution p.32 **)
| eq_type_subs_id {Γ : preCtx} {A : preType} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A [id] == A type ]
| eq_type_subs_comp {Γ2 Γ1 Γ0 : preCtx} {A : preType} {y1 y0 : preSubs} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ2 ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]

(**** Term Equivalence ****)
with eq_term : preCtx -> preType -> preTerm -> preTerm -> Prop :=
(* Symmetric Transitive Closure *)
| eq_term_sym {Γ : preCtx } {A : preType} {a b : preTerm} :
	[ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == a @ A ]
| eq_term_trans {Γ : preCtx} {A : preType} {a b c : preTerm} :
	[ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == c @ A ] -> [ Γ ⊢ a == c @ A ]
(** Compatibility with substitution p.32 **)
| eq_term_subs_id {Γ : preCtx} {A : preType} {a : preTerm} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ id ] == a @ A ]
| eq_term_subs_comp {Γ2 Γ1 Γ0 : preCtx} {y1 : preSubs} {y0 : preSubs} {A : preType} {a : preTerm} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1 ] == a [ y0 ] [ y1 ] @ A [y0 ∘ y1] ]
(** βη-equivalence for substitution extension p.34 **)
| eq_term_beta_qar {Δ Γ : preCtx} {y : preSubs} {A : preType} {a : preTerm} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ]

where "[ ⊢ Γ 'cx' ]"          := (CtxJG Γ)
and   "[ Δ ⊢ y ~ Γ ]"         := (@SubsJG Δ Γ y)
and   "[ Γ ⊢ A 'type' ]"      := (TypeJG Γ A)
and   "[ Γ ⊢ a @ A ]"         := (TermJG Γ A a)
and   "[ Δ ⊢ y == y' ~ Γ ]"   := (eq_subs Δ Γ y y')
and   "[ Γ ⊢ A == B 'type' ]" := (eq_type Γ A B)
and   "[ Γ ⊢ a == b @ A ]"    := (eq_term Γ A a b)
.
(** End Judgements *)

(******************************************************************************)
(** Register Equality Relations **)
Add Morphism eq_ctx with signature preq_ctx ==> preq_ctx ==> iff as eq_ctx_pmor.
Proof.
	intros Γ Δ Heq Γ' Δ' Heq'.
	split; intro IH.
	- (* -> direction *)
		inversion IH; subst.
		inversion Heq; subst.
		inversion Heq'; subst.
		now constructor.
		apply IHHeq in H2.
		apply (type_subs_morp _ _ _ _ H0) in H3.
		now apply ctx_ext.
	- (* <- direction *)
		dependent induction Heq; try (tauto).
		inversion H; subst.
		apply IHHeq in H2.
		apply (type_subs_morp _ _ _ _ H0) in H3.
		now apply ctx_ext.

(******************************************************************************)
(** Register Equality Relations **)
(* Add Relation (preCtx) (eq_ctx)
	(* reflexivity proved by (@eq_ctx_refl n) *)
   symmetry proved by (@eq_ctx_sym)
   transitivity proved by (@eq_ctx_trans)
   as eq_ctx_rel. *)

Add Parametric Relation Δ Γ : (preSubs) (eq_subs Δ Γ)
   symmetry proved by (@eq_subs_sym Δ Γ)
   transitivity proved by (@eq_subs_trans Δ Γ)
   as eq_subs_rel.

Add Parametric Relation Γ : (preType) (eq_type Γ)
   symmetry proved by (@eq_type_sym Γ)
   transitivity proved by (@eq_type_trans Γ)
   as eq_type_rel.

Add Parametric Relation Γ A : (preTerm) (eq_term Γ A)
   symmetry proved by (@eq_term_sym Γ A)
   transitivity proved by (@eq_term_trans Γ A)
	as eq_term_rel.

(******************************************************************************)
(** Reflexivity lemmas **)
Lemma eq_type_refl {Γ : preCtx} {A : preType} :
	[ Γ ⊢ A type ] -> [ Γ ⊢ A == A type ].
Proof.
   intro H.
   transitivity (A [id])%ty.
   symmetry.
   all: now apply eq_type_subs_id.
Qed.

Lemma eq_term_refl {Γ : preCtx} {A : preType} {a : preTerm} :
	[ Γ ⊢ a @ A ] -> [ Γ ⊢ a == a @ A ].
Proof.
   intro H.
   transitivity (a [id])%term.
   symmetry.
   all: now apply eq_term_subs_id.
Qed.

Lemma eq_subs_refl {Δ Γ : preCtx} {y : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y == y ~ Γ ].
Proof.
   intro H.
	transitivity (id ∘ y)%subs.
	symmetry.
   all: now apply (eq_subs_id_left H).
Qed.

Lemma eq_ctx_refl {Γ : preCtx} :
	[ ⊢ Γ cx ] -> eq_ctx Γ Γ.
Proof.
	intro H.
	dependent induction H; try (tauto).
	now apply eq_ctx_one.
	apply eq_type_refl in H0.
	now apply eq_ctx_ext.
Qed.
(** End reflexivity lemmas **)
(** End Equality Relations **)

(******************************************************************************)
(** Proof of pressupositions For Jugements **)
Lemma type_comp_inv {Γ : preCtx} {A : preType} {y0 y1} :
   [ Γ ⊢ A [y0 ∘ y1] type ] <-> [ Γ ⊢ A [y0] [y1] type ].
Proof.
   split; intro HA;
   inversion HA; subst.
   inversion H2; subst.
   apply (type_subs H5 (type_subs H6 H3)).
   inversion H3; subst.
   apply (type_subs (subs_comp H2 H4) H5).
Qed.

Lemma subs_id_inv {Γ Γ' : preCtx} :
	[ Γ ⊢ id ~ Γ' ] -> Γ = Γ'.
Proof.
	intro H.
	inversion H; subst.
	tauto.
Qed.

Lemma type_id_inv {Γ : preCtx} {A} :
   [ Γ ⊢ A [id] type ] <-> [ Γ ⊢ A type ].
Proof.
   split;
      intro HA.
      inversion HA; subst.
		apply subs_id_inv in H2; subst.
		now apply H3.
      apply type_inv in HA as HΓ.
      now apply (type_subs (subs_id HΓ)).
Qed.

Lemma ContextJG_morphism {Γ Δ : preCtx} :
	eq_ctx Γ Δ -> [ ⊢ Γ cx ] -> [ ⊢ Δ cx ]
with TypeJG_ctx_morphism {Γ Δ : preCtx} {A : preType} :
	eq_ctx Γ Δ -> [ Γ ⊢ A type ] -> [ Δ ⊢ A type ]
with SubsJG_ctx_morphism {Δ Δ' : preCtx} {Γ: preCtx} {y : preSubs} :
	eq_ctx Δ Δ' -> [ Δ ⊢ y ~ Γ ] -> [ Δ' ⊢ y ~ Γ ].
Proof.
	- (* ContextJG case *)
		intros Heq HΓ.
		dependent induction Heq; try (tauto).
		inversion HΓ; subst.
		apply IHHeq in H2.
		apply (TypeJG_morphism H) in H3.
		pose proof (TypeJG_ctx_morphism _ _ _ Heq H3).
		now apply ctx_ext.
	- (* TypeJG case *)
		intros Heq Hty.
		dependent induction Hty generalizing Γ Δ A Heq Hty; try (tauto).
		pose proof (ContextJG_morphism _ _ Heq H).
		now apply type_base.
		apply subs_inv in H as HΔ.
		destruct HΔ as [HΔ HΓ].
		pose proof (SubsJG_ctx_morphism _ _ _ _ Heq H).
		now apply (type_subs H0).
	- (* SubsJG case *)
		intros HeqΔ Hy.
		dependent induction Hy generalizing Δ' HeqΔ; try (tauto).

Lemma type_subs_inv {Δ Γ : preCtx} {y : preSubs} :
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
with type_inv {Γ : preCtx} {A : preType} :
   [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
	- (* substitution *)
		intros Hy.
		dependent induction Hy generalizing Δ Γ Hy; try (tauto).
   	+	(* Projection *)
			apply type_inv in H as HΔ.
			split.
			now apply ctx_ext.
			now tauto.
(*
		- (* Bang *)
			split. tauto.
			now apply ctx_one. *)
   	+  apply (type_subs (subs_weak H)) in H.
			apply type_inv in H as HΓ.
			now tauto.
		+
	- (* type *)
		intro HA.
		dependent induction HA; try (tauto).
		apply type_subs_inv in H as HΔ.
		destruct HΔ as [HΔ HΓ].
		split; try assumption.
		now apply ctx_ext.
Qed.

Lemma type_inv {Γ : preCtx} {A : preType} :
   [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
   intro HA.
   dependent induction HA ; try (tauto).
   -  (* type_subs *)
      apply (type_subs_inv H).
      now intros _.
Qed.

Lemma subs_inv {Δ Γ : preCtx} {y : preSubs} :
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ].
Proof.
   intro Hy.
   (* epose proof (@type_inv Γ)  as Ha. *)
   apply (type_subs_inv Hy).
   intros [A HA].
   now apply type_inv in HA.
Qed.

Lemma type_comp_inv {Γ : preCtx} {A : preType} {y0 y1} :
   [ Γ ⊢ A [y0 ∘ y1] type ] <-> [ Γ ⊢ A [y0] [y1] type ].
Proof.
   split; intro HA;
   inversion HA; subst.
   inversion H2; subst.
   apply (type_subs H5 (type_subs H6 H3)).
   inversion H3; subst.
   apply (type_subs (subs_comp H2 H4) H5).
Qed.

Lemma subs_id_inv {Γ Γ' : preCtx} :
	[ Γ ⊢ id ~ Γ' ] -> Γ = Γ'.
Proof.
	intro H.
	inversion H; subst.
	tauto.
Qed.

Lemma type_id_inv {Γ : preCtx} {A} :
   [ Γ ⊢ A [id] type ] <-> [ Γ ⊢ A type ].
Proof.
   split;
      intro HA.
      inversion HA; subst.
		apply subs_id_inv in H2; subst.
		now apply H3.
      apply type_inv in HA as HΓ.
      now apply (type_subs (subs_id HΓ)).
Qed.

Lemma term_inv {Γ : preCtx} {A : preType} {a : preTerm} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intros Ha.
   dependent induction Ha; try (tauto).
   - (* Qariable *)
      now apply (type_subs (subs_weak H) H).
   - (* Substitution *)
      dependent induction H generalizing A a; try (tauto).
      now apply (type_subs (subs_weak H)).
      now apply type_id_inv.
      now apply type_comp_inv, (type_subs H), (type_subs H0).
      (* now apply (type_subs (subs_bang H)). *)
      now apply (type_subs (subs_ext H H0 H1)).
Qed.
(** End Pressuposition lemma **)

(******************************************************************************)
(** Helpers and derived operators *)
Corollary ctx_typ {Γ : preCtx} {A : preType}:
   [ Γ ⊢ A type ] -> [ ⊢ Γ # A cx ].
Proof.
   apply (fun HA => ctx_ext (type_inv HA) HA).
Qed.

Corollary term_ctx_inv {Γ : preCtx} {A : preType} {a : preTerm} :
	[ Γ ⊢ a @ A ] -> [ ⊢ Γ cx ].
Proof.
	apply (fun Ha => type_inv (term_inv Ha)).
Qed.

Corollary term_id_inv {Γ : preCtx} {A : preType} {a : preTerm}:
   ([ Γ ⊢ a [id] @ A[id] ] <-> [ Γ ⊢ a @ A ]).
Proof.
   split; intro Ha.
      inversion Ha; subst.
		now apply subs_id_inv in H3; subst.
      apply term_ctx_inv in Ha as HΓ.
      eapply term_subs.
      now apply subs_id.
      now apply Ha.
Qed.

Lemma term_comp_inv {Γ : preCtx} {A : preType} {a : preTerm} {y1 y2}:
   ([ Γ ⊢ a [y1 ∘ y2] @ A[y1 ∘ y2] ] <-> [ Γ ⊢ a [y1] [y2] @ A[y1][y2]]).
Proof.
   split; intro Ha; inversion Ha; subst.
   inversion H3; subst.
   apply (term_subs H5 (term_subs H6 H4)).
   inversion H4; subst.
   apply (term_subs (subs_comp H3 H5) H6).
Qed.


Definition psubs_lift (y : preSubs) : preSubs := (y ∘ p)#q.
Notation "⇑( y )" := (psubs_lift y) (at level 1, left associativity) : subs_scope.

Fixpoint psubs_lift_n (n : nat) (y : preSubs) : preSubs :=
	match n with
	| 0 => y
	| S n' => psubs_lift (psubs_lift_n n' y)
	end.

Notation "⇑ n ( y )" := (psubs_lift_n n y) (at level 1, left associativity) : subs_scope.

(* Notation "!"       := psub_Bang (at level 0). *)

Lemma VarId {Γ : preCtx} {A : preType} :
	[ Γ ⊢ A type ] ->
	[ Γ # A ⊢ q [id] == q @ A [p]].
Proof.
	intro.
	apply eq_term_subs_id.
	apply term_qar.
	dependent induction Γ; try (tauto).
Qed.

Lemma VarConst {Δ Γ : preCtx} {y} {A : preType} {a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ].
Proof.
	apply eq_term_beta_qar.
Qed.

(******************************************************************************)
(** Ctx Morphisms **)
Lemma TypeJG_morphism {Γ : preCtx} {A B : preType} :
	[ Γ ⊢ A == B type ] ->  [ Γ ⊢ A type  ] <-> [ Γ ⊢ B type ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   now apply type_id_inv.
   now apply type_comp_inv.
Qed.

(* Lemma Id_ctx_mor {Γ Δ : preCtx} :
  eq_ctx Γ Δ -> [ Γ ⊢ id ~ Δ ].
Proof.
  intros Heq.
   dependent induction Heq generalizing Δ Γ Heq; try (tauto).
	now apply subs_id,ctx_one.
  apply eq_ctx_inv in Heq as [H1 H2].
  apply (type_subs H1).
Qed. *)

Lemma ContextJG_morphism {Γ Δ : preCtx} :
	eq_ctx Γ Δ -> [ ⊢ Γ cx ] -> [ ⊢ Δ cx ]
with TypeJG_ctx_morphism {Γ Δ : preCtx} {A : preType} :
	eq_ctx Γ Δ -> [ Γ ⊢ A type ] -> [ Δ ⊢ A type ]
with SubsJG_ctx_morphism {Δ Δ' : preCtx} {Γ: preCtx} {y : preSubs} :
	eq_ctx Δ Δ' -> [ Δ ⊢ y ~ Γ ] -> [ Δ' ⊢ y ~ Γ ].
(* with SubsJG_ctx_morphism {Δ Δ' : preCtx} {Γ Γ': preCtx} {y : preSubs} :
	eq_ctx Δ Δ' -> eq_ctx Γ' Γ -> [ Δ ⊢ y ~ Γ ] -> [ Δ' ⊢ y ~ Γ' ]. *)
Proof.
	- (* ContextJG case *)
		intros Heq HΓ.
		dependent induction Heq; try (tauto).
		(* dependent induction HΓ generalizing Δ Heq; try (tauto). *)
		inversion HΓ; subst.
		apply IHHeq in H2.
		apply (TypeJG_morphism H) in H3.
		pose proof (TypeJG_ctx_morphism _ _ _ Heq H3).
		now apply ctx_ext.
	- (* TypeJG case *)
		intros Heq Hty.
		dependent induction Hty generalizing Γ Δ A Heq Hty; try (tauto).
		pose proof (ContextJG_morphism _ _ Heq H).
		now apply type_base.
		apply subs_inv in H as HΔ.
		destruct HΔ as [HΔ HΓ].
		pose proof (SubsJG_ctx_morphism _ _ _ _ Heq H).
		now apply (type_subs H0).
	-	(* SubsJG case *)
		intros HeqΔ Hy.
		dependent induction Hy generalizing Δ' HeqΔ; try (tauto).
		(* dependent induction HeqΔ generalizing Γ y; try (tauto). *)
		(* apply subs_inv in Hy as HΔ.
		destruct HΔ as [HΔ HΓ].
		inversion HΔ; subst.
		specialize (IHHeqΔ _ _ (subs_id H2)) as HΓ'.
		apply subs_id_inv in HΓ'; subst.
		clear HeqΔ HΔ.
		move y at bottom.
		dependent induction y generalizing Γ0 A B H HΓ H2 H3 IHHeqΔ; try (tauto). *)
		(* dependent induction HeqΔ generalizing Γ  A B' y; try (tauto). *)
		(* dependent induction Hy generalizing Γ' HeqΓ; try (tauto). *)
	(* dependent induction H0 generalizing Γ0 B Heq H IHHeq; try (tauto). *)
		+ (* Projection *)
			dependent induction Γ; try (tauto).
			(* dependent induction Δ generalizing Γ' A H; try (tauto). *)
			dependent destruction HeqΔ.
			dependent destruction HeqΔ.
			apply (TypeJG_morphism H0) in H.
			now apply subs_weak.
			dependent destruction HeqΔ.
			apply type_inv in H as HΓ.
			inversion HΓ; subst.
			specialize (IHΓ _ H4 _ HeqΔ).
		+ (* Identity *)
			inversion H0; subst.
			specialize (IHHeq _ _ (subs_id H3)).
			apply subs_id_inv in IHHeq; subst.
			clear Heq H0.
			move H at bottom.
			dependent induction H; try (tauto).
			apply (TypeJG_morphism H) in H4.
			specialize (IHeq_type H3 H4).
			apply subs_id_inv in IHeq_type; subst.
			dependent destruction IHeq_type.
			now apply subs_id, ctx_ext.
			specialize (IHeq_type1 H3 H4).
			apply subs_id_inv in IHeq_type1.
			dependent destruction IHeq_type1.
			specialize (IHeq_type2 H3 H4).
			apply subs_id_inv in IHeq_type2.
			dependent destruction IHeq_type2.
			now apply subs_id, ctx_ext.
		- (* Composition *)
			inversion Heq; subst.
			apply subs_comp with (Γ1 := Γ); try assumption.
			now apply IHH in H0.
		- (* Extension *)
			inversion Heq; subst.
			apply subs_ext with (Γ := Γ); try assumption.
			now apply IHH in H0.
Qed.

Proof.
	intros Heq H.
	dependent induction H generalizing Δ Heq; try (tauto).
	dependent destruction Δ.
	now apply ctx_one.
	dependent destruction Δ.
	dependent destruction Heq.
	now apply ctx_ext.
	- inversion H0; subst.
		apply ctx_ext.
		now apply IHeq_ctx.
		now apply TypeJG_ctx_morphism with (Γ := Γ).

Lemma SubsJG_ctx_morphism {n m : nat} {Δ : preCtx n} {Δ' : preCtx n} {Γ : preCtx m} {Γ' : preCtx m} {y : preSubs} :
	eq_ctx n Δ Δ' -> eq_ctx m Γ Γ' -> SubsJG n m Δ Γ y -> SubsJG n m Δ' Γ' y.


Lemma TermJG_ctx_morphism {n : nat} {Γ Δ : preCtx n} {A : preType} {a : preTerm} :
	eq_ctx n Γ Δ -> TermJG n Γ A a -> TermJG n Δ A a.

Lemma term_comp_inv' {n2 n1 n0 : nat} {Γ2 : preCtx n2} {Γ1 : preCtx n1}
	{Γ0 : preCtx n0} {y1 : preSubs} {y0 : preSubs} {A : preType} {a : preTerm}:
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> (([ Γ2 ⊢ a [y0] [y1] @ A [y0] [y1]]
		<-> [ Γ2 ⊢ a [y0] [y1] @ A [y0 ∘ y1]])
	/\ ([ Γ2 ⊢ a [y0] [y1] @ A [y0] [y1]]
		<-> [ Γ2 ⊢ a [y0 ∘ y1] @ A [y0] [y1] ]))
.
Proof.
	intros Hy1 Hy0 Ha.
	dependent induction n0 generalizing n2 n1; try (tauto).
	dependent destruction Γ0; try (tauto).
	inversion Ha; subst.
	dependent induction a generalizing n2 n1 Γ2 Γ1 y1 y0 A; try (tauto).
	-	inversion Ha'; subst.
		dependent destruction H.
		dependent destruction H0.
		apply (term_subs (subs_comp Hy1 Hy0) H0).
	-	inversion Ha'; subst.
		dependent destruction H.
		dependent destruction H0.
		apply (term_subs (subs_comp Hy1 Hy0) H0).
Qed.

Lemma VarLift {n : nat} {Γ : preCtx n} {A : preType} {a : preTerm} :
	[ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ A [id]].
Proof.
	intro.
	dependent induction n; try (tauto).
	dependent destruction Γ.
	dependent induction a generalizing A; try (tauto).
	inversion H; subst.
	dependent induction y generalizing a; try (tauto).
	-	inversion H; subst.
		dependent destruction H0.
		inversion H5; subst.
	-	inversion H; subst.
		dependent destruction Δ.
		dependent destruction H0.
		inversion H5; subst.
		dependent destruction H0.
		dependent destruction H7.
		apply IHa in H6.
		now apply (term_subs H5).
	- admit.
	- admit.
	- inversion H; subst.
		dependent destruction Δ.
		dependent destruction H0.
		inversion H5; subst.
		dependent destruction H0.
		dependent destruction H2.
		dependent destruction H7.
		apply IHa in H6.
		now apply (term_subs H5).

Lemma subs_lift_id {n m : nat} {Γ : preCtx n} :
	[ Γ ⊢ id ~ Γ ] ->
	exists (Δ : preCtx (n + m)),[ Δ ⊢ psubs_lift_n m (id) ~ Δ ].
Proof.
	intro H.
	induction m; try (tauto).
	rewrite <-  plus_n_O.
	now exists (Γ).
	destruct IHm as [Δ IHm].
	simpl.
	rewrite <- plus_n_Sm.
	exists (Δ # b)%ctx.
	unfold psubs_lift.
	apply subs_ext.
	eapply subs_comp.
	apply subs_weak.
	apply type_base.
	now apply subs_inv in IHm as HΔ.
	now apply IHm.
	apply type_base.
	now apply subs_inv in IHm as HΔ.
	apply subs_weak.
	apply type_base.

Abort.

Lemma magic {n Γ A} :
	[ Γ ⊢ q @ A ] ->
	( exists Δ B,
	[ Δ ⊢ q [ psubs_lift_n n id ] @ B ]).
Proof.
Abort.

Lemma qar_id_comp {Γ A} :
	[ ⊢ Γ cx ] -> [ Γ ⊢ A type ] -> [ Γ # A ⊢ q @ A [ id ∘ p ]].
Proof.
	intros HΓ HA.
	dependent induction HΓ; try (tauto).
Abort.

(* Lemma eq_ctx_refl {Γ} : [ ⊢ Γ cx] -> eq_ctx Γ Γ.
Proof.
   intro HΓ.
   dependent induction HΓ; try (tauto).
   now apply eq_ctx_one.
   apply eq_ctx_ext.
   now apply IHHΓ.
   now apply eq_type_refl.
Qed. *)

(******************************************************************************)
(** Building Equationlaity Relations **)

(** context morphisms **)
(* Add Parametric Morphism Γ : (pctx_ext Γ)
   with signature (eq_type Γ ==> eq_ctx)
   as ctx_mor.
Proof.
   intros A B Heq.
   apply eq_ctx_ext; try assumption.
   dependent induction Heq; try (tauto).
   now apply eq_ctx_refl, (type_inv H).
   apply subs_inv in H.
   now apply eq_ctx_refl.
   now symmetry.
Qed. *)

(** Type morphisms **)
Add Parametric Morphism Γ: (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as type_mor.
Proof.
   intros A B Heq.
   dependent induction Heq; try (tauto).
   now apply type_id_inv.
   now apply type_comp_inv.
Qed.

Lemma eq_type_inv {Γ A B} :
	[ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
	intro Heq.
	dependent induction Heq; try (tauto).
	split.
		now apply type_id_inv.
		now apply H.
	split.
		now apply (type_subs (subs_comp H H0) H1).
		now apply (type_subs H (type_subs H0 H1)).
Qed.

(** Substitution morphisms **)
Lemma id_left_inv {Δ Γ} {y}:
   [ Δ ⊢ id ∘ y ~ Γ ] <-> [ Δ ⊢ y ~ Γ ].
Proof.
   split; intro Hy.
   inversion Hy; subst.
   inversion H4; subst.
   now assumption.
   eapply (subs_comp Hy).
   apply subs_inv in Hy.
   now apply (subs_id).
Qed.

Lemma id_right_inv {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] <-> [ Δ ⊢ y ∘ id ~ Γ ].
Proof.
   split; intro Hy.
   apply subs_inv in Hy as Hx.
   eapply subs_comp.
   now apply (subs_id).
   now assumption.
   inversion Hy; subst.
   inversion H3; subst.
   now assumption.
Qed.

Lemma subs_assoc_inv {Δ Γ} {y2 y1 y0}:
   [Δ ⊢ y0 ∘ y1 ∘ y2 ~ Γ] <-> [Δ ⊢ (y0 ∘ y1) ∘ y2 ~ Γ].
Proof.
   split;
   intro Hy.
   -  inversion Hy; subst.
      inversion H3; subst.
      now apply (subs_comp H5 (subs_comp H6 H4)).
   -  inversion Hy; subst.
      inversion H4; subst.
      now apply (subs_comp (subs_comp H3 H5) H6).
Qed.

Lemma subs_bang_inv {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ] -> !%subs = δ.
Abort. (** should we do something for bang ? **)

Lemma subs_beta_inv {Δ Γ a y} :
   [ Δ ⊢ p ∘ y # a ~ Γ ] -> [ Δ ⊢ y ~ Γ ].
Proof.
   intro Hy.
   inversion Hy; subst.
   inversion H4; subst.
   now inversion H3; subst.
Qed.

Lemma subs_beta_inv' {Δ Γ a y} :
   ([Δ ⊢ y ~ Γ] /\ (exists A, [Γ ⊢ A type ] /\ [Δ ⊢ a @ A [y]])) <->
      [ Δ ⊢ p ∘ y # a ~ Γ ].
Proof.
   split.
   intros [Hy [A [HA Ha]]].
   eapply (subs_comp (subs_ext Hy HA Ha)).
   now apply subs_weak.
   intro Hy.
   inversion Hy; subst.
   inversion H4; subst.
   inversion H3; subst.
   split.
   now apply H7.
   now exists A.
Qed.

Lemma subs_eta_inv {Δ Γ A y} :
   [ Δ ⊢ y ~ Γ # A ] ->
   [ Δ ⊢ (p ∘ y) # q[y] ~ (Γ # A) ].
Proof.
   intro Hy.
   apply subs_inv in Hy as Hx.
   destruct Hx as [HΔ HΓ].
   inversion HΓ; subst.
   eapply subs_ext.
   apply (subs_comp Hy).
   now apply subs_weak.
   now apply H2.
Abort.

Lemma aelkn { Δ Γ A y } :
   [Γ ⊢ A type ]-> [Δ ⊢ y ~ Γ # A]
      -> [Δ ⊢ q [y] @ A [p ∘ y]].
Proof.
   intros HA Hy.
   apply term_qar in HA.
   apply (term_subs Hy) in HA.
Abort.

Lemma type_id_equiv {Γ A a} :
	[ Γ ⊢ a @ A ] <-> [ Γ ⊢ a @ A [id] ].
Proof.
	dependent induction Γ; try (tauto).
	- dependent induction a generalizing A.
		split; intro H.
			inversion H; subst.
			inversion H; subst.
	apply term_ctx_inv in H as HΓ.
	eapply term_subs.
	now apply subs_id.
	now apply H.
Qed.


Lemma term_term_equiv {Γ A B a} :
	[ Γ ⊢ A == B type ]->
	[ Γ ⊢ a @ A ] <-> [ Γ ⊢ a @ B ].
Proof.
	intros Heq.
	dependent induction Heq; try (tauto).
	- now apply type_id_inv in H.
	- now apply type_comp_inv in H.

Lemma eq_term_inv {Γ T a b} :
	[ Γ ⊢ a == b @ T ] ->
	(exists A B,
		[Γ ⊢ A == T type ] /\ [ Γ ⊢ a @ A ] /\
		[Γ ⊢ B == T type ] /\ [ Γ ⊢ b @ B ]).
Proof.
	intro Heq.
	dependent induction Heq; try (tauto).
	- destruct (IHHeq) as [A0 [B0 [HA [HB [Ha Hb]]]]].
		now exists B0, A0.
	- destruct (IHHeq1) as [A0 [B0 [HA [HB [Ha Hb]]]]].
		destruct (IHHeq2) as [A0' [B0' [HA' [HB' [Ha' Hb']]]]].
		now exists A0, B0'.
	- exists (A[id])%ty, A.
		split.
			apply eq_type_subs_id.
			now apply term_inv in H.
		split.
			now apply term_id_inv.
		split.
			apply term_inv in H.
			now apply eq_type_refl.
		now assumption.
	-


Lemma eq_subs_inv {Δ Γ y d} :
	[ Δ ⊢ y == d ~ Γ ] -> [ Δ ⊢ y ~ Γ ] /\ [ Δ ⊢ d ~ Γ ].
Proof.
	intro Heq.
	dependent induction Heq; try (tauto).
	- split.
		now apply id_left_inv.
		now apply H.
	- split.
		now apply H.
		now apply id_right_inv in H.
	- split.
		now apply (subs_comp (subs_comp H H0) H1).
		now apply (subs_comp H (subs_comp H0 H1)).
	- split.
		apply subs_inv in H.
		now apply subs_bang.
		now apply H.
	- split.
		eapply subs_comp.
		now apply (subs_ext H H0 H1).
		now apply subs_weak.
		now apply H.
	- split.
		now apply H0.
		apply subs_ext.
		eapply subs_comp.
		now apply H0.
		now apply subs_weak.
		now apply H.
Qed.


(* Add Parametric Morphism Δ Γ : (ptyp_subs)
   with signature (eq_type Γ ==> eq_subs Δ Γ ==> eq_type Δ)
   as type_subs_mor.
Proof.
   intros A B Heq y1 y2 Heqy.
   dependent induction Heq; try (tauto).
   -  symmetry.
      apply IHHeq.
      now symmetry.
   -  transitivity (B [y2])%ty.
      now apply IHHeq1.
      apply IHHeq2.
      transitivity y1.
      now symmetry.
      assumption.
   -

Qed. *)

(** term morphisms *)
Lemma term_comp_inv' {Γ2 Γ1 Γ0 y1 y0 A a}:
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> ([ Γ2 ⊢ a [y0] [y1] @ A [y0] [y1] ]
   -> ([ Γ2 ⊢ a [y0] [y1] @ A [y0 ∘ y1] ]
   /\ [ Γ2 ⊢ a [y0 ∘ y1] @ A [y0] [y1] ]))
.
Proof.
   intros Hy1 Hy0 Ha.
   dependent induction y0 generalizing Γ2 Γ1 Γ0 y1; try (tauto).
Abort.

Lemma term_id_term_inv {Γ A a}:
   ([ Γ ⊢ a @ A ] -> [ Γ ⊢ a [id] @ A ] /\ [ Γ ⊢ a @ A [id]]).
Proof.
   dependent induction Γ; try (tauto).
   intro Ha.
   dependent induction a generalizing A; try (tauto).
   inversion Ha; subst.
   dependent induction y generalizing a; try (tauto).
   -  inversion Ha; subst.
      inversion H3; subst.
   - inversion Ha; subst.
      inversion H3; subst.
      apply IHa in H4.
      split; now apply (term_subs H3).
   -  specialize (IHy1 _ IHa) as Hy1.
      specialize (IHy2 _ Hy1) as Hy2.
      inversion Ha; subst.
      apply term_comp_inv in Ha.
      apply IHy2 in Ha as [Ha1 Ha2].
      inversion Ha1; subst.
      inversion H7; subst.
      inversion H5; subst.
      inversion H6; subst.
Abort.



(** Substitution morphisms **)
Lemma id_left_inv {Δ Γ} {y}:
   [ Δ ⊢ id ∘ y ~ Γ ] <-> [ Δ ⊢ y ~ Γ ].
Proof.
   split; intro Hy.
   inversion Hy; subst.
   inversion H4; subst.
   now assumption.
   eapply (subs_comp Hy).
   apply subs_inv in Hy.
   now apply (subs_id).
Qed.

Lemma id_right_inv {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] <-> [ Δ ⊢ y ∘ id ~ Γ ].
Proof.
   split; intro Hy.
   apply subs_inv in Hy as Hx.
   eapply subs_comp.
   now apply (subs_id).
   now assumption.
   inversion Hy; subst.
   inversion H3; subst.
   now assumption.
Qed.

Lemma subs_assoc_inv {Δ Γ} {y2 y1 y0}:
   [Δ ⊢ y0 ∘ y1 ∘ y2 ~ Γ] <-> [Δ ⊢ (y0 ∘ y1) ∘ y2 ~ Γ].
Proof.
   split;
   intro Hy.
   -  inversion Hy; subst.
      inversion H3; subst.
      now apply (subs_comp H5 (subs_comp H6 H4)).
   -  inversion Hy; subst.
      inversion H4; subst.
      now apply (subs_comp (subs_comp H3 H5) H6).
Qed.

Lemma subs_bang_inv {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ] -> !%subs = δ.
Abort. (** should we do something for bang ? **)

Lemma subs_beta_inv {Δ Γ a y} :
   [ Δ ⊢ p ∘ y # a ~ Γ ] -> [ Δ ⊢ y ~ Γ ].
Proof.
   intro Hy.
   inversion Hy; subst.
   inversion H4; subst.
   now inversion H3; subst.
Qed.

Lemma subs_beta_inv' {Δ Γ a y} :
   ([Δ ⊢ y ~ Γ] /\ (exists A, [Γ ⊢ A type ] /\ [Δ ⊢ a @ A [y]])) <->
      [ Δ ⊢ p ∘ y # a ~ Γ ].
Proof.
   split.
   intros [Hy [A [HA Ha]]].
   eapply (subs_comp (subs_ext Hy HA Ha)).
   now apply subs_weak.
   intro Hy.
   inversion Hy; subst.
   inversion H4; subst.
   inversion H3; subst.
   split.
   now apply H7.
   now exists A.
Qed.

Lemma subs_eta_inv {Δ Γ A y} :
   [ Δ ⊢ y ~ Γ # A ] ->
   [ Δ ⊢ (p ∘ y) # q[y] ~ (Γ # A) ].
Proof.
   intro Hy.
   apply subs_inv in Hy as Hx.
   destruct Hx as [HΔ HΓ].
   inversion HΓ; subst.
   eapply subs_ext.
   apply (subs_comp Hy).
   now apply subs_weak.
   now apply H2.
Abort.

Lemma aelkn { Δ Γ A y } :
   [Γ ⊢ A type ]-> [Δ ⊢ y ~ Γ # A]
      -> [Δ ⊢ q [y] @ A [p ∘ y]].
Proof.
   intros HA Hy.
   apply term_qar in HA.
   apply (term_subs Hy) in HA.
Abort.


Add Parametric Morphism Δ Γ: (SubsJG Δ Γ)
   with signature (eq_subs Δ Γ ==> iff)
   as subs_mor.
Proof.
   intros y1 y2 Heq.
   dependent induction Heq; try (tauto).
   - apply id_left_inv.
   - apply id_right_inv.
   - apply subs_assoc_inv.
   -  (* bang *)
      split; intro. tauto.
      apply subs_inv in H.
      now apply subs_bang.
   -  (* beta *)
   split; intro Hs.
      now assumption.
      apply (subs_comp (subs_ext H H0 H1)).
      now apply subs_weak.
   - (* eta *)
   split; intro Hs.
      eapply subs_ext.
      apply (subs_comp H0).
      now apply subs_weak.
      now assumption.
      apply term_qar in H.
      apply (term_subs H0) in H.
      revert H.
      dependent induction A generalizing Δ Γ A; try (tauto).

(* Lemma term_comp_type_assoc {Γ A a y0 y1 y2}:
   [ Γ ⊢ a @ A [y0 ∘ (y1 ∘ y2)] ]  <-> [ Γ ⊢ a @ A [(y0 ∘ y1) ∘ y2] ].
Proof.
   dependent induction a generalizing Γ A; try (tauto).
   split; intro Ha; inversion Ha; subst.
   split; intro Ha; inversion Ha; subst.
      inversion H3; subst.
      apply (term_subs (subs_comp H3 (subs_comp H5 H6)) H4).
   -  inversion Ha; subst.
      inversion H4; subst.
      apply (term_subs (subs_comp (subs_comp H3 H5) H6) H4). *)



(*
Lemma term_com_inv {Γ A a y0 y1}:
   [ Γ ⊢ a [y0] [y1] @ A ]  <-> [ Γ ⊢ a [y0 ∘ y1] @ A ].
Proof.
   dependent induction A generalizing Γ; try (tauto).
   (* dependent induction A. *)
   dependent induction a generalizing Γ; try (tauto).
   split; intro Ha.
   inversion Ha; subst.
   inversion H5; subst.
   inversion H6; subst.
   (* dependent induction A generalizing Γ; try (tauto). *)
Abort.
(*  *)
Lemma term_com_type_inv {Γ A a y0 y1}:
   [ Γ ⊢ a @ A [y0] [y1] ]  <-> [ Γ ⊢ a @ A [y0 ∘ y1] ]
   /\ [ Γ ⊢ a [y0] [y1] @ A ]  <-> [ Γ ⊢ a [y0 ∘ y1] @ A ].
Proof.
   dependent induction a generalizing Γ A; try (tauto).
   -
   dependent induction A generalizing Γ; try (tauto).
   split ; intro Ha;
   inversion Ha; subst.
   apply IHA.
   dependent induction y0 generalizing Γ A; try (tauto).
      inversion H4; subst.
      apply (term_subs (subs_comp H3 H5) H6).
   -  inversion Ha; subst.
      inversion H3; subst.
      apply (term_subs H5).
      apply (term_subs H6 H4). *)


Add Parametric Morphism Γ: (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_type_mor.
Proof.
   intros A B Heq a.
   dependent induction Heq; try (tauto).
   now symmetry.
   now transitivity [ Γ ⊢ a @ B ].
   now apply term_subs_id.
   now apply term_subs_comp.
   now apply eq_term_beta_qar.
Qed.


Add Parametric Morphism Δ Γ: (SubsJG Δ Γ)
   with signature (eq_subs Δ Γ ==> iff)
   as ctx_subs_mor.
Proof.
   intros y1 y2 Heq.
   dependent induction Heq; try (tauto).
   - apply id_left_inv.
   - apply id_right_inv.
   - apply subs_assoc_inv.
   -  (* bang *)
      split. tauto.
      apply subs_inv in H.
      intro.
      now apply subs_bang.
   -  (* beta *)
   split; intro Hs.
      now assumption.
      eapply subs_comp.
      apply (subs_ext H H0 H1).
      now apply subs_weak.
   - (* eta *)
   split; intro.
      eapply subs_ext.
      apply (subs_comp H0).
      now apply subs_weak.
      now assumption.
      apply term_qar in H.
      apply (term_subs H0) in H.
      revert H.
      dependent induction A generalizing Δ Γ A; try (tauto).
      inberrsion

Qed.

Add Parametric Morphism : (TypeJG)
   with signature (eq_ctx ==> eq ==> iff)
   as ctx_type_mor.
Proof.
   intros Δ Γ Heq.
Admitted.

Add Parametric Morphism : (TermJG)
   with signature (eq_ctx ==> eq ==> eq ==> iff)
   as ctx_term_mor.
Proof.
   intros Δ Γ Heq.
Admitted.

(*** End Equality Relations ***)

Theorem eq_type_inv {Γ} {A B}:
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
   intros.
   dependent induction H; try (tauto).
   -  (* Identity *)
      split.
      now apply type_id_inv.
      now assumption.
   -  (* Composition *)
      split.
      now apply (type_subs (subs_comp H H0)).
      now apply (type_subs H), (type_subs H0).
Qed.

Theorem eq_subs_inv {Δ Γ y1 y0}:
   [ Δ ⊢ y1 == y0 ~ Γ ] -> [ Δ ⊢ y1 ~ Γ ] /\ [ Δ ⊢ y0 ~ Γ ].
Proof.
   intros.
   dependent induction H; try (tauto).
   -  (* right id *)
      split.
      now apply id_left_inv in H.
      now assumption.
   -  (* left id *)
      split. now assumption.
      now apply id_right_inv in H.
   -  (* associativity *)
   split.
      now apply (subs_comp (subs_comp H H0) H1).
      now apply (subs_comp H (subs_comp H0 H1)).
   -  (* Bang *)
   split.
      apply subs_inv in H as Hx.
      now apply subs_bang.
      now assumption.
   -  (* beta *)
   split.
      eapply subs_comp.
      apply (subs_ext H H0 H1).
      now apply subs_weak.
      now assumption.
   - (* eta *)
   split.
      now assumption.
      eapply subs_ext.
      apply (subs_comp H0).
      now apply subs_weak.
      now assumption.
      apply term_qar in H.
      apply (term_subs H0) in H.
      revert H.
      dependent induction A generalizing Δ Γ A; try (tauto).
      inberrsion

(* Qed. *)
Admitted.


Lemma pctx_ext_mor {Δ Γ} {A B} :
   eq_ctx Δ Γ -> [ Δ ⊢ A == B type ] -> eq_ctx (Δ # A) (Γ # B).
Proof.
   intros Heq HeqAB.
   simpl.
   split; try assumption.
Qed.

Lemma eq_type_inv {Γ} {A B} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] <-> [ Γ ⊢ B type ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   exact type_id_inv.
   exact type_comp_inv.
Qed.

Lemma eq_ctx_type_weak_inv {Δ Γ} {A} :
   eq_ctx Δ Γ -> [ Δ ⊢ A[p] type ] <-> [ Γ ⊢ A[p] type ].
Proof.
   intros Heq.
   dependent induction Δ; try (tauto);
   destruct Γ; simpl in Heq; try (tauto).
   destruct Heq as [Heq HeqAB].
   split; intro HA.
   inversion HA; subst.
   inversion H2; subst.

Lemma eq_ctx_id_l {Δ Γ}:
   eq_ctx Δ Γ -> [Δ ⊢ id ~ Γ] <-> [Γ ⊢ id ~ Γ].
Proof.
   dependent induction Δ;
   induction Γ; simpl; try (tauto).
   simpl in Heq; try contradiction.
   simpl in Heq; try contradiction.
   tauto.
   split; intro HA;
   inversion HA; subst.
   now apply subs_id.
   destruct Heq as [Heq HeqAB].
   specialize (IHΔ _ Heq) as HS.
   inversion H; subst.
   apply subs_id in H2.
   apply HS in H2.
   inversion H2; subst.
Qed.


Lemma eq_ctx_subs_morp_l {Δ Γ Θ} {y} :
   eq_ctx Δ Θ -> [Δ ⊢ y ~ Γ] -> [Θ ⊢ y ~ Γ].
Proof.
   intros Heq Hy.
   dependent induction y generalizing Δ Γ Θ.
   - inversion Hy; subst.
      clear Hy.
      move Θ after H.
      dependent induction Θ generalizing Γ H.
      destruct Γ; simpl in Heq; try contradiction.
      now apply subs_id.
      dependent induction Γ generalizing A;
      simpl in Heq; try contradiction.
      destruct Heq as [Heq HeqAB].



      apply (subs_weak (eq_type_inv HeqAB)).
      apply (subs_weak (eq_type_inv HeqAB)).
   tauto.
   dependent induction H generalizing Δ Heq; try tauto.
      inversion H0; subst.
      apply subs_id in H3.
      apply IHHeq in H3.
      inversion H3; subst.

Lemma eq_ctx_inv {Δ Γ A} :
   eq_ctx Δ Γ ->
      ([ ⊢ Δ cx ] <-> [ ⊢ Γ cx ]) /\ ([ Δ ⊢ A type ] <-> [ Γ ⊢ A type ]).
Proof.
   intros Heq.
   dependent induction A generalizing Δ Γ; try (tauto).
   dependent induction y generalizing A.
   all : split; [ now specialize (IHA _ _ Heq) as [Hx _] | ].
   (* Identity *)
   - specialize (IHA _ _ Heq) as [Hx HA].
   rewrite type_id_inv, HA.
   now rewrite type_id_inv.
   -
   specialize (IHy1 _ IHA).
   specialize (IHy2 _ IHy1 _ _ Heq) as [Hx HA].
   rewrite type_comp_inv, HA.
   now rewrite type_comp_inv.
   -
      split; intro HAp;
      inversion HAp; subst;
      inversion H2; subst.
      destruct Γ; simpl in Heq; try contradiction.
      destruct Heq as [Hx HeqAB].
      apply (type_inv) in HAp as Hcx.
      apply (IHA _ _ (pctx_ext_mor Hx HeqAB)) in Hcx.
      inversion Hcx; subst.
      apply (type_subs (subs_weak H5)).
      specialize (IHA _ _ Hx) as [_ HA].
      now apply HA.
      destruct Δ; simpl in Heq; try contradiction.
      destruct Heq as [Hx HeqAB].
      apply (type_inv) in HAp as Hcx.
      apply (IHA _ _ (pctx_ext_mor Hx HeqAB)) in Hcx.
      inversion Hcx; subst.
      apply (type_subs (subs_weak H5)).
      specialize (IHA _ _ Hx) as [_ HA].
      now apply HA.
   -  split; intro HA;
      inversion HA; subst;
      inversion H2; subst;
      specialize (IHA _ _ Heq) as [Hx _];
      apply Hx in H;
      now apply (type_subs (subs_bang H)).
   -  split; intro HA;
      inversion HA; subst;
      inversion H2; subst.
      specialize (IHA _ _ Heq) as [Hx _];
      apply Hx in H;
      now apply (type_subs (subs_bang H)).





Lemma eq_ctx_weak_inv {Δ Γ A B} :
   eq_ctx Δ Γ -> [ Δ ⊢ A == B type ]
   -> ([ Δ # A ⊢ p ~ Δ ] <-> [ Γ # B ⊢ p ~ Γ ]).
Proof.
   dependent induction Δ;
   destruct Γ; simpl; try tauto.
   - intros _ Heq.
      dependent induction Heq; subst.
      symmetry.
      apply (IHHeq eq_refl).
      rewrite (IHHeq1 eq_refl).
      apply (IHHeq2 eq_refl).
      dependent induction H; try tauto.
      inversion H; subst.
      inversion H0; subst.
   apply (subs_weak (eq_type_inv HeqAB)).
   inversion H2; subst.
   apply (subs_weak (eq_type_inv (eq_type_sym HeqAB))).



Lemma eq_ctx_inv' {Δ Γ} :
   eq_ctx Δ Γ
   -> ([ ⊢ Δ cx ] <-> [ ⊢ Γ cx ])
   /\ (forall A, [ Δ ⊢ A type ] <-> [ Γ ⊢ A type ])
      .
Proof.
   dependent induction Δ;
   destruct Γ; simpl; try tauto.
   intros [Hx Heq].
   split.
   specialize (IHΔ _ Hx) as [IHx IHA].
   split; intro HA;
   inversion HA; subst;
   apply ctx_ext.
   now apply IHx.
   apply (eq_type_inv Heq) in H2.
   now apply IHA.
   now apply IHx.
   apply IHA in H2.
   now apply (eq_type_inv Heq).
   intros B .
   dependent induction B generalizing Γ A0 Hx Heq.
   dependent induction y generalizing B.
   specialize (IHB _ _ Hx Heq).
   rewrite type_id_inv, IHB.
   now rewrite type_id_inv.
   specialize (IHy1 B IHB).
   specialize (IHy2 _ IHy1 _ _ Hx Heq).
   rewrite type_comp_inv, IHy2.
   now rewrite type_comp_inv.
   split; intro HB;
   inversion HB; subst;
   inversion H2; subst;
   specialize (IHΔ _ Hx) as [IHx IHA].
   apply (eq_type_inv Heq) in H4.
   apply IHA in H4.
   apply (type_subs (subs_weak H4)).
   now apply IHA.
   apply IHA in H4.
   apply (eq_type_inv Heq) in H4.
   apply (type_subs (subs_weak H4)).
   now apply IHA.
   split; intro HB;
   inversion HB; subst;
   inversion H2; subst;
   specialize (IHΔ _ Hx) as [IHx IHA];
   inversion H; subst;
   apply IHx in H4.
   apply (eq_type_inv Heq), IHA in H5.
   now apply (type_subs (subs_bang (ctx_ext H4 H5))).
   apply IHA, (eq_type_inv Heq) in H5.
   now apply (type_subs (subs_bang (ctx_ext H4 H5))).
   split; intro HB;
   inversion HB; subst.
   inversion H2; subst.
   specialize (IHΔ _ Hx) as [IHx IHA];
   inversion H; subst;
   apply IHx in H4.
   apply (eq_type_inv Heq), IHA in H5.


Qed.

Theorem eq_ctx_inv {Δ Γ} :
   eq_ctx Δ Γ -> [ ⊢ Δ cx ] -> [ ⊢ Γ cx ].
Proof.
   intros Hx.
   apply (eq_ctx_inv' Hx).
Qed.
Lemma eq_ctx_type_mor' {Δ Γ} {A}:
   (eq_ctx Δ Γ -> [Δ ⊢ A type ] -> [Γ ⊢ A type])
   /\ (forall B, [ Δ ⊢ A == B type ] -> [ Δ ⊢ A type ] <-> [ Δ ⊢ B type ]).
Proof.
   dependent induction A generalizing Δ Γ.
   dependent induction y generalizing A.
   -  split. intros Hx HA.
      inversion HA; subst.
      inversion H2; subst.
      eapply (type_subs).
      eapply (subs_id).
      now apply (eq_ctx_inv Hx).
      destruct (IHA Γ0 Γ) as [IHA2 _].
      now apply (IHA2 Hx).
      intros B HB.
      dependent induction HB; try (tauto).

   - specialize (IHy1 _ IHA).
      specialize (IHy2 _ IHy1).
      apply type_comp_inv in HA.
      apply (IHy2 _ _ Hx) in HA.
      now apply type_comp_inv.
   - inversion HA; subst.
      inversion H2; subst.
      destruct Γ; simpl in Hx; try contradiction.
      destruct Hx.
      apply (IHA _ _ H0) in H3.
Abort.

Lemma eq_type_eq_ctx_mor {Δ Γ A B}:
   (eq_ctx Δ Γ -> [ Δ ⊢ A == B type ] -> [ Γ ⊢ A == B type ]).
Proof.
   intros Hx Heq.
   (* dependent induction A generalizing Δ Γ. *)
   dependent induction Heq generalizing Γ Hx.
   now apply eq_type_sym, IHHeq.
   apply @eq_type_trans with (B:=B).
   now apply IHHeq1.
   now apply IHHeq2.
   destruct Γ;
   simpl; try tauto.

Lemma eq_ctx_sym {Δ Γ}:
   eq_ctx Δ Γ -> eq_ctx Γ Δ.
Proof.
   dependent induction Δ;
   destruct Γ;  simpl; try tauto.
   intros [Hx Heq]. split.
   now apply IHΔ.
Abort.

Lemma eq_ctx_trans {Δ Γ Θ} :
   eq_ctx Δ Γ -> eq_ctx Γ Θ -> eq_ctx Δ Θ.
Proof.
   dependent induction Δ;
   destruct Γ, Θ;
   simpl; try tauto.
   intros [Hx1 Heq1] [Hx2 Heq2].


Lemma eq_ctx_type_mor' {Δ Γ} {A}:
   eq_ctx Δ Γ -> [Δ ⊢ A type ] -> [Γ ⊢ A type].
Proof.
   intros Hx HA.
   dependent induction A generalizing Δ Γ.
   dependent induction y generalizing A.
   - inversion HA; subst.
      inversion H2; subst.
      eapply (type_subs).
      eapply (subs_id).
      now apply (eq_ctx_inv Hx).
      now apply (IHA _ _ Hx).
   - specialize (IHy1 _ IHA).
      specialize (IHy2 _ IHy1).
      apply type_comp_inv in HA.
      apply (IHy2 _ _ Hx) in HA.
      now apply type_comp_inv.
   - inversion HA; subst.
      inversion H2; subst.
      destruct Γ; simpl in Hx; try contradiction.
      destruct Hx.
      eapply (type_subs).
      eapply (subs_id).

Lemma eq_type_eq_ctx_mor {Δ Γ A B}:
   eq_ctx Δ Γ -> [ Δ ⊢ A == B type ] -> [ Γ ⊢ A == B type ].
Proof.
   intros Hx Heq.
   (* dependent induction A generalizing Δ Γ. *)
   dependent induction Heq generalizing Γ Hx.
   now apply eq_type_sym, IHHeq.
   apply @eq_type_trans with (B:=B).
   now apply IHHeq1.
   now apply IHHeq2.
   destruct Γ;
   simpl; try tauto.

(* Lemma skew_id1 {Γ A} :
   [Γ ⊢ A type] -> [Γ # A [id] ⊢ id ~ Γ # A].
Proof.
   intro HA.

   dependent induction A generalizing Γ.
   dependent induction y generalizing A.
   - inversion HA; subst.
      inversion H2; subst.
      apply IHA in H3.
      inversion H3; subst.
      now rewrite H0,H0.
   -

   -  inversion IHHAB; subst.
      apply (subs_id H1).
   -  inversion IHHAB1; subst.
      inversion IHHAB2; subst.
      apply (subs_id H2).
   - dependent induction H.
      dependent induction y generalizing Δ Γ.
      + inversion H; subst.
         inversion IHTypeJG; subst.
         now rewrite H2, H2 in IHTypeJG.
+ Abort. *)

(*
Lemma skew_id {Δ Γ} :
   eq_ctx Δ Γ -> [Δ ⊢ id ~ Γ].
Proof.
   intros Heq.
   dependent induction Heq.
   apply (subs_id ctx_one).
   inversion IHHeq; subst.
   clear Heq IHHeq.
   move H0 before Γ.
   dependent induction H; try tauto.
   apply IHeq_type in H0.
   inversion H0; subst.
   apply (subs_id H3).
   specialize (IHeq_type1 H0).
   specialize (IHeq_type2 H0).
   inversion IHeq_type1; subst.
   inversion IHeq_type2; subst.
   apply (subs_id H5).
   dependent induction A generalizing Γ H0.
   inversion H; subst. *)


(* Lemma eq_ctx_subs_mor' {Δ Γ Θ} {y} :
      eq_ctx Δ Θ -> [Δ ⊢ y ~ Γ] <-> [Θ ⊢ y ~ Γ].
Proof.
   intro Heq.
   dependent induction y generalizing Δ Γ Θ.
   -  split; intro Hy.
         inversion Hy; subst.

   dependent induction Heq generalizing Γ.
   tauto.
   dependent induction H generalizing Δ Heq; try tauto.
      inversion H0; subst.
      apply subs_id in H3.
      apply IHHeq in H3.
      inversion H3; subst. *)

Lemma eq_ctx_ctx_mor' {Δ Γ} :
   eq_ctx Δ Γ -> [ ⊢ Δ cx ] -> [ ⊢ Γ cx ].
   intros Heq HΔ.
   dependent induction Γ generalizing Δ.
   apply ctx_one.
   inversion Heq; subst.
   inversion HΔ; subst.
   apply (IHΓ _ H2) in H1.
   apply (ctx_ext H1).

Lemma eq_ctx_type_mor' {Δ Γ} {A}:
   eq_ctx Δ Γ -> [Δ ⊢ A type ] <-> [Γ ⊢ A type].
Proof.
   intros Heq.
   dependent induction A generalizing Δ Γ.
   dependent induction y generalizing A; try (tauto).
   - split; intro HA;
      inversion HA; subst.
      inversion H2; subst.
      apply (IHA _ _ Heq) in H3.
      apply (type_subs ).
   split; intro HA.
   inversion HA; subst.
   - split; intro HA.
      inversion HA; subst.
      inversion H2; subst.
      apply (IHA _ _ Heq) in H3.
      apply (type_subs (subs_id (type_inv H3)) H3).
   -  specialize (IHy1 _ IHA).
      specialize (IHy2 _ IHy1).
      specialize (IHy2 _ _ Heq).
      split; intro HA;
      now apply type_comp_inv, IHy2, type_comp_inv.
   -  dependent induction Heq; try (tauto).
      split; intro HA;
      inversion HA; subst;
      inversion H6; subst;
      apply (IHA _ _ Heq) in H7.
      apply (type_subs (subs_weak H1) H7).
      apply (type_subs (subs_weak H) H7).
Lemma eq_type_eq_ctx_mor {Δ Γ A B}:
   eq_ctx Δ Γ -> [ Δ ⊢ A == B type ] <-> [ Γ ⊢ A == B type ].
Proof.
   intros Heq.
   split; intro HA.
   dependent induction HA generalizing Γ Heq.
   - apply eq_type_sym. apply (IHHA _ Heq).
   - specialize (IHHA1 _ Heq).
      specialize (IHHA2 _ Heq).
      apply (eq_type_trans IHHA1 IHHA2).
   -
   move y after IHA.
   dependent induction y; try (tauto).
   dependent induction B generalizing Δ Γ A IHA.
   dependent induction y0 generalizing Δ Γ; try (tauto).
   dependent induction y0.
   (* dependent induction y0. *)
   - split; intro HA.
      dependent induction HA generalizing Γ Heq; subst.
      apply (IHA _ _ Heq) in H3;
      apply (type_subs (subs_id (type_inv H3)) H3).
   -  specialize (IHy1 _ IHA).
      specialize (IHy2 _ IHy1).
      specialize (IHy2 _ _ Heq).
      split; intro HA;
      now apply type_comp_inv, IHy2, type_comp_inv.
   -  dependent induction Heq; try (tauto).
      split; intro HA;
      inversion HA; subst;
      inversion H6; subst;
      apply (IHA _ _ Heq) in H7.
      apply (type_subs (subs_weak H1) H7).
      apply (type_subs (subs_weak H) H7).
Lemma eq_ctx_sym {Δ Γ} : eq_ctx Δ Γ -> eq_ctx Γ Δ.
Proof.
   intros H.
   dependent induction H.
   (* - apply (eq_ctx_trans IHeq_ctx2 IHeq_ctx1). *)
   - apply eq_ctx_one.
   - apply (eq_ctx_ext IHeq_ctx H1 H0).
Qed.

Lemma eq_ctx_transitive {Δ Γ Θ} : eq_ctx Δ Γ -> eq_ctx Γ Θ -> eq_ctx Δ Θ.
Proof.
   intros H1 H2.
   dependent induction H1 generalizing Θ.
   apply H2.
   induction Θ; try (tauto).
   inversion H2; subst.
   inversion H2; subst.

   dependent induction H2 generalizing Δ A B H1 H H0 IHeq_ctx; try (tauto).
   apply IHeq_ctx in H2 as H9.
   apply (eq_ctx_ext H9).
   apply (eq_type_trans H).

Lemma type_inv {Γ} {A}:
   [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
   intro HA.
   dependent induction HA; try (tauto).
   dependent induction H generalizing A; try (tauto).
   apply (ctx_ext IHHA H).
   specialize (IHSubsJG2 A HA IHHA).
   apply (IHSubsJG1 _ (type_subs H0 HA) IHSubsJG2).
Qed.

(* Lemma eq_ctx_sym {Δ Γ} : eq_ctx Δ Γ -> eq_ctx Γ Δ.
Proof.
   intros H.
   dependent induction H.
   (* - apply (eq_ctx_trans IHeq_ctx2 IHeq_ctx1). *)
   - apply eq_ctx_one.
   - apply (eq_ctx_ext IHeq_ctx).
Qed. *)

Lemma eq_ctx_trans {Δ Γ Θ} : eq_ctx Δ Γ -> eq_ctx Γ Θ -> eq_ctx Δ Θ.
Proof.
   intros H1 H2.
   dependent induction H1 generalizing Θ.
   apply H2.
   dependent induction H2 generalizing Δ A B H1 H H0 IHeq_ctx; try (tauto).
   apply IHeq_ctx in H2 as H9.
   apply (eq_ctx_ext H9).
   apply (eq_type_trans H).


Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as type_mor.
Proof.
   intros A B Heq.
   dependent induction Heq; try (tauto).
   - split; intro HA.
      assumption. apply (type_subs (subs_id (type_inv HA)) HA).
   -  exact type_comp_inv.
Qed.

Add Morphism (TypeJG)
   with signature (eq_ctx ==> eq ==> iff)
   as eq_ctx_type_mor.
Proof.
   intros Heq A B.
   dependent induction A generalizing Δ Γ Heq.
   dependent induction y generalizing A; try (tauto).
   - split; intro HA;
      inversion HA; subst;
      inversion H2; subst;
      apply (IHA _ _ Heq) in H3;
      apply (type_subs (subs_id (type_inv H3)) H3).
   -  specialize (IHy1 _ IHA).
      specialize (IHy2 _ IHy1).
      specialize (IHy2 _ _ Heq).
      split; intro HA;
      now apply type_comp_inv, IHy2, type_comp_inv.
   -  dependent induction Heq; try (tauto).
      split; intro HA;
      inversion HA; subst;
      inversion H6; subst;
      apply (IHA _ _ Heq) in H7.
      apply (type_subs (subs_weak H1) H7).
      apply (type_subs (subs_weak H) H7).
Qed.

Add Morphism (SubsJG)
   with signature (eq_ctx ==> eq_ctx ==> eq ==> iff)
   as eq_ctx_subs_mor.
Proof.
   intros Δ Δ' Heq1 Γ Γ' Heq2 y.
   dependent induction Heq1; try (tauto).
   rewrite (IHHeq1_1 _ _ Heq2).
   apply IHHeq1_2.
   transitivity Γ0; [symmetry | ]; apply Heq2.
   -
      dependent induction y generalizing Γ Γ' Heq2; try (tauto).
      dependent induction Heq2; try (tauto).
      split; intro Hy; inversion Hy; subst.
      dependent induction Heq2 generalizing y1 y2 IHy1 IHy2; try (tauto).
      rewrite (IHHeq2_1 _ _ IHy1 IHy2).
      apply (IHHeq2_2 _ _ IHy1 IHy2).
      split; intro Hy; inversion Hy; subst.
      move y after Heq2.
      dependent induction y generalizing Δ Γ B A; try (tauto).
      split; intro Hy; inversion Hy; subst.

      clear H Hy.
      specialize (IHHeq2_1 eq_refl).
      inversion IHHeq2_1; subst.
      apply (IHHeq2_2 eq_refl).
      apply (subs_id ctx_one).


         apply (subs_comp H2 (subs_weak H1)).
         apply (subs_comp H2 (subs_weak H)).

Qed.
Lemma eq_ctx_type_mor' {Δ Γ A} :
   eq_ctx Δ Γ
   -> [ Δ ⊢ A type ] <-> [ Γ ⊢ A type].

Lemma id_ctx_ext_mor {Γ} {A B} :
   [ Γ ⊢ A == B type ]
   -> [ Γ # A ⊢ id ~ Γ # B ].
Proof.
   intro Heq.
   dependent induction Heq; try (tauto).
   - inversion IHHeq; subst.
      apply (subs_id H1).
   - inversion IHHeq1; inversion IHHeq2; subst.
      apply (subs_id H1).
   - dependent induction A generalizing Γ.
      dependent induction y generalizing A.
      inversion H; subst.
      inversion H3; subst.
      apply IHA in H4.
      inversion H4; subst.
      rewrite H1, H1.
      apply H4.
      specialize (IHy1 _ IHA).
      specialize (IHy2 _ IHy1).
      apply type_comp_inv in H.
      apply IHy2 in H.
      inversion H; subst.

Lemma skew_id {Δ Γ} :
   eq_ctx Δ Γ -> [ Δ ⊢ id ~ Γ ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   - inversion IHHeq1; inversion IHHeq2; subst.
      apply (subs_id H2).
   - apply (subs_id (ctx_one)).
   - inversion IHHeq; subst.
      clear H0 Heq IHHeq H H1 H3.
      induction H2; try (tauto).
      inversion IHeq_type; subst.
      apply (subs_id H1).
      inversion IHeq_type1; subst.
      inversion IHeq_type2; subst.
      apply (subs_id H1).

Lemma eq_ctx_subs_mor' {Δ Δ' Γ Γ'} y :
   eq_ctx Δ Δ' -> eq_ctx Γ Γ'
   ->  [ Δ ⊢ y ~ Γ ] <-> [ Δ' ⊢ y ~ Γ' ].
Proof.
   intros Heq Heq'.
   dependent induction y generalizing Δ Δ' Γ Γ'; try (tauto).
   -
      split; intros Hy.
      inversion Hy; subst.
      symmetry in Heq.
      apply (transitivity Heq) in Heq'.
      apply IHHeq1.
         assumption.
      now apply IHHeq1, IHHeq2.
   - intros A0.
   induction A0; try (tauto).
   split; intro HA0.
   inversion HA0; subst.



      split; intros.
Abort.

(* Add Morphism (TypeJG)
   with signature (eq_ctx ==> eq ==> iff)
   as ctx_type_mor.
Proof.
   intros Δ Γ Heq A.
   dependent induction A generalizing Δ Γ Heq; try (tauto).
   (* move y after IHA. *)
   generalize dependent A.
   induction y; try (tauto);
   intros A IHA.
   - split; intro HA;
      inversion HA; subst;
      inversion H2; subst;
      apply (IHA _ _ Heq) in H3;
      apply eq_ctx_inv in Heq as [HD HG].
      apply (type_subs (subs_id HG) H3).
      apply (type_subs (subs_id HD) H3).
   - split; intro HA;
      inversion HA; subst.
      inversion H2; subst.
      apply (IHA _ _ Heq) in H3;
      apply eq_ctx_inv in Heq as [HD HG].
      apply (type_subs (subs_id HG) H3).
      apply (type_subs (subs_id HD) H3).
   dependent induction Heq; try (tauto).
   rewrite IHHeq1.
   apply IHHeq2.
   dependent induction A0; try (tauto).
   apply eq_ctx_inv in Heq as [HD HG].
   dependent induction y generalizing A0; try (tauto).
   - split; intro HA.
      inversion HA; subst.
      inversion H6; subst.
      apply IHA0 in H7.
      apply (type_subs (subs_id (ctx_ext HG H1)) H7).
      inversion HA; subst.
      inversion H6; subst.
      apply IHA0 in H7.
      apply (type_subs (subs_id (ctx_ext HD H)) H7).
   - split; intro HA.
      inversion HA; subst.
      inversion H6; subst.
      apply IHA0 in H7.
      apply (type_subs (subs_id (ctx_ext HG H1)) H7).
      inversion HA; subst.
      inversion H6; subst.
      apply IHA0 in H7.
      apply (type_subs (subs_id (ctx_ext HD H)) H7).
   -
   apply type_subs(subs_comp H H0) H1.
   apply subs_id.
   apply
   inversion H1; subst.
   - intro T. dependent induction T.
      dependent induction HT; try (tauto).
      inversion HT; subst.
      dependent induction HA; try (tauto).
     apply (type_subs (subs_weak H) H).
     apply (type_subs H IHHA).
   - dependent induction HA; try (tauto).
     apply (type_subs H IHHA). *)

(* requires morphism for Types *)
(* Add Morphism (ContextJG)
   with signature (eq_ctx ==> iff)
   as ctx_mor.
Proof.
   intros Δ Γ Heq.
   induction Heq; try (tauto).
   split; intro H1.
   - dependent induction H; try (tauto).
     apply (ctx_ext_mor Heq).
     split; assumption.
   - dependent induction H; try (tauto).
     apply (ctx_ext_mor (eq_ctx_sym Heq)).
     split; assumption. *)

(** Inversion Lemma **)
(* Lemma type_inv {Γ} {A}:
   [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
   intro HA.
   dependent induction HA; try (tauto).
   dependent induction H generalizing A; try (tauto).
   apply (ctx_ext IHHA H).
   specialize (IHSubsJG2 A HA IHHA).
   apply (IHSubsJG1 _ (type_subs H0 HA) IHSubsJG2).
Qed. *)

Corollary type_ctx {Γ} {A} :
   [ Γ ⊢ A type ] -> [ ⊢ Γ # A cx ].
Proof.
   intro HA.
   apply (ctx_ext (type_inv HA) HA).
Qed.

Lemma subs_inv_left {Δ Γ} {y} :
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ cx ].
Proof.
   intro Hy.
   dependent induction Hy; try (tauto).
   apply (type_ctx H).
Qed.

Lemma subs_inv_right {Δ Γ} {y} :
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Γ cx ].
Proof.
   intro Hy.
   dependent induction Hy; try (tauto).
   apply (type_inv H).
   (* apply ctx_one. *)
   (* apply (type_ctx H). *)
Qed.

Lemma term_ctx_inv {Γ} {A} {a} :
   [ Γ ⊢ a @ A ] -> [ ⊢ Γ cx ].
Proof.
   intro Ha.
   dependent induction Ha; try (tauto).
   apply (type_ctx H).
   apply (subs_inv_left H).
Qed.

Lemma term_inv {Γ} {A} {a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intro Ha.
   dependent induction Ha; try (tauto).
   apply (type_subs (subs_weak H) H).
   apply (type_subs H IHHa).
Qed.


Lemma comp_assoc_inv {Γ3 Γ0} {y0 y1 y2} :
   [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) ~ Γ0 ] <-> [ Γ3 ⊢ ((y0 ∘ y1) ∘ y2) ~ Γ0 ].
Proof.
   split; intro H.
   - inversion H; subst.
     inversion H4; subst.
     apply (subs_comp H6 (subs_comp H7 H5)).
   - inversion H; subst.
     inversion H5; subst.
      apply (subs_comp (subs_comp H4 H6) H7).
Qed.

Lemma comp_right_inv {Γ0 Γ1 Γ2} {y0 y1} :
      [ Γ2 ⊢ y1 ~ Γ1 ]
      ->[ Γ2 ⊢ (y0 ∘ y1) ~ Γ0 ]
      -> [ Γ1 ⊢ y0 ~ Γ0 ].
Proof.
   intros Hy1 H.
   dependent induction Hy1 generalizing y0; try (tauto).
   inversion H0; subst.
   inversion H5; subst.
   assumption.
   inversion H0; subst.
   inversion H5; subst.
   assumption.
   apply IHHy1_2.
   apply IHHy1_1.
   apply (comp_assoc_inv).
   assumption.
   (* inversion H0; subst.
   inversion H5; subst.
   assumption. *)
Qed.


Lemma weak_inv {Γ2 Γ1 Γ0} :
   [ Γ0 ⊢ p ~ Γ1 ] -> [ Γ0 ⊢ p ~ Γ2 ] -> Γ1 = Γ2.
intros H1 H2.
   dependent induction H1; try (tauto).
   dependent induction H2; try (tauto).
Qed.

(* Lemma subs_ext_inv_e {Δ Γ} {y} {a A} :
   [ Δ ⊢ (y # a) ~ (Γ # A) ]
      -> [ Δ ⊢ a @ A[y] ]. *)
(* Proof. *)
   (* intros H. *)
   (* inversion H; subst. *)
   (* assumption. *)
(* Qed. *)

(* Lemma subs_ext_inv {Δ Γ} {y} {a A} :
   [ Δ ⊢ (y # a) ~ (Γ # A) ]
   -> [ Δ ⊢ y ~ Γ ].
Proof.
   intros H.
   inversion H; subst.
   assumption.
Qed. *)

Lemma type_comp_inv {Γ} {A} {y0 y1} :
   [ Γ ⊢ A [y0] [y1] type ]  <-> [ Γ ⊢ A [y0 ∘ y1] type ].
Proof.
   split; intro HA;
   inversion HA; subst.
   inversion H3; subst.
   apply (type_subs (subs_comp H2 H4) H5).
   inversion H2; subst.
   apply (type_subs H5).
   apply (type_subs H6 H3).
Qed.

Lemma type_id_inv {Γ} {A} :
   [ Γ ⊢ A [id] type ] -> [ Γ ⊢ A type ].
Proof.
   intro HA.
   inversion HA; subst.
   inversion H2; subst.
   assumption.
Qed.

Lemma type_id_inv2 {Γ} {A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A [id] type ].
Proof.
   intro HA.
   eapply type_subs.
   apply subs_id.
   inversion H2; subst.
   assumption.
Qed.


Lemma term_comp_inv {Γ2} {A} {a} {y0 y1} :
   [ Γ2 ⊢ a [y0] [y1] @ A [y0] [y1] ]  <-> [ Γ2 ⊢ a [y0 ∘ y1] @ A [y0 ∘ y1] ].
Proof.
   split; intro Ha;
   inversion Ha; subst.
   inversion H4; subst.
   apply (term_subs (subs_comp H3 H5) H6).
   inversion H3; subst.
   apply (term_subs H5).
   apply (term_subs H6 H4).
Qed.

Lemma term_id_inv {Γ} {A} {a} :
   [ Γ ⊢ a [id] @ A [id] ] -> [ Γ ⊢ a @ A ].
Proof.
   intro Ha.
   inversion Ha; subst.
   inversion H3; subst.
   assumption.
Qed.



(* Lemma term_comp_inv {Γ} {A} {a} {y0 y1} :
      ([Γ ⊢ a [ y0 ∘ y1 ] @ A [ y0 ∘ y1 ] ]  <-> [ Γ ⊢ a [y0][y1] @ A [y0 ∘ y1]])
   /\ ([Γ ⊢ a [ y0 ∘ y1 ] @ A [ y0 ∘ y1 ] ]  <-> [ Γ ⊢ a [y0][y1] @ A [y0] [y1]])
   /\ ([Γ ⊢ a [ y0 ∘ y1 ] @ A [ y0 ∘ y1 ] ]  <-> [ Γ ⊢ a [y0 ∘ y1] @ A [y0] [y1]])
.
Proof.
Qed. *)

Lemma type_subs_inv {Δ Γ} {y} {A} :
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ A [y] type ]
   -> [ Γ ⊢ A type ].
intros.
   dependent induction H generalizing A; try (tauto).
   inversion H0; subst.
   inversion H4; subst.
   assumption.
   inversion H0; subst.
   inversion H4; subst.
   assumption.
   apply type_comp_inv in H1.
   apply IHSubsJG1 in H1.
   apply IHSubsJG2 in H1.
   assumption.
   (* inversion H0; subst. *)
   (* inversion H4; subst. *)
   (* assumption. *)
   (* inversion H2; subst.
   inversion H6; subst. *)
Qed.


(* Lemma eq_subs_beta_inv {Δ Γ A a y} :
   [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ p ∘ y # a ~Γ ] <-> [ Δ ⊢ y ~ Γ ].
Proof.
   intros HA Ha.
   split; intro H.
   inversion H; subst.
   inversion H4; subst.
   (* inversion H5; subst.
   apply H2. *)
   (* apply (subs_comp (subs_ext H HA Ha) (subs_weak HA)). *)
Abort. *)

(* Lemma eq_subs_eta_inv {Δ Γ A y} :
   [ Γ ⊢ A type ] ->
   [ Δ ⊢ y ~ Γ # A ] <-> [ Δ ⊢ (p ∘ y) # q[y] ~ (Γ # A) ].
Proof.
   intros HA.
   split; intro Hy.
   apply (subs_ext (subs_comp Hy (subs_weak HA)) HA).
   dependent induction Δ; try (tauto).
   dependent induction Γ; try (tauto).
   dependent induction HA generalizing y; try (tauto).
   inversion H4; subst.
   inversion H5; subst.
   apply H2.
   apply (subs_comp (subs_ext H HA Ha) (subs_weak HA)).
Qed. *)


(* * requires substitution rewrite and term press *
Lemma skew_id {Δ Γ} :
   eq_ctx Δ Γ -> [ Δ ⊢ id ~ Γ ]
   (* /\ (forall A, [ Γ ⊢ A type ] <-> [ Δ ⊢ A type ]) *)
   (* /\ (forall A B, [ Γ ⊢ A == B type ] <-> [ Δ ⊢ A == B type ]) *)
   (* /\ (forall A B, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ]) *)
   (* /\ (forall A B, [ Γ ⊢ A == B type ] -> [ Γ # A ⊢ q @ B [id ∘ p]])  *)
   (* /\ (forall A B e, [ Γ ⊢ A == B type ] -> [ Γ ⊢ e @ B ] <-> [ Γ ⊢ e @ A ]) *)
   (* /\ (forall E y, [ E ⊢ y ~ Γ ] <-> [ E ⊢ y ~ Δ ])
   /\ (forall E y, [ Γ ⊢ y ~ E ] <-> [ Δ ⊢ y ~ E ])
   /\ (forall E y d, [ E ⊢ y == d ~ Γ ] -> [ E ⊢ y ~ Γ ] <-> [ E ⊢ d ~ Γ ]) *)
   .
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   - apply (subs_id ctx_one).
    split. tauto.
    split. tauto.
    split.
    + intros A B Heq.
      dependent induction Heq; try (tauto).
      split. apply (type_subs (subs_id ctx_one) H). assumption.
      split.
      apply (type_subs (subs_comp H H0) H1).
      apply (type_subs H (type_subs H0 H1)).
   + intros A B e Heq.
      dependent induction Heq; try (tauto).
      specialize (IHHeq eq_refl) as H.
      inversion H; subst.
      specialize (IHHeq1 eq_refl) as H1.
      inversion H1; subst.
      specialize (IHHeq2 eq_refl) as H2.
      inversion H2; subst.
      apply (term_qar H3).

   (* + intros y d Heq.
     dependent induction Heq; try (tauto).
     split; intro. assumption. apply (subs_comp H (subs_id ctx_one)).
     split; intro. apply (subs_comp (subs_id ctx_one) H). assumption.
     split; intro. apply (subs_comp H (subs_comp H0 H1)).
   apply (subs_comp (subs_comp H H0) H1).
     apply (subs_comp H (subs_id ctx_one)). *)
   - destruct IHHeq as [Hid [HL [HeqL Hpress]]].
      apply Hpress in H as HAB.
      destruct HAB as [HA HB].
     split.
     apply HL in HA.
     (* apply (type_subs Hid) in HB as Hq. *)
     apply term_qar in HA as Hq.
     (** I need Hq : [Δ # A ⊢ q @ B [id ∘ p]]*)
     apply (subs_comp (subs_weak HA)) in Hid as Hp.
     remember (subs_ext (subs_comp (subs_weak HA) Hid) HB (term_qar HB)) as Hpq.
     split. tauto.
     split. tauto.
     (* split. *)
     + intros A B Heq.
       dependent induction Heq; try (tauto).
       split; intro. assumption. apply (type_subs (subs_ext H_id H_type H_eq_type) H).
       split; intro.  apply (type_subs H (type_subs (subs_ext H_id H_type H_eq_type) H0)).
       apply (type_subs (subs_comp (subs_ext H_id H_type H_eq_type) (subs_weak H)) H0). *)


(*** Fundamental property of CTX ***)
(** End **)

(** Building term_conv. **)
Lemma ctx_eq {Γ} {A B}:
   [Γ ⊢ A == B type ]
   -> (
   (forall T, [ Γ # A ⊢ T type ] <-> [ Γ # B ⊢ T type])
   /\ (forall Δ y, [ Δ ⊢ y ~ Γ # A ] <-> [ Δ ⊢ y ~ Γ # B ] )
   /\ (forall Δ y, [ Δ # A ⊢ y ~ Γ ] <-> [ Δ # B ⊢ y ~ Γ ] )
   /\ (forall T e, [ Γ # A ⊢ e @ T ] <-> [ Γ # B ⊢ e @ T ])
   ).
Proof.
   (* intros Heq.
   dependent induction Heq; try (tauto).
   - split; symmetry; apply IHHeq.
   - destruct IHHeq1,IHHeq2.
      split; intros.
      rewrite H. apply H1.
      rewrite H0. apply H2.
   - dependent induction H; try (tauto).
      split; intros.
      split; intro HT.
      inversion HT; subst.
      inversion H0; subst.
      apply (type_base).
      apply (ctx_ext H).
      apply (type_base H).
      inversion H0; subst. *)
Admitted.
Lemma eq_ctx_type {Γ} {A B}:
   [Γ ⊢ A == B type ]
   -> (forall T, [ Γ # A ⊢ T type ] <-> [ Γ # B ⊢ T type]).
Proof.
   intros Heq.
   apply (ctx_eq Heq).
Qed.

Lemma eq_ctx_subs_r {Γ} {A B}:
   [Γ ⊢ A == B type ]
   -> (forall Δ y, [ Δ ⊢ y ~ Γ # A ] <-> [ Δ ⊢ y ~ Γ # B ] ).
Proof.
   intros Heq.
   apply (ctx_eq Heq).
Qed.
Lemma eq_ctx_subs_l {Γ} {A B}:
   [Γ ⊢ A == B type ]
   -> (forall Δ y, [ Δ # A ⊢ y ~ Γ ] <-> [ Δ # B ⊢ y ~ Γ ] ).
Proof.
   intros Heq.
   apply (ctx_eq Heq).
Qed.
Lemma eq_ctx_term {Γ} {A B}:
   [Γ ⊢ A == B type ]
   -> (forall T e, [ Γ # A ⊢ e @ T ] <-> [ Γ # B ⊢ e @ T ]).
Proof.
   intros Heq.
   apply (ctx_eq Heq).
Qed.

Lemma magic_q {Γ} {A B}:
   [Γ ⊢ B type ] ->
   [Γ ⊢ A == B type ]
   -> [ Γ # A ⊢ q @ B [p]].
Proof.
   intros HB Heq.
   apply (eq_ctx_term Heq).
   apply (term_qar HB).
Qed.

Lemma magic' {Γ} {A B}:
   [Γ ⊢ A type ] ->
   [Γ ⊢ A == B type ] -> A = B.
Proof.
   intros HA Heq.
   apply (eq_type_sym) in Heq.
   apply (magic_q HA) in Heq as H.
   inversion H; subst.
   reflexivity.
Qed.

Lemma magic {Γ} {A B}:
   [Γ ⊢ A == B type ] -> A = B.
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   inversion IHHeq; subst; assumption.
   inversion IHHeq1; subst; assumption.
   apply (eq_type_subs_id) in H as Heq.
   apply eq_type_sym in Heq.
   apply (magic' H) in Heq.
   auto.
   apply (eq_type_subs_comp H H0) in H1 as Heq.
   apply (magic' (type_subs (subs_comp H H0) H1)) in Heq.
   assumption.
Qed.

Lemma term_conv {Γ A B a} :
   [ Γ ⊢ B == A type ] ->
   ([ Γ ⊢ a @ B ] <-> [ Γ ⊢ a @ A ]).
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   -  apply (eq_type_subs_id) in H as Heq.
      apply eq_type_sym in Heq.
      apply (magic' H) in Heq.
      rewrite Heq at 2.
      tauto.
   -  apply (eq_type_subs_comp H H0) in H1 as Heq.
      apply (magic' (type_subs (subs_comp H H0) H1)) in Heq.
      rewrite Heq.
      tauto.
Qed.

Lemma eq_term_conv {Γ A B a b} :
   [ Γ ⊢ B == A type ] ->
   ( [ Γ ⊢ a == b @ B ] <-> [ Γ ⊢ a == b @ A ] ).
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   -  apply (eq_type_subs_id) in H as Heq.
      apply eq_type_sym in Heq.
      apply (magic' H) in Heq.
      rewrite Heq at 2.
      tauto.
   -  apply (eq_type_subs_comp H H0) in H1 as Heq.
      apply (magic' (type_subs (subs_comp H H0) H1)) in Heq.
      rewrite Heq.
      tauto.
Qed.
(** End Context Equality **)

(** Setoid declarations **)
(*** Fundamental property ***)
Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as type_mor.
Proof.
   intros A B Heq.
   apply magic in Heq; subst.
   tauto.
Qed.

Add Parametric Morphism Γ T : (fun A => TypeJG (Γ # A) T)
   with signature (eq_type Γ ==> iff)
   as eq_type_etx_mor.
Proof.
   intros A B Heq.
   apply (magic) in Heq; subst.
   tauto.
Qed.

Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_jug_eq_type_mor.
Proof.
   intros A B Heq e.
   apply (term_conv Heq).
Qed.

(** Bug ? **)
Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> Basics.flip Basics.impl)
   as term_jug_eq_type_mor2.
Proof.
   intros A B Heq e H.
   apply (term_conv Heq).
   assumption.
Qed.

Add Parametric Morphism Γ : (eq_term Γ)
   with signature (eq_type Γ ==> eq ==> eq ==> iff)
   as eq_term_eq_type_mor.
Proof.
   intros A B Heq a b.
   apply (eq_term_conv Heq).
Qed.
(** End Fundamental property **)


(** Construction helpers **)
(* Lemma eq_subs_comp_l {Γ2 Γ1 Γ0} {y d} {y'} :
   [ Γ1 ⊢ y == d ~ Γ0 ] -> [ Γ2 ⊢ y' ~ Γ1 ]
   -> [ Γ2 ⊢ (y ∘ y') == (d ∘ y') ~ Γ0 ].
Proof.
   intros Heq H.
   apply (eq_subs_comp Heq (eq_subs_refl H)).
Qed. *)
(* Lemma eq_subs_comp_r {Γ2 Γ1 Γ0} {y} {y' d'} :
   [ Γ1 ⊢ y ~ Γ0 ] -> [ Γ2 ⊢ y' == d' ~ Γ1 ]
   -> [ Γ2 ⊢ (y ∘ y') == (y ∘ d') ~ Γ0 ].
Proof.
   intros H Heq.
   apply (eq_subs_comp (eq_subs_refl H) Heq).
Qed. *)

(*** Rewriting under construction ***)
(* Add Parametric Morphism Γ2 Γ1 Γ0 : psub_comp with
   signature (eq_subs Γ1 Γ0 ==> eq_subs Γ2 Γ1 ==> eq_subs Γ2 Γ0)
as eq_subs_comp_mor.
Proof.
   intros y d Heq y' d' Heq'.
   apply (eq_subs_comp Heq Heq').
Qed. *)
(** Requires eq_term_press **)
Add Parametric Morphism Δ Γ A y (H : [Δ ⊢ y ~ Γ]) : (psub_ext y) with
   signature (eq_term Δ (A [y]) ==> eq_subs Δ (Γ # A))
as eq_subs_ext_mor.
Proof.
   intros a b Heq.
Abort.

Add Parametric Morphism Δ Γ : (ptyp_subs) with
   signature  (eq_type Γ ==> eq_subs Δ Γ ==> eq_type Δ)
as eq_type_subs_mor.
Proof.
   intros A B Heq y d Heq'.
   (* apply (eq_type_subs Heq' Heq). *)
Abort.

Add Parametric Morphism Δ Γ A (H : [Γ ⊢ A type ]) : (ptyp_subs A) with
   signature  (eq_subs Δ Γ ==> eq_type Δ)
as eq_type_subs_mor2.
Proof.
   intros y d Heq'.
   (* apply (eq_type_subs_S Heq' H). *)
Abort.
Add Parametric Morphism Δ Γ A y (H : [Δ ⊢ y ~ Γ]) : (fun a => ptrm_subs a y) with
   signature (eq_term Γ A ==> eq_term Δ A[y])
as eq_term_subs_mor.
Proof.
   intros a b Heq.
   (* apply (eq_term_subs_T H Heq). *)
Abort.
(** End Rewriting **)


(*** "Presupositions" Theorems ***)
Theorem type_press {Γ A}:
   [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
   exact (type_inv).
Qed.

(**** helper ****)
Corollary type_weak {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ # A ⊢ A [p] type ].
Proof. apply (fun H => type_subs (subs_weak H) H). Qed.

Corollary type_id {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A [id] type ].
Proof. apply (fun H => type_subs  (subs_id (type_press H)) H). Qed.

(**** End Helpers ****)


Theorem eq_subs_inv {Δ Γ y1 y0}:
   [ Δ ⊢ y1 == y0 ~ Γ ] -> [ Δ ⊢ y1 ~ Γ ] /\ [ Δ ⊢ y0 ~ Γ ].
Proof.
   intros.
   dependent induction H; try (tauto).
   -  split. apply id_left_inv in H. assumption.
      assumption.
   -  split. assumption.
      apply id_right_inv in H. assumption.
   -  split.
      apply (subs_comp (subs_comp H H0) H1).
      apply (subs_comp H (subs_comp H0 H1)).
   -  split. 2:assumption.
      (* apply (subs_comp
         (subs_ext H H0 H1)
         (subs_weak H0)). *)
         admit.
   -  split. assumption.
      (* apply (subs_ext (subs_comp H0 (subs_weak H)) H).
      rewrite (eq_type_subs_comp H0 (subs_weak H) H).
      apply (term_subs H0 (term_qar H)). *)
      admit.
   - split. 2:assumption.
      apply (subs_bang (subs_inv_left H)).
(* Qed. *)
Admitted.

Add Parametric Morphism Δ Γ : (SubsJG Δ Γ)
   with signature (eq_subs Δ Γ ==> iff)
   as subs_mor.
Proof.
   intros y d Heq.
   apply eq_subs_inv in Heq as [H_y H_d].
   tauto.
Qed.


Theorem eq_type_inv :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
   intros.
   dependent induction H; try (tauto).
   - split; [apply (type_id H) | apply H].
   - split.
      apply (type_subs (subs_comp H H0) H1).
      apply (type_subs H (type_subs H0 H1)).
Qed.


Corollary term_id {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a [id] @ A ].
Proof.
   intro H.
   rewrite <- (eq_type_subs_id (term_inv H)).
   apply (term_subs (subs_id (term_ctx_inv H)) H).
Qed.

Corollary term_subs_compose {Δ Γ A a y1 y0} :
   [ Δ ⊢ y0 ~ Γ ]
   -> [ Γ ⊢ a @ A [y1] ]
   -> [ Δ ⊢ a [y0] @ A [y1 ∘ y0] ].
Proof.
   intros H_y0 H_a.
   remember (term_inv H_a) as HA.
   inversion HA; subst.
   rewrite (eq_type_subs_comp H_y0 H2 H3).
   apply (term_subs H_y0 H_a).
Qed.

Corollary term_id_type {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ A [id] ].
Proof.
   intro H.
   rewrite (eq_type_subs_id (term_inv H)).
   apply H.
Qed.

(* Corollary self_extension {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ (id # a) ~ (Γ # A) ].
Proof.
   intro H.
   apply (subs_ext
            (subs_id (term_press_ctx H))
            (term_press H)
            (term_id_type H)).
Qed. *)


(*
Corollary eq_subs_beta_id {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ p ∘ (id # a) == id ~ Γ ].
Proof.
   intro H.
   apply (eq_subs_beta
         (subs_id (term_press_ctx H))
         (term_press H)
         (term_id_type H)).
Qed. *)

Theorem eq_term_inv {Γ A a b}:
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   - split; [apply (term_id H) | apply H].
   - split.
      apply (term_subs (subs_comp H H0) H1).
      rewrite (eq_type_subs_comp H H0 (term_inv H1)).
      apply (term_subs H (term_subs H0 H1)).
   - split. 2:assumption.
      (* apply (subs_ext H H0) in H1 as H2.
      apply (eq_subs_beta H H0) in H1 as H3. *)
      admit.
Admitted.

Add Parametric Morphism Γ A : (TermJG Γ A)
   with signature (eq_term Γ A ==> iff)
   as term_jug_eq_term_mor.
Proof.
   intros a b Heq.
   apply eq_term_inv in Heq.
   tauto.
Qed.

Add Parametric Morphism Δ Γ A y (H : [Δ ⊢ y ~ Γ]) : (psub_ext y) with
   signature (eq_term Δ (A [y]) ==> eq_subs Δ (Γ # A))
as eq_subs_ext_mor.
Proof.
   intros a b Heq.
   (* apply (eq_subs_ext2 (eq_subs_refl H) Heq). *)
Abort.


(** End "Presupositions" Theorems **)

Lemma subs_functional {Δ Γ Γ' y}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y ~ Γ' ] -> Γ = Γ'.
Proof.
   dependent induction y generalizing y Δ Γ Γ' ; intros H1 H2; try (tauto).
   - inversion H1; inversion H2; subst.
      reflexivity.
   - inversion H1; inversion H2; subst.
      specialize (IHy2 _ _ _ H5 H11); subst.
      apply (IHy1 _ _ _ H6 H12).
   - inversion H1; subst.
      inversion H2; subst.
      reflexivity.
   - inversion H1; subst.
      inversion H2; subst.
      reflexivity.
   -  inversion H1; subst.
Abort.


(** Exercises **)
(** Exercise 2.2. Show that substitutions Γ ⊢ 𝛾 : Γ.𝐴 satisfying p ◦𝛾= id are in bijection with terms Γ ⊢𝑎: 𝐴. **)
Section Exercise_2_2.
   Let f : preSubs -> preTerm := fun y => (q [y])%term.
   Let g : preTerm -> preSubs := fun a => (id # a)%subs.

   Lemma f_wf {Γ A y } :
      [ Γ ⊢ y ~ Γ # A ] -> [ Γ ⊢ p ∘ y == id ~ Γ ]
      -> ([ Γ ⊢ f y @ A ] ).
   Proof.
      intros H_subs H_id.
      apply (subs_inv_right) in H_subs as HA.
      inversion HA; subst.
      rewrite <- (eq_type_subs_id H2).
   Abort.
      (* rewrite <- (eq_type_subs_S H_id H2).
      apply (term_subs_compose H_subs).
      apply (term_qar H2).
   Qed. *)

Lemma g_wf {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ g a ~ Γ # A ] /\ [ Γ ⊢ p ∘ g a == id ~ Γ ].
Proof.
   intros H_a.
   split.
   apply (self_extension H_a).
   apply (eq_subs_beta_id H_a).
Qed.

Lemma f_g {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ f (g a) == a @ A ].
Proof.
   intros H_a.
   rewrite <- (eq_type_subs_id (term_press H_a)).
   apply (eq_term_beta_qar (subs_id (term_press_ctx H_a)) (term_press H_a) (term_id_type H_a)).
Qed.

Lemma g_f {Γ A y} :
   [ Γ ⊢ y ~ Γ # A ] -> [ Γ ⊢ p ∘ y == id ~ Γ ]
   -> [ Γ ⊢ g (f y) == y ~ Γ # A ].
Proof.
   intros H_subs H_id.
   apply (subs_press_r) in H_subs as HA.
   inversion HA; subst.
   rewrite (eq_subs_eta H2 H_subs) at 2.
   (* apply (eq_subs_ext_S (eq_subs_sym H_id) H2).
   rewrite (eq_type_subs_id H2).
   apply (f_wf H_subs H_id).
Qed. *)
Abort.
End Exercise_2_2.


(***    Exercise 2.3. Show that (𝛾.𝑎)◦𝛿= (𝛾◦𝛿).𝑎[𝛿]. ***)

Lemma Exercise_2_3 {Γ2 Γ1 Γ0 A a y δ} :
[ Γ1 ⊢ y ~ Γ0 ] -> [ Γ2 ⊢ δ ~ Γ1 ] -> [ Γ0 ⊢ A type ] -> [ Γ1 ⊢ a @ A[y] ]
-> [ Γ2 ⊢ (y # a) ∘ δ == (y ∘ δ) # a [δ] ~ Γ0 # A ].
Proof.
intros H_y H_δ H_A H_a.
   rewrite (eq_subs_eta H_A).
      assert([ Γ2 ⊢ p ∘ (y#a ∘ δ) == y ∘ δ ~ Γ0 ]).
      {
         rewrite (eq_subs_comp_assoc H_δ (subs_ext H_y H_A H_a) (subs_weak H_A)).
         eapply (eq_subs_comp_l
         (eq_subs_beta H_y H_A H_a)
         H_δ).
      }
      apply (eq_subs_ext2 H H_A).
      rewrite (eq_type_subs_comp (subs_comp H_δ (subs_ext H_y H_A H_a)) (subs_weak H_A) H_A).
      rewrite (eq_term_subs_comp H_δ (subs_ext H_y H_A H_a) (term_qar H_A)).
      rewrite (eq_type_subs_comp H_δ (subs_ext H_y H_A H_a) (type_subs(subs_weak H_A) H_A)).
      apply (eq_term_subs_T H_δ).
      rewrite <- (eq_type_subs_comp (subs_ext H_y H_A H_a) (subs_weak H_A) H_A).
      rewrite (eq_type_subs_S (eq_subs_beta H_y H_A H_a) H_A).
      apply (eq_term_beta_qar H_y H_A H_a).
      apply (subs_comp H_δ (subs_ext H_y H_A H_a)).
Qed.

(*** Exercise 2.4. Given Δ ⊢𝛾 : Γ and Γ ⊢ A type, construct a substitution that we will
name y.A, satisfying Δ.A[y]⊢𝛾.A: Γ.A. ***)

Lemma Exercise_2_4 {Δ Γ A y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
   -> exists yA, [ Δ # A[y] ⊢ yA ~ (Γ # A) ].
Proof.
   intros H_subs H_type.
   remember (type_subs H_subs H_type) as A_subs.
   remember (subs_weak A_subs) as weak_subs.
   eexists (_ # _)%subs.
   eapply (subs_ext).
   eapply (subs_comp weak_subs H_subs).
   apply (H_type).
   rewrite (eq_type_subs_comp (subs_weak A_subs) H_subs H_type).
   apply (term_qar (type_subs H_subs H_type)).
Qed.

Corollary subs_yA {Δ Γ A y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
   -> [ Δ # A[y] ⊢ (y ∘ p) # q ~ (Γ # A) ].
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
Section Exercise_2_5.
   Local Notation "( a , b )" := (pair a b).
   Let f : preSubs -> (preSubs * preTerm) := fun y => ( (p ∘ y)%subs , q[y]%term ).
   Let g : (preSubs * preTerm) -> preSubs := fun '(y0, a) => (y0 # a)%subs.

   Lemma f_wf2 {Δ Γ A y} :
      [ Δ ⊢ y ~ Γ # A ] ->
      let (y0, a) := f y in
      [ Δ ⊢  y0 ~ Γ ] /\ [ Δ ⊢ a @ A[y0] ].
   Proof.
      intros H_subs.
      apply (subs_press_r) in H_subs as HA.
      inversion HA; subst.
      split.
      apply (subs_comp H_subs (subs_weak H2)).
      apply (term_subs_compose H_subs).
      apply (term_qar H2).
   Qed.

   Lemma g_wf2 {Δ Γ A y0 a} :
      [ Δ ⊢ y0 ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A[y0] ]
      -> [ Δ ⊢ g (y0, a) ~ Γ # A ].
   Proof.
      apply (subs_ext).
   Qed.

   Lemma f_g2 {Δ Γ A y0 a} :
      [ Δ ⊢ y0 ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A[y0] ]
      -> let y := g (y0, a) in
         let (y0', a') := f y in
         [ Δ ⊢ y0' == y0 ~ Γ ] /\ [ Δ ⊢ a' == a @ A[y0] ].
   Proof.
      intros H_y0 H_type H_a.
      split.
      apply (eq_subs_beta H_y0 H_type H_a).
      apply (eq_term_beta_qar H_y0 H_type H_a).
   Qed.

   Lemma g_f2 {Δ Γ A y} :
      [ Δ ⊢ y ~ Γ # A ] ->
      [ Δ ⊢ g (f y) == y ~ Γ # A ].
   Proof.
      intros H_subs.
      apply (subs_press_r) in H_subs as HA.
      inversion HA; subst.
      unfold f.
      symmetry.
      apply (eq_subs_eta H2 H_subs).
   Qed.
End Exercise_2_5.


