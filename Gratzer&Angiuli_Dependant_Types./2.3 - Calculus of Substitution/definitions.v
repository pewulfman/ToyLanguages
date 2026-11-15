   (* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

From Corelib Require Import
      Relation_Definitions
      RelationClasses
      Setoid
      Morphisms.

From Stdlib Require Import
		Arith
      Relation_Operators
      Program.Equality
		Vectors.Vector
		Lists.List.


(** Pre-syntax definitions **)

(** Convention For syntax sorts. On the left is fonction parameters, on the right construction to stay true to the textbook
   Contexts ctx: greek uppercase letters: 𝚪, Δ, ...
   Types t : uppercase letters: A, B, ...
   Terms e : lowercase letters: a, b, ...
   Substitutions g :  greak lowercase :γ, δ, μ ...
**)

Inductive preSubs : Type :=
(** Monoid Structure **)
| psub_id   : preSubs
| psub_comp (y1 y2 : preSubs) : preSubs
(** Actual Stack Manipulation *)
| psub_weak : preSubs
| psub_ext (y : preSubs)(a : preTerm) : preSubs

with preTerm : Type :=
(** Substitution Engine **)
| ptrm_qar : preTerm
| ptrm_subs (a : preTerm) (y : preSubs) : preTerm
(** Actual Language Constructs **)
| ptrm_unit : preTerm
.
Inductive preType : Type :=
(** Substitution Engine **)
| ptyp_subs (A : preType) (y : preSubs) : preType
(** Actual Language Constructs **)
(* | ptyp_base : preType (* not really in the book but needed for logical consistency *)
*)
| ptyp_unit : preType
.
Inductive preCtx :  Type :=
(** Context as a stack of types **)
| pctx_one : preCtx
| pctx_ext (Γ : preCtx) (A : preType) : preCtx
.

(* Coercion ctx_size (Γ : preCtx) : nat := 0. *)
(* Definition preContext : Type := forall n, preCtx n. *)


Fixpoint size (Γ : preCtx) : nat :=
	match Γ with
	| pctx_one => 0
	| pctx_ext Γ' A => S (size Γ')
end.

(** End pre-syntax definitions **)


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


Notation "1"       := (pctx_one).
Notation "Γ # A"   := (pctx_ext Γ A) (at level 2, left associativity) : ctx_scope.

Abbreviation id    := psub_id.
Notation "y1 ∘ y0" := (psub_comp y1 y0) (at level 90, left associativity) : subs_scope.
Abbreviation p     := psub_weak.
Notation "y # a"   := (psub_ext y a)(at level 2, left associativity) : subs_scope.


Notation "A [ y ]" := (ptyp_subs A y) (at level 1): ty_scope.
Abbreviation Unit  := ptyp_unit.

Abbreviation q     := ptrm_qar.
Notation "a [ y ]" := (ptrm_subs a y)(at level 1): term_scope.
Abbreviation tt    := ptrm_unit.

Reserved Notation "[ ⊢ Γ 'cx' ]"          (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]"         (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y ~ Γ ]"         (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A == B 'type' ]" (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a == b @ A ]"    (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y == d ~ Γ ]"    (at level 0, no associativity).

(** End Notations **)

(******************************************************************************)
(** Judgments **)
(**** Context Judgments ****)
Inductive CtxJG : preCtx -> Prop :=
   | ctx_one :
      [ ⊢ 1 cx ]
   | ctx_ext {Γ : preCtx} {A : preType} :
      [ ⊢ Γ cx ] -> [ Γ ⊢ A type ]
      -> [ ⊢  Γ # A cx]

(**** Substitution Judgments ****)
with SubsJG : preCtx -> preCtx -> preSubs -> Prop :=
   | subs_id {Γ : preCtx} :
      [ ⊢ Γ cx ]
      -> [ Γ ⊢ id ~ Γ ]
   | subs_comp {Γ2 Γ1 Γ0 : preCtx} {y1 y0 : preSubs} :
      [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ]
      ->[ Γ2 ⊢ (y0 ∘ y1) ~ Γ0 ]
   | subs_weak {Γ : preCtx} {A : preType} :
      [ Γ ⊢ A type ]
      -> [ Γ # A ⊢ p ~ Γ ]
   | subs_ext {Δ Γ : preCtx} {y : preSubs} {a : preTerm} {A : preType} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A[y] ]
      ->  [ Δ ⊢ (y # a) ~ (Γ # A) ]
	(** compatibility with quotient **)
	| subs_over_ctx_quot_l {Δ Γ : preCtx} {Δ' : preCtx} {y : preSubs} :
		eq_ctx Δ Δ' -> [ Δ ⊢ y ~ Γ ]	-> [ Δ' ⊢ y ~ Γ ]
	| subs_over_ctx_quot_r {Δ Γ : preCtx} {Γ' : preCtx} {y : preSubs} :
		eq_ctx Γ Γ' -> [ Δ ⊢ y ~ Γ ]	-> [ Δ ⊢ y ~ Γ' ]

(*** Type Judgments ****)
with TypeJG : preCtx -> preType -> Prop :=
   | type_subs {Δ Γ : preCtx} {y : preSubs} {A : preType} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
      -> [ Δ ⊢ A [y] type ]
	| type_unit {Γ : preCtx} :
		[ ⊢ Γ cx ]
		-> [ Γ ⊢ Unit type ]
	(** compatibility with quotient **)
	| type_over_ctx_quot {Δ Γ : preCtx} {A : preType} :
		eq_ctx Δ Γ -> [ Δ ⊢ A type ] -> [ Γ ⊢ A type ]

(*** Term Judgments ****)
with TermJG : preCtx -> preType -> preTerm -> Prop :=
	(* The q term is a "generic element" of the type A, which can be substituted by any term of type A. *)
	| term_qar {Γ : preCtx} {A : preType} :
		[ Γ ⊢ A type ]
		-> [ Γ # A ⊢ q @ A [p] ]
	| term_subs {Δ Γ : preCtx} {y : preSubs} {A : preType} {a : preTerm} :
		[ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
		-> [ Δ ⊢ (a [y]) @ A [y] ]
	| term_unit {Γ : preCtx} :
		[ ⊢ Γ cx ]
		-> [ Γ ⊢ tt @ Unit ]
	(** compatibility with quotient **)
	| term_over_ctx_quot {Δ Γ : preCtx} {A : preType} {a : preTerm} :
		eq_ctx Δ Γ -> [ Δ ⊢ a @ A ] -> [ Γ ⊢ a @ A ]
	| term_over_type_quot {Γ : preCtx} {A B : preType} {a : preTerm} :
		[ Γ ⊢ A == B type ] -> [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ B ]

(******************************************************************************)
(** Equivalence Relations **)

(*** Context Equivalence ****)
with eq_ctx : preCtx -> preCtx -> Prop :=
(* | eq_ctx_sym {Γ Δ : preCtx} : eq_ctx Γ Δ -> eq_ctx Δ Γ *)
(* | eq_ctx_trans {Γ Δ Θ : preCtx} : eq_ctx Γ Δ -> eq_ctx Δ Θ -> eq_ctx Γ Θ *)
	| eq_ctx_one : eq_ctx pctx_one pctx_one
	| eq_ctx_ext {Γ Δ : preCtx} {A B : preType} :
		eq_ctx Γ Δ -> [ Γ ⊢ A == B type ]
		(* -> [ Δ ⊢ A == B type ] *)
		-> eq_ctx (Γ # A) (Δ # B)

(**** Substitution Equivalence ****)
with eq_subs : preCtx -> preCtx -> preSubs -> preSubs -> Prop :=
	(** Symmetric Transitive Closure **)
	| eq_subs_sym {Δ Γ : preCtx} {y1 y2 : preSubs} :
		[ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y1 ~ Γ ]
	| eq_subs_trans {Δ Γ : preCtx} {y1 y2 y3 : preSubs} :
		[ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ] -> [ Δ ⊢ y1 == y3 ~ Γ ]
	(** Enforce composition properties (unital + associative) p.31 **)
	| eq_subs_id_left {Δ Γ : preCtx} {y : preSubs}:
		[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ id ∘ y == y ~ Γ ]
	| eq_subs_id_right {Δ Γ : preCtx} {y : preSubs}:
		[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y == y ∘ id ~ Γ ]
	| eq_subs_comp_assoc {Γ3 Γ2 Γ1 Γ0 : preCtx} {y2 y1 y0 : preSubs}:
			[ Γ3 ⊢ y2 ~ Γ2 ] -> [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ]
			-> [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ0 ]
	(** Unicity of bang p.34 **)
	(* | eq_subs_bang {Γ : preCtx} {δ : preSubs} :
		[ Γ ⊢ δ  ~ 1 ] -> [ Γ ⊢ ! == δ ~ 1 ] *)
	(** βη-equivalence for substitution p.34 **)
	| eq_subs_beta {Δ Γ : preCtx} {A : preType} {a : preTerm} {y : preSubs} :
		[ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
		-> [ Δ ⊢ p ∘ y # a == y ~ Γ ]
	| eq_subs_eta {Δ Γ : preCtx} {A : preType} {y : preSubs} :
		[ Γ ⊢ A type ] -> [ Δ ⊢ y ~ Γ # A ]
		-> [ Δ ⊢ y == (p ∘ y) # q[y] ~ (Γ # A) ]
	(** compatibility with quotient **)
	| eq_subs_over_ctx_quot_l {Δ Γ : preCtx} {Δ' : preCtx} {y y' : preSubs} :
		eq_ctx Δ Δ' ->	[ Δ ⊢ y == y' ~ Γ ] -> [ Δ' ⊢ y == y' ~ Γ ]
	| eq_subs_over_ctx_quot_r {Δ Γ : preCtx} {Γ' : preCtx} {y y' : preSubs} :
		eq_ctx Γ Γ' -> [ Δ ⊢ y == y' ~ Γ ] -> [ Δ ⊢ y == y' ~ Γ' ]
	(** Morphism Property ? not clearly stated but implied, also don't know how to prove it **)
	| subs_ext_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a b : preTerm}:
		[ Δ ⊢ y == y' ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a == b @ A[y] ] ->
		[ Δ ⊢ y # a == y' # b ~ Γ # A ]

(**** Type Equivalence ****)
with eq_type : preCtx -> preType -> preType -> Prop :=
	(** Symmetric Transitive Closure **)
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
	(* | eq_type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
		[Δ ⊢ y == y' ~ Γ] -> [Γ ⊢ A type ] -> [Δ ⊢ A [y] == A [y'] type ] *)
	(** Unit p.47 *)
	| eq_type_unit {Δ Γ : preCtx} {y : preSubs} :
		[ Δ ⊢ y ~ Γ ] -> [ Δ  ⊢ Unit[y] == Unit type ]
	(** invarience of base types, implied now and effective when we replace Base for concrete types **)
	(* | eq_type_base { Δ Γ : preCtx} {y : preSubs} :
		[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ b [y] == b type ] *)
	(** compatibility with quotient **)
	| eq_type_over_ctx_quot {Δ Γ : preCtx} {A B : preType} :
		eq_ctx Δ Γ -> [ Δ ⊢ A == B type ] -> [ Γ ⊢ A == B type ]


(**** Term Equivalence ****)
with eq_term : preCtx -> preType -> preTerm -> preTerm -> Prop :=
	(** Symmetric Transitive Closure **)
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
	(** Unicity of unit **)
	| eq_term_unit {Γ : preCtx} {a : preTerm} :
		[ Γ ⊢ a @ Unit ] -> [ Γ ⊢ a == tt @ Unit ]
	(** compatibility with quotient **)
	| eq_term_over_ctx_quot {Δ Γ : preCtx} {A : preType} {a b: preTerm} :
		eq_ctx Δ Γ -> [ Δ ⊢ a == b @ A ] ->
			[ Γ ⊢ a == b @ A ]
	| eq_term_over_type_quot {Γ : preCtx} {A B : preType} {a b : preTerm} :
		[ Γ ⊢ A == B type ] -> [ Γ ⊢ a == b @ A ] ->
		[ Γ ⊢ a == b @ B ]


where "[ ⊢ Γ 'cx' ]"          := (CtxJG Γ)
and   "[ Γ ⊢ A 'type' ]"      := (TypeJG Γ A)
and   "[ Γ ⊢ a @ A ]"         := (TermJG Γ A a)
and   "[ Δ ⊢ y ~ Γ ]"         := (SubsJG Δ Γ y)
and   "[ Γ ⊢ A == B 'type' ]" := (eq_type Γ A B)
and   "[ Γ ⊢ a == b @ A ]"    := (eq_term Γ A a b)
and   "[ Δ ⊢ y == y' ~ Γ ]"   := (eq_subs Δ Γ y y')
.
(** End Judgements *)

(******************************************************************************)
(** Register Equality Relations **)

Lemma eq_ctx_sym : forall Γ Δ : preCtx, eq_ctx Γ Δ -> eq_ctx Δ Γ.
	intros Γ Δ H.
	dependent induction H; try (tauto).
	now apply eq_ctx_one.
	apply eq_ctx_ext.
	now assumption.
	apply eq_type_sym.
	now apply (eq_type_over_ctx_quot H).
Qed.

Lemma eq_ctx_trans : forall Γ Δ Θ : preCtx, eq_ctx Γ Δ -> eq_ctx Δ Θ -> eq_ctx Γ Θ.
	intros Γ Δ Θ H1 H2.
	dependent induction H1 generalizing Θ; try (tauto).
	dependent destruction H2; try (tauto).
	apply eq_ctx_ext.
	now apply IHeq_ctx.
	apply (eq_type_trans H).
	apply eq_ctx_sym in H1.
	now apply (eq_type_over_ctx_quot H1).
Qed.

Add Relation (preCtx) (eq_ctx)
   symmetry proved by (@eq_ctx_sym)
   transitivity proved by (@eq_ctx_trans)
   as eq_ctx_rel.

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
(** Register Morphisms **)
Add Morphism SubsJG
	with signature eq_ctx ==> eq ==> eq ==> iff
as subs_ctx_l_mor.
Proof.
	intros Δ Δ' Hctx Γ y.
	split.
	now apply (subs_over_ctx_quot_l Hctx).
	symmetry in Hctx.
	now apply (subs_over_ctx_quot_l Hctx).
Qed.

Add Parametric Morphism Δ : (SubsJG Δ)
	with signature eq_ctx ==> eq ==> iff
as subs_ctx_r_mor.
Proof.
	intros Γ Γ' Hctx y.
	split.
	now apply (subs_over_ctx_quot_r Hctx).
	symmetry in Hctx.
	now apply (subs_over_ctx_quot_r Hctx).
Qed.

Add Morphism TypeJG with signature eq_ctx ==> eq ==> iff as type_ctx_mor.
Proof.
	intros Δ Γ Hctx A.
	split.
	now apply (type_over_ctx_quot Hctx).
	symmetry in Hctx.
	now apply (type_over_ctx_quot Hctx).
Qed.

Add Morphism TermJG with signature eq_ctx ==> eq ==> eq ==> iff as term_ctx_mor.
Proof.
	intros Δ Γ Hctx A a.
	split.
	now apply (term_over_ctx_quot Hctx).
	symmetry in Hctx.
	now apply (term_over_ctx_quot Hctx).
Qed.

Add Parametric Morphism Γ : (TermJG Γ)
	with signature eq_type Γ ==> eq ==> iff
as term_type_mor.
Proof.
	intros A B Hty a.
	split.
	now apply (term_over_type_quot Hty).
	symmetry in Hty.
	now apply (term_over_type_quot Hty).
Qed.

Add Morphism eq_subs
	with signature eq_ctx ==> eq ==> eq ==> eq ==> iff
as eq_subs_ctx_l_mor.
Proof.
	intros Δ Δ' Hctx Γ y y'.
	split.
	now apply (eq_subs_over_ctx_quot_l Hctx).
	symmetry in Hctx.
	now apply (eq_subs_over_ctx_quot_l Hctx).
Qed.

Add Parametric Morphism Δ : (eq_subs Δ)
	with signature eq_ctx ==> eq ==> eq ==> iff
as eq_subs_ctx_r_mor.
Proof.
	intros Γ Γ' Hctx y y'.
	split.
	now apply (eq_subs_over_ctx_quot_r Hctx).
	symmetry in Hctx.
	now apply (eq_subs_over_ctx_quot_r Hctx).
Qed.

Add Morphism eq_type
	with signature eq_ctx ==> eq ==> eq ==> iff
as eq_type_ctx_mor.
Proof.
	intros Δ Γ Hctx A B.
	split.
	now apply (eq_type_over_ctx_quot Hctx).
	symmetry in Hctx.
	now apply (eq_type_over_ctx_quot Hctx).
Qed.

Add Morphism eq_term
	with signature eq_ctx ==> eq ==> eq ==> eq ==> iff
as eq_term_ctx_mor.
Proof.
	intros Δ Γ Hctx A a.
	split.
	now apply (eq_term_over_ctx_quot Hctx).
	symmetry in Hctx.
	now apply (eq_term_over_ctx_quot Hctx).
Qed.

Add Parametric Morphism Γ : (eq_term Γ)
	with signature eq_type Γ ==> eq ==> eq ==> iff
as eq_term_type_mor.
Proof.
	intros A B Hty a.
	split.
	now apply (eq_term_over_type_quot Hty).
	symmetry in Hty.
	now apply (eq_term_over_type_quot Hty).
Qed.

(* Add Parametric Morphism Δ Γ y A (H : [ Δ ⊢ y ~ Γ ]) (HA : [ Γ ⊢ A type ]) : (psub_ext y)
	with signature eq_term Δ (A [y])%ty ==> eq_subs Δ (Γ # A) as
	eq_subs_ext_mor.
Proof.
	intros a b Heq.
	apply (eq_subs_refl) in H.
	now apply (subs_ext_mor).
Qed. *)

(******************************************************************************)
(** Extra lemmas **)

Lemma ctx_size_eq {Γ Δ : preCtx} :
	eq_ctx Γ Δ -> size Γ = size Δ.
Proof.
	intros H.
	dependent induction H; try (tauto).
	simpl.
	auto.
Qed.

Lemma ctx_size_0 (Γ : preCtx) :
	size Γ = 0 -> Γ = 1.
Proof.
	intros H.
	destruct Γ; try (tauto).
	simpl in H.
	inversion H.
Qed.

Lemma ctx_size_S_n {n : nat} (Γ : preCtx) :
	size Γ = S n -> exists (A : preType) (Γ' : preCtx), Γ = (Γ' # A)%ctx /\ size Γ' = n.
Proof.
	intros H.
	destruct Γ; try (tauto).
	simpl in H.
	inversion H.
	eauto.
Qed.

(******************************************************************************)
(** Non Axiomatics Extensions **)

Fixpoint shift_n (n : nat) : preSubs :=
	match n with
	| 0 => id
	| S n' => (shift_n n') ∘ p
end.

Notation "!"       := (shift_n _) : subs_scope.

Fixpoint psubs_list_ext (y : preSubs) (aL : list preTerm): preSubs :=
	match aL with
	| nil => y
	| a :: aL' => psubs_list_ext y # a aL'
	end.

Notation "y #:: aL" := (psubs_list_ext y aL ) (at level 2, left associativity) : subs_scope.

Fixpoint pctx_list_ext (Γ : preCtx) (AL : list preType) : preCtx :=
	match AL with
	| nil => Γ
	| A :: AL' => pctx_list_ext Γ # A AL'
	end.
Notation "Γ #:: AL" := (pctx_list_ext Γ AL ) (at level 2, left associativity) : ctx_scope.

Lemma subs_bang {Γ : preCtx} :
	[ ⊢ Γ cx ] -> [ Γ ⊢ (shift_n (size Γ)) ~ 1 ].
Proof.
	intros HΓ.
	induction HΓ.
	-	apply subs_id. (* base case *)
		apply ctx_one.
	-	simpl.
		apply (subs_comp (subs_weak H) IHHΓ).
Qed.


(* Lemma subs_list_ext {Δ Γ : preCtx} {y : preSubs} {AaL : list (preTerm * preType)} :
	[ Δ ⊢ y ~ Γ ] ->
	(forall (aA : preTerm * preType) (l1 l2 : list (preTerm * preType))
		(Hin : AaL = l1 ++ aA :: l2),
	 	[ (pctx_list_ext Γ (List.map snd l2)) ⊢ (snd aA) type ]
		/\ [ Δ ⊢ (fst aA) @ (snd aA)[ (psubs_list_ext y (List.map fst l2))] ]) ->
	[ Δ ⊢ psubs_list_ext y (List.map fst AaL) ~ pctx_list_ext Γ (List.map snd AaL) ].
Proof.
	intros Hy HA.
	dependent induction AaL generalizing Δ Γ y AaL.
	-	now simpl.
	-
		simpl.
		pose proof (HA a List.nil AaL) as [H1 H2].
		tauto.
		apply subs_ext.
		apply (IHAaL Hy).
		intros aA l1 l2 Hin.
		apply (HA aA (a :: l1) l2).
		rewrite Hin.
		apply (app_comm_cons).
		apply H1.
		apply H2.
Qed. *)


(******************************************************************************)
(** Proof of pressupositions For Jugements **)

Lemma ctx_ext_inv { Γ : preCtx} {A : preType} :
	[ ⊢ Γ # A cx ] -> [ ⊢ Γ cx ] /\ [ Γ ⊢ A type ].
Proof.
	intros H.
	dependent induction H; try (tauto).
Qed.

Lemma subs_press {Δ Γ : preCtx} {y : preSubs} (H: [ Δ ⊢ y ~ Γ ]) :
	[ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
with type_press {Γ : preCtx} {A : preType} (H: [ Γ ⊢ A type ]) :
	[ ⊢ Γ cx ]
with eq_ctx_press {Γ Δ : preCtx} (H: eq_ctx Γ Δ) :
	[ ⊢ Γ cx ] /\ [ ⊢ Δ cx ]
with eq_type_press {Γ : preCtx} {A B : preType} (H: [ Γ ⊢ A == B type ]) :
	[ Γ ⊢ A type ] /\ [ Γ ⊢ B type ]
.	Proof.
	(* subs_press *)
-	dependent induction H; try (tauto).
	apply type_press in H as HΓ.
	split; [now apply ctx_ext | now assumption].
	destruct IHSubsJG as [HΔ HΓ].
	split; [now assumption | now apply ctx_ext].
	now apply eq_ctx_press in H.
	now apply eq_ctx_press in H.
	Guarded.

	(* type_press *)
-	dependent induction H; try (tauto).
	now apply subs_press in H.
	now apply eq_ctx_press in H.
	Guarded.

	(* eq_ctx_inv *)
-	dependent induction H; try (tauto).
	+	now split; apply ctx_one.
	+	apply (eq_type_press) in H0 as [HA HB].
		rewrite H in HB.
		now split; apply ctx_ext.
		Guarded.

	(* eq_type_press *)
- 	dependent induction H; try (tauto).
	+	split.
		apply (type_subs (subs_id (type_press _ _ H)) H).
		now apply H.
	+	split.
		now apply (type_subs (subs_comp H H0) H1).
		now apply (type_subs H (type_subs H0 H1)).
	+	pose proof (subs_press _ _ _ H) as [HΔ HΓ].
		split.
			now apply (type_subs H), type_unit.
			now apply type_unit.
	+	now split; rewrite <- H.
Qed.


Lemma term_press {Γ : preCtx} {A : preType} {a : preTerm} (H: [ Γ ⊢ a @ A ]) :
	[ ⊢ Γ cx ] /\ [ Γ ⊢ A type ].
Proof.
	dependent induction H; try (tauto).
		apply type_press in H as HΓ.
		split; [now apply ctx_ext | now apply (type_subs (subs_weak H))].
		destruct IHTermJG as [HΓ HA].
		apply (type_subs H) in HA.
		apply subs_press in H as [HΔ HΓ'].
		now tauto.
		split; [now exact H | now apply type_unit].
		destruct IHTermJG as [_ HA].
		rewrite H in HA.
		apply eq_ctx_press in H as [HΔ HΓ].
		now tauto.
		destruct IHTermJG as [HΓ _].
		apply eq_type_press in H as [HA HB].
		now tauto.
Qed.

Lemma eq_subs_bang {Γ : preCtx} {δ : preSubs} :
	[ ⊢ Γ cx ] -> [ Γ ⊢ δ  ~ 1 ]
	-> [ Γ ⊢ (shift_n (size Γ)) == δ ~ 1 ].
Proof.
	intros HΓ Hδ.
	dependent induction Hδ.
	- simpl.
		apply eq_subs_refl, subs_id, H.
	-	admit.
	-	simpl.
		apply eq_subs_id_left, subs_weak, H.
	-	apply (eq_subs_over_ctx_quot_l H).
		apply ctx_size_eq in H.
		rewrite <- H.
		apply subs_press in Hδ as [HΔ _].
		now apply IHHδ.
	-	inversion H; subst.
		now apply IHHδ.
Abort.


(** Normal form for substitution *)
Definition subs_to_normal_form {Δ Γ : preCtx} {y : preSubs} (Hy : [ Δ ⊢ y ~ Γ ]) :
	{ aL : list preTerm &
		[ Δ ⊢ y == psubs_list_ext (shift_n (size Δ)) aL ~ Γ]
		/\ List.length aL = ctx_len Γ }.
Proof.
	dependent induction Γ generalizing Δ.
	-	exists List.nil.
		simpl.
		split.
		symmetry.
		now apply (eq_subs_bang Hy).
		reflexivity.
	-	pose proof (subs_press Hy) as [HΔ HΓA].
		apply ctx_ext_inv in HΓA as [HΓ HA].
		specialize (IHΓ _ _ (subs_comp Hy (subs_weak HA))) as [aL [Heq Hlen]].
		exists (q [y]%term :: aL).
		simpl.
		rewrite (eq_subs_eta HA Hy) at 1.
		split.
		apply (subs_ext_mor Heq HA).
		apply eq_term_refl.
		rewrite (eq_type_subs_comp Hy (subs_weak HA) HA).
		apply (term_subs Hy).
		apply (term_qar HA).
		now apply eq_S.
Defined.

Theorem substitution_extensionality {Δ Γ : preCtx} {y y' : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y' ~ Γ ] ->
	(forall (A : preType), [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ]) ->
	(forall (A : preType) (a : preTerm), [ Γ ⊢ a @ A] -> [ Δ ⊢ a [y] == a [y'] @ A [y]]) ->
	[ Δ ⊢ y == y' ~ Γ ].
Proof.
-	intros Hy Hy' IHA IHa.
	dependent induction Γ generalizing Δ.
	+	rewrite <- (eq_subs_bang Hy).
		now apply (eq_subs_bang Hy').
	+
	pose proof (subs_press Hy) as [HΔ HΓA].
	inversion HΓA; subst.
	rewrite (eq_subs_eta H2 Hy).
	rewrite (eq_subs_eta H2 Hy').
	apply subs_ext_mor.
	apply IHΓ.
	now apply (subs_comp Hy (subs_weak H2)).
	now apply (subs_comp Hy' (subs_weak H2)).
	intros A0 HA0.
	rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
	rewrite (eq_type_subs_comp Hy' (subs_weak H2) HA0).
	apply IHA.
	now apply (type_subs (subs_weak H2) HA0).
	intros A0 a Ha.
	pose proof (term_press Ha) as [_ HA0].
	rewrite (eq_term_subs_comp Hy (subs_weak H2) Ha).
	rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
	transitivity (a [p] [y'])%term.
	apply IHa.
	apply (term_subs (subs_weak H2) Ha).
	symmetry.
	rewrite (IHA _ (type_subs (subs_weak H2) HA0)).
	rewrite <- (eq_type_subs_comp Hy' (subs_weak H2) HA0).
	now apply (eq_term_subs_comp Hy' (subs_weak H2) Ha).
	apply H2.
	rewrite (eq_type_subs_comp Hy (subs_weak H2) H2).
	apply IHa.
	now apply (term_qar H2).
Qed.



Definition EqSubsNormalForm {Δ Γ : preCtx} {y y' : preSubs} (Hy : [ Δ ⊢ y ~ Γ ]) (Hy' : [ Δ ⊢ y' ~ Γ ]) : Prop :=
	let '(existT _ aL Ha) := subs_to_normal_form Hy in
	let '(existT _ bL Hb) := subs_to_normal_form Hy' in
	List.Forall2
		(fun a b => exists Θ A, [ Θ ⊢ A type ] /\ [ Θ ⊢ a == b @ A ])
		aL bL.

Lemma EqSubsNormalForm_sym {Δ Γ : preCtx} {y y' : preSubs}
	(Hy : [ Δ ⊢ y ~ Γ ]) (Hy' : [ Δ ⊢ y' ~ Γ ]) :
	EqSubsNormalForm Hy Hy' ->
	EqSubsNormalForm Hy' Hy.
Proof.
	unfold EqSubsNormalForm.
	destruct (subs_to_normal_form Hy) as [aL [Ha Hlen]].
	destruct (subs_to_normal_form Hy') as [bL [Hb Hlen']].
	intros H.
	apply Forall2_flip.
	revert H.
	apply Forall2_impl.
	intros a b [Θ [A [HA Heq]]].
	exists Θ, A.
	now symmetry in Heq.
Qed.


(* Theorem subs_ext_normal_form {Δ Γ : preCtx} {y : preSubs} {A : preType} {a : preTerm}
	(Hy : [ Δ ⊢ y ~ Γ ])
	(HA : [ Γ ⊢ A type ]) (Ha : [ Δ ⊢ a @ A [y] ]) :
	let (aL, _) := subs_to_normal_form Hy in
	let (bL, _) := subs_to_normal_form (subs_ext Hy HA Ha) in
	List.Forall2
		(fun a b => exists Θ A, [ Θ ⊢ A type ] /\ [ Θ ⊢ a == b @ A ])
 		(a :: aL) bL.
Proof.
	dependent induction Γ generalizing Δ.
	-	simpl.
		auto.
		now apply (eq_subs_bang Hy). *)


Theorem eq_sub_norm {Δ Γ : preCtx} {y y': preSubs} (Hy : [ Δ ⊢ y ~ Γ ]) (Hy' : [ Δ ⊢ y' ~ Γ ]) :
	[ Δ ⊢ y == y' ~ Γ ] <-> EqSubsNormalForm Hy Hy'.
Proof.
	split.
	intros H.
	dependent induction H.
	- specialize (IHeq_subs Hy' Hy).
		now symmetry.
	dependent induction Γ generalizing Δ.
	-	split; intros H.
		unfold EqSubsNormalForm.
		simpl.
		now apply Forall2_nil.
		rewrite <- (eq_subs_bang Hy).
		apply (eq_subs_bang Hy').
	-	split; intros H.
		unfold EqSubsNormalForm.
		simpl.


(* Lemma eq_subs_ext_inv {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y == y' ~ Γ # A ] ->
	[ Δ ⊢ p ∘ y == p ∘ y' ~ Γ ].
Proof.
	intros H.
	dependent induction H.
	- specialize (IHeq_subs _ _ eq_refl).
		now symmetry.
	-	specialize (IHeq_subs1 _ _ eq_refl).
		specialize (IHeq_subs2 _ _ eq_refl).
		now transitivity (p ∘ y2)%subs.
	-	rewrite <- (eq_subs_bang Hy).
	now apply (eq_subs_bang Hy').
	dependent induction Γ generalizing Δ.
	-
		rewrite (eq_subs_eta H3 Hy).
		rewrite (eq_subs_eta H3 Hy').
		apply subs_ext_mor.
		eapply IHΓ.
		apply H2.
		now apply (subs_comp Hy (subs_weak H3)).
		now apply (subs_comp Hy' (subs_weak H3)). *)

(* Lemma weak_comp_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y == y' ~ Γ # A ] ->
	[ Δ ⊢ p ∘ y == p ∘ y' ~ Γ ].
Proof.
	intros Heq.
	dependent induction H. *)

Lemma __subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	{Hy1 : [ Δ ⊢ y1 ~ Γ ]} {Hy1' : [ Δ ⊢ y1' ~ Γ ]}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ]
with __subs_comp_mor_r {Δ Γ Θ : preCtx} {y1  : preSubs} {y0 y0' : preSubs}
	(Hy1 : [ Δ ⊢ y1 ~	Γ ])
	(* (Hy0 : [ Γ ⊢ y0 ~ Θ ]) (Hy0' : [ Γ ⊢ y0' ~ Θ ]) *)
	(HeqY0 : [ Γ ⊢ y0 == y0' ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0' ∘ y1) ~ Θ ]
with subs_ext_dist {Δ Γ Θ : preCtx} {y d : preSubs} {A : preType} {a : preTerm}
	(Hd : [ Δ ⊢ d ~ Γ ]) (Hy : [ Γ ⊢ y ~ Θ ]) (HA : [ Θ ⊢ A type ]) (Ha : [ Γ ⊢ a @ A[y] ]) :
	[ Δ ⊢ y # a ∘ d == (y ∘ d) # a [d] ~ Θ # A ]
.	Proof.
	(* subs_comp_mor_l *)
*	dependent induction Hy0 generalizing Δ y1 y1' Hy1 Hy1' HeqY1.
	- 	admit.
	-	rewrite (eq_subs_id_left Hy1).
		rewrite (eq_subs_id_left Hy1').
		now apply HeqY1.
	-
		rewrite <- (eq_subs_comp_assoc Hy1 Hy0_1 Hy0_2).
		rewrite <- (eq_subs_comp_assoc Hy1' Hy0_1 Hy0_2).
		apply IHHy0_2.
		apply (subs_comp Hy1 Hy0_1).
		apply (subs_comp Hy1' Hy0_1).
		now apply IHHy0_1.
		Guarded.
	-	rewrite (subs_ext_dist _ _ _ y y1 A a Hy1 Hy0 H H0).
		rewrite (subs_ext_dist _ _ _ y y1' A a Hy1' Hy0 H H0).
		apply subs_ext_mor.
		now apply IHHy0.
		apply H.
		rewrite (eq_type_subs_comp Hy1 Hy0 H).
		Guarded.
		admit.
	-	rewrite <- (eq_subs_bang (subs_comp Hy1 (subs_bang H))).
		exact (eq_subs_bang (subs_comp Hy1' (subs_bang H))).
	-	apply IHHy0; now rewrite H.
	-	rewrite <- H.
		now apply IHHy0.

*	dependent induction HeqY0 generalizing Δ y1 Hy1.
	-	specialize (IHHeqY0 _ _ Hy1).
		now symmetry.
	-	specialize (IHHeqY0_1 _ _ Hy1).
		specialize (IHHeqY0_2 _ _ Hy1).
		now transitivity (y2 ∘ y1)%subs.
	-	pose proof (subs_press H) as [HΔ HΓ].
		rewrite <- (eq_subs_comp_assoc Hy1 H (subs_id HΓ)).
		now apply (eq_subs_id_left (subs_comp Hy1 H)).
	-	pose proof (subs_press H) as [HΔ HΓ].
		Guarded.
		rewrite <- (eq_subs_comp_assoc Hy1 (subs_id HΔ) H).
		apply (__subs_comp_mor_l _ _ _ _ _ _ Hy1 (subs_comp Hy1 (subs_id HΔ))).
		symmetry.
		apply (eq_subs_id_left Hy1).
		apply H.
		Guarded.
	-	admit.
	-	pose proof (subs_press Hy1) as [HΔ HΓ].
		rewrite <- (eq_subs_bang (subs_comp Hy1 (subs_bang HΓ))).
		exact (eq_subs_bang (subs_comp Hy1 H)).
	-	admit.
	-	admit.
	-	apply IHHeqY0; now rewrite H.
	-	rewrite <- H.
		now apply IHHeqY0.
	-	admit.
	Guarded.

*	pose proof (subs_ext Hy HA Ha) as Hya.
	pose proof (subs_comp Hd Hya) as Hyad.
	rewrite (eq_subs_eta HA Hyad).
	apply subs_ext_mor.
	rewrite (eq_subs_comp_assoc Hd Hya (subs_weak HA)).
	Guarded.
	apply (__subs_comp_mor_r _ _ _ _ _ _ Hd (eq_subs_beta Hy HA Ha)).
	Guarded.
		symmetry.
		pose proof (eq_subs_beta Hy HA Ha) as Hbeta.
		symmetry in Hbeta.
		(* Guarded. *)
		admit.
		apply HA.
		rewrite (eq_type_subs_comp Hyad (subs_weak HA) HA).
		apply (term_subs Hyad).
		Guarded.
		now apply (term_qar HA).
	+	apply eq_subs_ext_mor_T.
		apply (subs_comp Hd Hy).
		apply HA.
		pose proof (eq_term_subs_comp Hd Hya (term_qar HA)) as Heq.
		pose proof (eq_subs_beta Hy HA Ha) as Hbeta.
		Guarded.
		pose proof (subs_comp_mor_l _ _ _ _ _ _ Hbeta Hd) as Hbeta'.
		Guarded.
		rewrite <- (eq_subs_comp_assoc Hd Hya (subs_weak HA)) in Hbeta'.
		pose proof (eq_type_subs_mor Hbeta' HA) as Hty.
		rewrite (eq_type_subs_comp Hyad (subs_weak HA) HA) in Hty.
		rewrite Hty in Heq.
		rewrite Heq.
		rewrite (eq_type_subs_comp Hd Hy HA).
		apply (eq_term_subs_mor_T _ _ _ _ _ _ Hd).
		apply (eq_term_beta_qar Hy HA Ha).
		Guarded.
Qed.


Lemma type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType}
	(* {Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]} *)
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) : [ Δ ⊢ A[y] == A[y'] type ]
. Proof.
	dependent induction HeqY generalizing A.
	- specialize (IHHeqY _ HA).
		now symmetry.
	-	specialize (IHHeqY1 _ HA).
		specialize (IHHeqY2 _ HA).
		now transitivity (A[y2])%ty.
	-	admit.
	-
		pose proof (subs_press H) as [HΔ HΓ].
		rewrite (eq_type_subs_comp (subs_id HΔ) H HA).
		symmetry.
		apply (eq_type_subs_id).
		apply (type_subs H HA).
	-
	-


Lemma qar_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y == y' ~ Γ ] -> [ Γ ⊢ A type ]
	-> [ Δ ⊢ q[y] == q[y'] @ A[p][y]]
Proof.
	intros Heq HA.
	dependent induction Heq generalizing A.
	- specialize (IHHeq _ HA).
		split; now symmetry.
	-

	rewrite (eq_subs_eta H2 Heq).
	rewrite (eq_type_subs_comp Heq (subs_weak H2) H2).
	rewrite (eq_term_subs_comp Heq (subs_weak H2) (term_qar H2)).
	apply eq_term_refl.
	apply (term_qar (type_subs Heq H2)).

Lemma __subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	{Hy1 : [ Δ ⊢ y1 ~ Γ ]} {Hy1' : [ Δ ⊢ y1' ~ Γ ]}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ]
with __type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) : [ Δ ⊢ A[y] == A[y'] type ]
with __term_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a : preTerm}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) (Ha : [ Γ ⊢ a @ A ]) : [ Δ ⊢ a [y] == a [y'] @ A [y] ]
. Proof.
- dependent induction Θ generalizing Δ Γ.
	rewrite <- (eq_subs_bang (subs_comp Hy1 Hy0)).
	apply (eq_subs_bang (subs_comp Hy1' Hy0)).
	pose proof (subs_press Hy0) as [HΓ HΘA].
	inversion HΘA; subst.
	rewrite (eq_subs_eta H2 (subs_comp Hy1 Hy0)).
	rewrite (eq_subs_eta H2 (subs_comp Hy1' Hy0)).
	apply subs_ext_mor.
	+ rewrite (eq_subs_comp_assoc Hy1 Hy0 (subs_weak H2)).
		rewrite (eq_subs_comp_assoc Hy1' Hy0 (subs_weak H2)).
		apply (IHΘ _ _ _ _ _ Hy1 Hy1' HeqY1).
		apply (subs_comp Hy0 (subs_weak H2)).
	+	apply H2.
	+	rewrite (eq_type_subs_comp (subs_comp Hy1 Hy0) (subs_weak H2) H2).
		rewrite (eq_term_subs_comp Hy1 Hy0 (term_qar H2)).
		rewrite (eq_type_subs_comp Hy1 Hy0 (type_subs (subs_weak H2) H2)).
		transitivity (q [y0] [y1'])%term.
		pose proof (type_subs Hy0 (type_subs (subs_weak H2) H2)) as HApy.
		pose proof (term_subs Hy0 (term_qar H2)) as Hqy.
		Guarded.
		apply (
			__term_subs_mor Δ Γ y1 y1' (A[p][y0])%ty (q[y0])%term Hy1 Hy1' HeqY1
			HApy Hqy
		).
		Guarded.
		Guarded.
		apply (subs_comp Hy0 (subs_weak H2)).

-	dependent induction Hy0 generalizing Δ y1 y1' Hy1 Hy1' HeqY1.
	+	apply substitution_extensionality.
		apply (subs_comp Hy1 (subs_weak H)).
		apply (subs_comp Hy1' (subs_weak H)).
		intros A0 HA0.
		rewrite (eq_type_subs_comp  Hy1 (subs_weak H) HA0).
		rewrite (eq_type_subs_comp  Hy1' (subs_weak H) HA0).
		Guarded.
		apply (__type_subs_mor _ _ _ _ _
				Hy1
				Hy1' HeqY1
				).
				Guarded.
				(type_subs (subs_weak H) HA0)


		*	specialize (IHHeqY1 _ _ H eq_refl).
			now symmetry.
		*	specialize (IHHeqY1_1 _ _ H eq_refl).
			specialize (IHHeqY1_2 _ _ H eq_refl).
			now transitivity (p ∘ y2)%subs.
		*	admit.
		*	pose proof (subs_press H0) as [HΔ _].
			rewrite (eq_subs_comp_assoc (subs_id HΔ) H0 (subs_weak H)).
			apply (eq_subs_id_right (subs_comp H0 (subs_weak H))).
		*	admit. (* ext *)
		*

		apply HΘ.
		apply (subs_comp Hy1 (subs_weak H)).
		apply (subs_comp Hy1' (subs_weak H)).
		intros A0 HA0.
		Guarded.
		apply (__type_subs_mor _ _ _ _ _ _1).
	dependent induction Θ generalizing Δ Γ.
	-	rewrite <- (eq_subs_bang (subs_comp Hy1 Hy0)).
		apply (eq_subs_bang (subs_comp Hy1' Hy0)).
Lemma __subs_comp_mor {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 y0' : preSubs}
	(HΘ : [ ⊢ Θ cx ])
	(Hy0 : [ Γ ⊢ y0 ~ Θ ]) (Hy0' : [ Γ ⊢ y0' ~ Θ ])
	(HeqY0 : [ Γ ⊢ y0 == y0' ~ Θ ])
	(Hy1 : [ Δ ⊢ y1 ~ Γ ]) (Hy1' : [ Δ ⊢ y1' ~ Γ ])
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0' ∘ y1') ~ Θ ]
(* with __type_subs_mor_T {Δ Γ : preCtx} {y : preSubs} {A B : preType}
	(Hy : [ Δ ⊢ y ~ Γ ]) {HA : [ Γ ⊢ A type ]} {HB : [ Γ ⊢ B type ]}
	(HeqAB : [ Γ ⊢ A == B type ]) : [ Δ ⊢ A[y] == B[y] type ]
with __term_subs_mor_T  {Δ Γ : preCtx} {y : preSubs} {A : preType} {a b : preTerm}
	(Hy : [ Δ ⊢ y ~ Γ ])
	 (HA : [ Γ ⊢ A type ])
	 {Ha : [ Γ ⊢ a @ A ]} {Hb : [ Γ ⊢ b @ A ]}
	 (HeqAB : [ Γ ⊢ a == b @ A ])
	 : [ Δ ⊢ a [y] == b [y] @ A [y] ] *)
.	Proof.
	apply substitution_extensionality.
	apply HΘ.
	apply (subs_comp Hy1 Hy0).
	apply (subs_comp Hy1' Hy0').
		rewrite (eq_subs_eta H2 (subs_comp Hy0 Hy)).
		rewrite (eq_subs_eta H2 (subs_comp Hy0 Hy')).
		apply subs_ext_mor.
		* rewrite (eq_subs_comp_assoc Hy0 Hy (subs_weak H2)).
			rewrite (eq_subs_comp_assoc Hy0 Hy' (subs_weak H2)).
			eapply (__subs_comp_mor_r _ _ _ _ _ _ H1).
			apply (subs_comp Hy0 (subs_weak H2)).
		* apply H2.
		* rewrite (eq_type_subs_comp (subs_comp Hy0 Hy) (subs_weak H2) H2).
			rewrite (eq_term_subs_comp Hy0 Hy (term_qar H2)).
			rewrite (eq_type_subs_comp (subs_comp Hy0 Hy') (subs_weak H2) H2).
			rewrite (eq_term_subs_comp Hy0 Hy' (term_qar H2)).
			transitivity (q [y'] [y0])%term.
			Guarded.
			eapply (__term_subs_mor_T _ _ _ _ _ _ H1).
			apply (subs_comp Hy0 (subs_weak H2)).
			now apply HeqAB.




Lemma __type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ])
	(HA : [ Γ ⊢ A type ])
	{Hm : forall { Θ : preCtx} {y0 : preSubs}
		(* {HΘ : [ ⊢ Θ cx ]}
		{Hy1 : [ Δ ⊢ y1 ~ Γ ]} {Hy1' : [ Δ ⊢ y1' ~ Γ ]} *)
		(Hy0 : [ Γ ⊢ y0 ~ Θ ]),
		[ Δ ⊢ (y0 ∘ y) == (y0 ∘ y') ~ Θ ] }
	: [ Δ ⊢ A[y] == A[y'] type ]
. Proof.
	dependent induction HA generalizing Δ y y' Hy Hy' HeqY.
	-	rewrite (eq_type_base Hy').
		now apply (eq_type_base Hy).
	-	rewrite <- (eq_type_subs_comp Hy H HA).
		rewrite <- (eq_type_subs_comp Hy' H HA).
		apply IHHA.
		apply (subs_comp Hy H).
		apply (subs_comp Hy' H).
		eapply Hm.
		apply H.
		intros Θ y1 Hy1.
		rewrite (eq_subs_comp_assoc Hy H Hy1).
		rewrite (eq_subs_comp_assoc Hy' H Hy1).
		apply Hm.
		apply (subs_comp H Hy1).
	-	apply IHHA.
		1-3: now rewrite H.
		intros Θ y1 Hy1.
		apply Hm.
		now rewrite <- H.
Qed.

Lemma __subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	{HΘ : [ ⊢ Θ cx ]}
	{Hy1 : [ Δ ⊢ y1 ~ Γ ]} {Hy1' : [ Δ ⊢ y1' ~ Γ ]}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ]
with __term_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a : preTerm}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) (Ha : [ Γ ⊢ a @ A ]) : [ Δ ⊢ a [y] == a [y'] @ A [y] ]
.	Proof.
* dependent induction Θ generalizing Δ Γ.
	-	rewrite <- (eq_subs_bang (subs_comp Hy1 Hy0)).
		apply (eq_subs_bang (subs_comp Hy1' Hy0)).
	-	inversion HΘ; subst.
		rewrite (eq_subs_eta H2 (subs_comp Hy1 Hy0)).
		rewrite (eq_subs_eta H2 (subs_comp Hy1' Hy0)).
		apply subs_ext_mor.
		+ rewrite (eq_subs_comp_assoc Hy1 Hy0 (subs_weak H2)).
			rewrite (eq_subs_comp_assoc Hy1' Hy0 (subs_weak H2)).
			eapply (IHΘ _ _ _ _ _ H1 Hy1 Hy1' HeqY1).
			apply (subs_comp Hy0 (subs_weak H2)).
		+	apply H2.
		+ 	rewrite (eq_type_subs_comp (subs_comp Hy1 Hy0) (subs_weak H2) H2).
			rewrite (eq_term_subs_comp Hy1 Hy0 (term_qar H2)).
			rewrite (eq_type_subs_comp Hy1 Hy0 (type_subs (subs_weak H2) H2)).
			transitivity (q [y0 ] [y1'])%term.
			Guarded.
			eapply __term_subs_mor.
			apply Hy1.
			apply Hy1'.
			apply HeqY1.
			apply (type_subs Hy0 (type_subs (subs_weak H2) H2)).
			apply (term_subs Hy0 (term_qar H2)).
			Guarded.
			apply (subs_comp Hy1' Hy0).
			eapply IHΘ.
Qed.

with __type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) : [ Δ ⊢ A[y] == A[y'] type ]
with __term_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a : preTerm}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) (Ha : [ Γ ⊢ a @ A ]) : [ Δ ⊢ a [y] == a [y'] @ A [y] ]
.
Proof.
	(*comp_mor *)
-	dependent induction HeqY1 generalizing Θ y0.
	+  specialize (IHHeqY1 _ _ Hy0).
		now symmetry.
	+  specialize (IHHeqY1_1 _ _ Hy0).
		specialize (IHHeqY1_2 _ _ Hy0).
		now transitivity (y0 ∘ y2)%subs.
	+ admit.
	+
		(* rewrite (eq_subs_comp_assoc (subs_id _) H Hy0). *)
		admit.
	+	admit.
	+	admit.

		rewrite <- (eq_subs_comp Hy1 Hy0).
		rewrite <- (eq_subs_comp Hy1' Hy0).
		now apply IHHeqY1.
	+	rewrite <- (eq_subs_bang (subs_comp Hy1 Hy0)).
		now apply (eq_subs_bang (subs_comp Hy1' Hy0)).
	+	apply substitution_extensionality.
		apply HΘ.
		apply (subs_comp Hy1 Hy0).
		apply (subs_comp Hy1' Hy0).
		intros A0 HA0.
		rewrite (eq_type_subs_comp Hy1 Hy0 HA0).
		rewrite (eq_type_subs_comp Hy1' Hy0 HA0).
		Guarded.
		apply (__type_subs_mor _ _ _ _ _ Hy1 Hy1' HeqY1 (type_subs Hy0 HA0)).
		Guarded.
	-	intros A a HA Ha.
		rewrite (eq_term_subs_comp Hy1 Hy0 Ha).
		rewrite (eq_type_subs_comp Hy1 Hy0 HA).
		transitivity (a [y0] [y1'])%term.
		Guarded.
		now apply eq_term_sym.

(******************************************************************************)
(** Proof of pressupositions For Jugements **)

Lemma eq_ctx_press {Γ Δ : preCtx} (H: eq_ctx Γ Δ) :
	[ ⊢ Γ cx ] /\ [ ⊢ Δ cx ]
with eq_subs_press {Δ Γ : preCtx} {y y' : preSubs} (H: [ Δ ⊢ y == y' ~ Γ ]) :
	[ Δ ⊢ y ~ Γ ] /\ [ Δ ⊢ y' ~ Γ ]
with eq_type_press {Γ : preCtx} {A B : preType} (H: [ Γ ⊢ A == B type ]) :
	[ Γ ⊢ A type ] /\ [ Γ ⊢ B type ]
with eq_term_press {Γ : preCtx} {A : preType} {a b : preTerm} (H: [ Γ ⊢ a == b @ A ]) :
	[ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ]
with subs_press {Δ Γ : preCtx} {y : preSubs} (H: [ Δ ⊢ y ~ Γ ]) :
	[ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
with type_press {Γ : preCtx} {A : preType} (H: [ Γ ⊢ A type ]) :
	[ ⊢ Γ cx ]
with term_press {Γ : preCtx} {A : preType} {a : preTerm} (H: [ Γ ⊢ a @ A ]) :
	[ ⊢ Γ cx ] /\ [ Γ ⊢ A type ]
(* needed because of subs_ext_mor *)
with type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType}
	{Hy : [ Δ ⊢ y ~ Γ ]} {Hy' : [ Δ ⊢ y' ~ Γ ]}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HA : [ Γ ⊢ A type ]) : [ Δ ⊢ A[y] == A[y'] type ]
with subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ]
.	Proof.
	(* eq_ctx_inv *)
-	dependent induction H.
	split; now apply ctx_one.
	apply eq_type_press in H0 as [HA HB].
	rewrite H in HB.
	split; now apply ctx_ext.

	(* eq_subs_press *)
- dependent induction H.
	+	now tauto.
	+	now tauto.
	+	apply subs_press in H as Hctx.
		split.
			apply (subs_comp H), subs_id, Hctx.
			apply H.
	+	apply subs_press in H as Hctx.
		split.
			apply H.
			apply (subs_comp (subs_id (proj1 Hctx)) H).
	+	split.
		apply (subs_comp (subs_comp H H0) H1).
		apply (subs_comp H (subs_comp H0 H1)).
	(* bang *)
	+	split.
		apply (subs_bang (proj1 (subs_press _ _ _ H))).
		apply H.
	+	split.
		apply (subs_comp
					(subs_ext H H0 H1)
					(subs_weak H0)).
		apply H.
	+	split.
		apply H0.
		apply (subs_ext
				(subs_comp H0 (subs_weak H))
				H).
		rewrite (eq_type_subs_comp H0 (subs_weak H) H).
		apply (term_subs H0 (term_qar H)).
	+	rewrite H in IHeq_subs.
		tauto.
	+	rewrite H in IHeq_subs.
		tauto.
	+	destruct IHeq_subs as [Hy Hy'].
		apply eq_term_press in H1 as [Ha Hb].
		split.
		eapply (subs_ext Hy H0 Ha).
		eapply (subs_ext Hy' H0).
		rewrite <- (type_subs_mor _ _ _ _ _ Hy Hy' H H0).
		apply Hb.
	Guarded.

	(* eq_type_press *)
- 	dependent induction H.
	+	now tauto.
	+	now tauto.
	+	split.
		apply (type_subs (subs_id (type_press _ _ H)) H).
		now apply H.
	+	split.
		now apply (type_subs (subs_comp H H0) H1).
		now apply (type_subs H (type_subs H0 H1)).
	+	destruct IHeq_type as [HA HB].
		rewrite H in HA, HB.
		tauto.
	+	pose proof (subs_press _ _ _ H) as [HΔ HΓ].
		split.
		apply (type_subs H).
		all: now apply type_base.
	Guarded.

	(* eq_term_press *)
-	dependent induction H; try (tauto).
	+	split.
		pose proof (term_press _ _ _ H) as [HΓ HA].
		rewrite <- (eq_type_subs_id HA).
		now apply (term_subs (subs_id HΓ) H).
		now apply H.
	+	split.
		now apply (term_subs (subs_comp H H0) H1).
		pose proof (term_press _ _ _ H1) as [HΓ HA].
		rewrite (eq_type_subs_comp H H0 HA).
		now apply (term_subs H),(term_subs H0 H1).
	+	split.
		pose proof (eq_subs_beta H H0 H1).
		pose proof (subs_ext H H0 H1) as Hext.
		rewrite <- (type_subs_mor _ _ _ _ _ (subs_comp Hext (subs_weak H0)) H H2 H0).
		rewrite (eq_type_subs_comp Hext (subs_weak H0) H0).
		apply (term_subs Hext).
		apply (term_qar H0).
		apply H1.
	+	now rewrite H in IHeq_term.
	+	now rewrite H in IHeq_term.
	Guarded.

	(* subs_press *)
-	dependent induction H; try (tauto).
	apply type_press in H as HΓ.
	split; [now apply ctx_ext | now assumption].
	destruct IHSubsJG as [HΔ HΓ].
	split; [now assumption | now apply ctx_ext].
	(* bang *)
	split; [now apply H | now apply ctx_one].
	now apply eq_ctx_press in H.
	now apply eq_ctx_press in H.
	Guarded.

	(* type_press *)
-	dependent induction H; try (tauto).
	now apply subs_press in H.
	now apply eq_ctx_press in H. (* rec *)
	Guarded.

	(* term_press *)
-	dependent induction H; try (tauto).
	apply type_press in H as HΓ.
	split; [now apply ctx_ext | now apply (type_subs (subs_weak H))].
	destruct IHTermJG as [HΓ HA].
	apply (type_subs H) in HA.
	apply subs_press in H as [HΔ HΓ'].
	now tauto.
	destruct IHTermJG as [_ HA].
	rewrite H in HA.
	apply eq_ctx_press in H as [HΔ HΓ].
	now tauto.
	destruct IHTermJG as [HΓ _].
	apply eq_type_press in H as [HA HB].
	now tauto.
	Guarded.

-  (* type_subs_mor *)
	dependent induction HA generalizing Δ y y' Hy Hy' HeqY.
	+	rewrite (eq_type_base Hy').
		apply (eq_type_base Hy).
	+	rewrite <- (eq_type_subs_comp Hy H HA).
		rewrite <- (eq_type_subs_comp Hy' H HA).
		apply IHHA.
		apply (subs_comp Hy H).
		apply (subs_comp Hy' H).
		admit.
	+	apply IHHA; now rewrite H.
	Guarded.
	(* subs_comp_mor_l *)

-	dependent induction Hy0 generalizing Δ y1 y1' HeqY1.
	-	admit.
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite (eq_subs_id_left Hy1).
		now rewrite (eq_subs_id_left Hy1').
	-  specialize (IHHy0_1 _ _ _ HeqY1).
		specialize (IHHy0_2 _ _ _ IHHy0_1).
		pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite <- (eq_subs_comp_assoc Hy1 Hy0_1 Hy0_2).
		now rewrite <- (eq_subs_comp_assoc Hy1' Hy0_1 Hy0_2).
	-	admit.
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite <- (eq_subs_bang (subs_comp Hy1 (subs_bang H))).
		apply (eq_subs_bang (subs_comp Hy1' (subs_bang H))).
	-	apply IHHy0.
		now rewrite H.
	-	rewrite <- H.
		now apply IHHy0.
Qed.

Lemma term_press {Γ : preCtx} {A : preType} {a : preTerm} (H: [ Γ ⊢ a @ A ]) :
	[ ⊢ Γ cx ] /\ [ Γ ⊢ A type ].
Proof.
	dependent induction H; try (tauto).
		apply type_press in H as HΓ.
		split; [now apply ctx_ext | now apply (type_subs (subs_weak H))].
		destruct IHTermJG as [HΓ HA].
		apply (type_subs H) in HA.
		apply subs_press in H as [HΔ HΓ'].
		now tauto.
		destruct IHTermJG as [_ HA].
		rewrite H in HA.
		apply eq_ctx_press in H as [HΔ HΓ].
		now tauto.
		destruct IHTermJG as [HΓ _].
		apply eq_type_press in H as [HA HB].
		now tauto.
Qed.

Add Parametric Morphism Γ : (pctx_ext Γ)
	with signature eq_type Γ ==> eq_ctx
as ctx_ext_mor_T.
Proof.
	intros A B H.
	apply eq_ctx_ext.
	apply (eq_type_press) in H as [HA HB].
	apply eq_ctx_refl, (type_press HA).
	apply H.
Qed.

Lemma eq_term_press {Γ : preCtx} {A : preType} {a b : preTerm} (H: [ Γ ⊢ a == b @ A ]) :
	[ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
	dependent induction H; try (tauto).
	- split.
		pose proof (term_press H) as [HΓ HA].
		rewrite <- (eq_type_subs_id HA).
		now apply (term_subs (subs_id HΓ) H).
		now apply H.
	- split.
		now apply (term_subs (subs_comp H H0) H1).
		pose proof (term_press H1) as [HΓ HA].
		rewrite (eq_type_subs_comp H H0 HA).
		now apply (term_subs H),(term_subs H0 H1).
	- split.
		enough ([ Δ ⊢ A [y] == A [p][y#a] type ]).
		rewrite H2.
		apply (term_subs (subs_ext H H0 H1)).
		apply (term_qar H0).
		+	rewrite <- (eq_type_subs_comp (subs_ext H H0 H1) (subs_weak H0) H0).
			dependent induction H0 generalizing Δ y a H.
			* rewrite (eq_type_base (subs_comp (subs_ext H (type_base H0) H1) (subs_weak (type_base H0)))).
				apply (eq_type_base H).
			* admit.
			* admit.
		+ apply H1.
	- now rewrite H in IHeq_term.
	- now rewrite H in IHeq_term.
Abort.

Lemma type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y == y' ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ].
Proof.
	intros HeqY HA.
	dependent induction HA generalizing Δ y y' HeqY.
	pose proof (eq_subs_press HeqY) as [Hy Hy'].
	rewrite (eq_type_base Hy').
 	apply (eq_type_base Hy).
	pose proof (eq_subs_press HeqY) as [Hy Hy'].
	rewrite <- (eq_type_subs_comp Hy H HA).
	rewrite <- (eq_type_subs_comp Hy' H HA).
	apply IHHA. admit.
	apply IHHA. now rewrite H.
Abort.

Lemma subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ].
Proof.
	dependent induction Hy0 generalizing Δ y1 y1' HeqY1.
	-	admit.
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite (eq_subs_id_left Hy1).
		now rewrite (eq_subs_id_left Hy1').
	-  specialize (IHHy0_1 _ _ _ HeqY1).
		specialize (IHHy0_2 _ _ _ IHHy0_1).
		pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite <- (eq_subs_comp_assoc Hy1 Hy0_1 Hy0_2).
		now rewrite <- (eq_subs_comp_assoc Hy1' Hy0_1 Hy0_2).
	-	admit.
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite <- (eq_subs_bang (subs_comp Hy1 (subs_bang H))).
		apply (eq_subs_bang (subs_comp Hy1' (subs_bang H))).
	-	apply IHHy0.
		now rewrite H.
	-	rewrite <- H.
		now apply IHHy0.
Abort.

Lemma subs_ext_mor_T {Δ Γ : preCtx} {y : preSubs} {A : preType} {a b : preTerm} :
	[ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ a == b @ A ] ->
	[ Δ ⊢ y # a[y] == y # b[y] ~ Γ # A ].
Proof.
	intros Hy HA Hab.
	dependent induction Hab generalizing Δ y Hy HA.
	-	symmetry. now apply IHHab.
	-	transitivity (y # b[y])%subs.
		now apply IHHab1.
		now apply IHHab2.
	-	admit.
	-	admit.
	-	admit.
	-	rewrite <- H in HA.
		rewrite <- (eq_ctx_ext H (eq_type_refl HA)).
		apply IHHab.
		now rewrite H.
		apply HA.
	-	pose proof (type_press HA) as HΓ.
		rewrite <- (eq_ctx_ext (eq_ctx_refl HΓ) H).
		apply IHHab.
		now apply Hy.
		now apply (eq_type_press H).
Abort.


Theorem substitution_extensionality {Δ Γ : preCtx} {y y' : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y' ~ Γ ] ->
	(forall (A : preType), [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ]) ->
	(forall (A : preType) (a : preTerm), [ Γ ⊢ a @ A] -> [ Δ ⊢ a [y] == a [y'] @ A [y]]) ->
	[ Δ ⊢ y == y' ~ Γ ].
Proof.
	-	intros Hy Hy' IHA IHa.
		dependent induction Γ generalizing Δ.
		+	rewrite <- (eq_subs_bang Hy).
			now apply (eq_subs_bang Hy').
		+	pose proof (subs_press Hy) as [HΔ HΓA].
			inversion HΓA; subst.
			(* rewrite (eq_subs_eta H2 Hy). *)
			(* rewrite (eq_subs_eta H2 Hy'). *)
			enough (
				[ Δ ⊢ p ∘ y == p ∘ y' ~ Γ ] -> [ Δ ⊢ q [y] == q [y'] @ A [p] [y] ] ->
				[ Δ ⊢ y == y' ~ Γ # A ]) as Hmor.
			*	apply Hmor.
				apply IHΓ.
				now apply (subs_comp Hy (subs_weak H2)).
				now apply (subs_comp Hy' (subs_weak H2)).
				intros A0 HA0.
				rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
				rewrite (eq_type_subs_comp Hy' (subs_weak H2) HA0).
				apply IHA.
				now apply (type_subs (subs_weak H2) HA0).
				intros A0 a Ha.
				pose proof (term_press Ha) as [_ HA0].
				rewrite (eq_term_subs_comp Hy (subs_weak H2) Ha).
				rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
				transitivity (a [p] [y'])%term.
				apply IHa.
				apply (term_subs (subs_weak H2) Ha).
				symmetry.
				rewrite (IHA _ (type_subs (subs_weak H2) HA0)).
				rewrite <- (eq_type_subs_comp Hy' (subs_weak H2) HA0).
				now apply (eq_term_subs_comp Hy' (subs_weak H2) Ha).
				apply IHa.
				now apply (term_qar H2).

			* (* Extension *)
			intros Hpy Hq.
			dependent induction Hpy generalizing A H2 Hy Hy' IHA IHa HΓA.
Abort.

Theorem substitution_extensionality {Δ Γ : preCtx} {y y' : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y' ~ Γ ] ->
	(forall (A : preType), [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ]) ->
	(forall (A : preType) (a : preTerm), [ Γ ⊢ a @ A] -> [ Δ ⊢ a [y] == a [y'] @ A [y]]) ->
	[ Δ ⊢ y == y' ~ Γ ]
with subs_ext_mor' {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y ~ Γ # A ] -> [ Δ ⊢ y' ~ Γ # A ] ->
	[ Δ ⊢ p ∘ y == p ∘ y' ~ Γ ] -> [ Δ ⊢ q [y] == q [y'] @ A [p] [y] ] ->
	[ Δ ⊢ y == y' ~ Γ # A ].
Proof.
	-	intros Hy Hy' IHA IHa.
		dependent induction Γ generalizing Δ.
		+	rewrite <- (eq_subs_bang Hy).
			now apply (eq_subs_bang Hy').
		+	pose proof (subs_press Hy) as [HΔ HΓA].
			inversion HΓA; subst.
			pose proof (subs_comp Hy (subs_weak H2)) as Hpy.
			pose proof (subs_comp Hy' (subs_weak H2)) as Hpy'.
			Guarded.
			apply (subs_ext_mor' _ _ _ _ _ Hy Hy').
			Guarded.
			apply (IHΓ _ _ _ Hpy Hpy').
			intros A0 HA0.
			rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
			rewrite (eq_type_subs_comp Hy' (subs_weak H2) HA0).
			apply IHA.
			now apply (type_subs (subs_weak H2) HA0).
			intros A0 a Ha.
			pose proof (term_press Ha) as [_ HA0].
			rewrite (eq_term_subs_comp Hy (subs_weak H2) Ha).
			rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
			transitivity (a [p] [y'])%term.
			apply IHa.
			apply (term_subs (subs_weak H2) Ha).
			symmetry.
			rewrite (IHA _ (type_subs (subs_weak H2) HA0)).
			rewrite <- (eq_type_subs_comp Hy' (subs_weak H2) HA0).
			now apply (eq_term_subs_comp Hy' (subs_weak H2) Ha).
			apply IHa.
			now apply (term_qar H2).

	- intros Hy Hy' Heq Hq.
		dependent induction Heq.
		symmetry.
		apply (IHHeq _ _ Hy' Hy eq_refl eq_refl).
		admit. (* req. type_subs_mor *)
		+ admit.
		+  admit. (* req. type_subs_mor *)
Abort.

Theorem substitution_extensionality {Δ Γ : preCtx} {y y' : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y' ~ Γ ] ->
	(forall (A : preType), [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ]) ->
	(forall (A : preType) (a : preTerm), [ Γ ⊢ a @ A] -> [ Δ ⊢ a [y] == a [y'] @ A [y]]) ->
	[ Δ ⊢ y == y' ~ Γ ].
Proof.
-	intros Hy Hy' IHA IHa.
	dependent induction Γ generalizing Δ.
	+	rewrite <- (eq_subs_bang Hy).
		now apply (eq_subs_bang Hy').
	+	pose proof (subs_press Hy) as [HΔ HΓA].
		inversion HΓA; subst.
		clear HΓA.
		assert ([ Δ ⊢ p ∘ y == p ∘ y' ~ Γ ]) as Hpy.
		apply IHΓ.
			apply (subs_comp Hy (subs_weak H2)).
			apply (subs_comp Hy' (subs_weak H2)).
			intros A0 HA0.
			rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
			rewrite (eq_type_subs_comp Hy' (subs_weak H2) HA0).
			apply IHA.
			now apply (type_subs (subs_weak H2) HA0).
			intros A0 a Ha.
			pose proof (term_press Ha) as [_ HA0].
			rewrite (eq_term_subs_comp Hy (subs_weak H2) Ha).
			rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
			transitivity (a [p] [y'])%term.
			apply IHa.
			apply (term_subs (subs_weak H2) Ha).
			symmetry.
			rewrite (IHA _ (type_subs (subs_weak H2) HA0)).
			rewrite <- (eq_type_subs_comp Hy' (subs_weak H2) HA0).
			now apply (eq_term_subs_comp Hy' (subs_weak H2) Ha).

		dependent induction Hpy generalizing A IHΓ y y' Hy Hy' IHA IHa HΔ H1 H2.
			* symmetry.
			apply (IHHpy _ IHΓ _ _ Hy' Hy).
			intros A0 HA0. symmetry. now apply IHA.
			intros A0 a Ha.  admit. (* req. type_subs_mor *)
			exact HΔ.
			exact H1.
			exact H2.
			reflexivity.
			reflexivity.
			* admit. (*equality issue *)
			* admit. (* inversion a ? *)
			* rewrite <- H in Hy, Hy' |- *.
				pose proof (eq_ctx_press H) as [HΔ' HΓ].
				apply IHHpy; try tauto.
				intros A0 HA0. rewrite H. now apply IHA.
				intros A0 a Ha. rewrite H. now apply IHa.
			*	symmetry in H.
				pose proof (eq_ctx_ext H (eq_type_refl H2)) as HΓA.
				pose proof (eq_ctx_press H) as [_ HΓ].
				rewrite H in H2.
				rewrite HΓA in Hy, Hy' |- *.
				apply IHHpy; try tauto.
				intros Δ0 y0 y0' Hy0 Hy0' IHA0 IHa0.
				rewrite <- H in Hy0, Hy0' |- *.
				apply IHΓ; try tauto.
				intros A0 HA0. apply IHA0. now rewrite <- H.
				intros A0 a Ha. apply IHa0. now rewrite <- H	.
				intros A0 HA0. apply IHA. now rewrite HΓA.
				intros A0 a Ha. apply IHa. now rewrite HΓA.
Abort.

Lemma subs_ext_ext {Δ Γ : preCtx} {A : preType} {y y' : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y' ~ Γ ] ->
	[ Δ ⊢ p ∘ y == p ∘ y' ~ Γ ] -> [ Δ ⊢ q [y] == q [y'] @ A [p] [y] ] ->
	[ Δ ⊢ y == y' ~ Γ # A ].
Proof.
	intros Hy Hy' Hpy Hq.
	dependent induction Hpy generalizing A y y' Hy Hy'.
	- symmetry.
		apply IHHpy; try tauto.
		admit. (* req. type_subs_mor *)
	- admit.
Abort.


Lemma subs_ext_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a b : preTerm}:
	[ Δ ⊢ y == y' ~ Γ ] -> [ Δ ⊢ a == b @ A[y] ] ->
	[ Δ ⊢ y # a == y' # b ~ Γ # A ].
	intros HeqY HeqAB.
	dependent induction HeqY generalizing A a b.
	-	symmetry. apply IHHeqY. admit.
	-	transitivity (y2 # a)%subs.
		apply IHHeqY1. now rewrite HeqAB at 2.
		apply IHHeqY2. admit.
	- admit.
Abort.

Lemma subs_ext_mor_S {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a : preTerm}:
	[ Δ ⊢ y == y' ~ Γ ] -> [ Δ ⊢ a @ A [y] ] ->
	[ Δ ⊢ y # a == y' # a ~ Γ # A ].
Proof.
	intros HeqY Ha.
	dependent induction Ha generalizing Γ y y' A HeqY.
	- admit.
	-
	- dependent induction HeqY generalizing y' HeqY.
		+	symmetry. apply IHHeqY. now apply Ha.
		+	transitivity (y2 # a)%subs.
			apply IHHeqY1. now apply Ha.
			apply IHHeqY2. now apply Ha.
		+	admit.

Lemma subs_ext_mor_T {Δ Γ : preCtx} {y  : preSubs} {A : preType} {a b : preTerm}:
	[ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a == b @ A ] ->
	[ Δ ⊢ y # a [y] == y # b [y] ~ Γ # A ].
Proof.
	intros Hy Heqa.
	dependent induction Heqa generalizing Δ y Hy.
	-	symmetry. now apply IHHeqa.
	-	transitivity (y # b [y])%subs.
		now apply IHHeqa1.
		now apply IHHeqa2.
	-	admit.
	-
		rewrite (eq_type_subs_comp Hy (subs_weak HΓ) HA).
		rewrite (eq_term_subs_comp Hy (subs_weak HΓ) H).
		apply (eq_term_subs_comp (subs_ext Hy HΓ H) (subs_weak HΓ) H).


Lemma subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ].
Proof.
	dependent induction Θ generalizing Δ Γ.
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite <- (eq_subs_bang (subs_comp Hy1 Hy0)).
		now apply eq_subs_bang, (subs_comp Hy1' Hy0).
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		dependent induction Hy0 generalizing Δ y1 y1' HeqY1.
		apply (eq_subs_comp_assoc Hy0 HeqY1 (subs_id H)).
Qed.

Lemma type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y == y' ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ].
Proof.
	intros HeqY HA.
	dependent induction HA generalizing Δ y y' HeqY.
	pose proof (eq_subs_press HeqY) as [Hy Hy'].
	rewrite (eq_type_base Hy').
 	apply (eq_type_base Hy).
	pose proof (eq_subs_press HeqY) as [Hy Hy'].
	rewrite <- (eq_type_subs_comp Hy H HA).
	rewrite <- (eq_type_subs_comp Hy' H HA).
	apply IHHA. admit.
	apply IHHA. now rewrite H.
Admitted.

Lemma type_eq_subs_beta {Δ Γ : preCtx} {y : preSubs} {A : preType} {a : preTerm} :
	[ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [Δ ⊢ a @ A [y] ] -> [ Δ ⊢ A[p ∘ y # a] == A[y] type ].
Proof.
	intros Hy HA Ha.
	dependent induction HA generalizing Δ y a Hy; try (tauto).
	pose proof (type_base H) as Hb.
	rewrite (eq_type_base Hy).
	apply (eq_type_base (subs_comp (subs_ext Hy Hb Ha) (subs_weak Hb))).


Theorem eq_term_press {Γ : preCtx} {A : preType} {a b : preTerm} (Heq: [ Γ ⊢ a == b @ A ]) :
	[ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
	dependent induction Heq; try (tauto).
	-	pose proof (term_press H) as [HΓ HA].
		split.
			rewrite <- (eq_type_subs_id HA).
			now apply (term_subs (subs_id HΓ) H).
			now apply H.
	-	split.
			now apply (term_subs (subs_comp H H0)).
			rewrite (eq_type_subs_comp H H0 (proj2 (term_press H1))).
			now apply (term_subs H), (term_subs H0 H1).
	-	split. 2:assumption.
		pose proof (term_qar H0) as Hq.
		apply (term_subs (subs_ext H H0 H1)) in Hq.
		enough ([ Δ ⊢ A [p] [y#a] == A [y] type ]) as Hsub.
		now rewrite Hsub in Hq.
		dependent induction H0 generalizing Δ y a H.


	-	now rewrite H in IHHeq.
	-	now rewrite H in IHHeq.




Add Morphism CtxJG
	with signature eq_ctx ==> iff
as ctx_mor.
Proof.
	intros Γ Δ Hctx.
	now apply eq_ctx_press in Hctx.
Qed.

Add Parametric Morphism Δ Γ : (SubsJG Δ Γ)
	with signature eq_subs Δ Γ ==> iff
as subs_mor.
Proof.
	intros y y' Heq.
	now apply eq_subs_press in Heq.
Qed.

Add Parametric Morphism Γ : (TypeJG Γ)
	with signature (eq_type Γ) ==> iff
as type_mor.
Proof.
	intros A B Hty.
	now apply eq_type_press in Hty.
Qed.

(* Add Parametric Morphism Γ A : (TermJG Γ A)
	with signature (eq_term Γ A) ==> iff
as term_mor.
Proof.
	intros a b Heq.
	now apply eq_term_press in Heq.
Qed. *)

(** End Pressuposition lemma **)

(* Lemma subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' : preSubs} {y0 : preSubs}
	(HeqY1 : [ Δ ⊢ y1 == y1' ~ Γ ]) (Hy0 : [ Γ ⊢ y0 ~ Θ ]) :
	[ Δ ⊢ (y0 ∘ y1) == (y0 ∘ y1') ~ Θ ].
Proof.
	dependent induction Hy0 generalizing Δ y1 y1' HeqY1.
	-	dependent induction HeqY1.
		+ specialize (IHHeqY1 _ _ H eq_refl).
			now symmetry.
		+	specialize (IHHeqY1_1 _ _ H eq_refl).
			specialize (IHHeqY1_2 _ _ H eq_refl).
			now transitivity (p ∘ y2)%subs.
		+	admit.
		+	pose proof (subs_press H0) as [HΔ HΓA].
			rewrite (eq_subs_comp_assoc (subs_id HΔ) H0 (subs_weak H)).
			apply eq_subs_id_right.
			apply (subs_comp H0), (subs_weak H).
		+	pose proof (subs_weak H) as Hp.
			rewrite (eq_subs_comp_assoc H2 (subs_comp H0 H1) Hp).
			rewrite (eq_subs_comp_assoc (subs_comp H2 H0) H1 Hp).
			admit.
		+ admit.
		+ rewrite (eq_subs_beta (subs_comp H0 (subs_weak H1)) H).
			apply eq_subs_refl, (subs_comp H0 (subs_weak H1)).

	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite (eq_subs_id_left Hy1).
		now rewrite (eq_subs_id_left Hy1').
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		rewrite <- (eq_subs_comp_assoc Hy1 Hy0_1 Hy0_2).
		rewrite <- (eq_subs_comp_assoc Hy1' Hy0_1 Hy0_2).
		apply IHHy0_2.
		now apply IHHy0_1.
	-	admit.
	-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
		transitivity (!)%subs. symmetry.
		apply eq_subs_bang, (subs_comp (Hy1)), (subs_bang H).
		apply eq_subs_bang, (subs_comp (Hy1')), (subs_bang H).
	-	apply IHHy0.
		now rewrite H.
	-	rewrite <- H.
		now apply IHHy0. *)

Lemma type_subs_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} :
	[ Δ ⊢ y == y' ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ].
Proof.
	intros HeqY HA.
	dependent induction HA generalizing Δ y y' HeqY.
	pose proof (eq_subs_press HeqY) as [Hy Hy'].
	rewrite (eq_type_base Hy').
 	apply (eq_type_base Hy).
	pose proof (eq_subs_press HeqY) as [Hy Hy'].
	rewrite <- (eq_type_subs_comp Hy H HA).
	rewrite <- (eq_type_subs_comp Hy' H HA).
	apply IHHA.
	apply IHHA. now rewrite H.
Qed.

Lemma substitution_extensionality {Δ Γ : preCtx} {y y' : preSubs} :
	[ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y' ~ Γ ] ->
	(forall (A : preType), [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[y'] type ]) ->
	(forall (A : preType) (a : preTerm), [ Γ ⊢ a @ A] -> [ Δ ⊢ a [y] == a [y'] @ A [y]]) ->
	[ Δ ⊢ y == y' ~ Γ ].
Proof.
	-	intros Hy Hy' IHA IHa.
		dependent induction Γ generalizing Δ.
		+	transitivity (!)%subs. symmetry.
			now apply (eq_subs_bang Hy).
			now apply (eq_subs_bang Hy').
		+	pose proof (subs_press Hy) as [HΔ HΓA].
			inversion HΓA; subst.
			pose proof (subs_comp Hy (subs_weak H2)) as Hpy.
			pose proof (subs_comp Hy' (subs_weak H2)) as Hpy'.
			rewrite (eq_subs_eta H2 Hy).
			rewrite (eq_subs_eta H2 Hy').
			Guarded.
			apply subs_ext_mor.
			Guarded.
			apply (IHΓ _ _ _ Hpy Hpy').
			intros A0 HA0.
			rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
			rewrite (eq_type_subs_comp Hy' (subs_weak H2) HA0).
			apply IHA.
			now apply (type_subs (subs_weak H2) HA0).
			intros A0 a Ha.
			pose proof (term_press Ha) as [_ HA0].
			rewrite (eq_term_subs_comp Hy (subs_weak H2) Ha).
			rewrite (eq_type_subs_comp Hy (subs_weak H2) HA0).
			transitivity (a [p] [y'])%term.
			apply IHa.
			apply (term_subs (subs_weak H2) Ha).
			symmetry.
			rewrite (IHA _ (type_subs (subs_weak H2) HA0)).
			rewrite <- (eq_type_subs_comp Hy' (subs_weak H2) HA0).
			now apply (eq_term_subs_comp Hy' (subs_weak H2) Ha).
			now apply H2.
			rewrite (eq_type_subs_comp Hy (subs_weak H2) H2).
			apply IHa.
			now apply (term_qar H2).
Qed.

(******************************************************************************)
(** Operator are morphism **)
Lemma subs_comp_mor_r {Δ Γ Θ : preCtx} {y1 y0 y0' : preSubs}
	(Hy1 : [ Γ ⊢ y1 ~ Θ ]) (HeqY0 : [ Δ ⊢ y0 == y0' ~ Γ ]) :
	[ Δ ⊢ (y1 ∘ y0) == (y1 ∘ y0') ~ Θ ].
Proof.
	pose proof (eq_subs_press HeqY0) as [Hy0 Hy0'].
	apply substitution_extensionality.
	now apply (subs_comp Hy0 Hy1).
	now apply (subs_comp Hy0' Hy1).
	intros A0 HA0.
	rewrite (eq_type_subs_comp Hy0 Hy1 HA0).
	rewrite (eq_type_subs_comp Hy0' Hy1 HA0).
	apply (eq_type_subs_mor HeqY0).
	now apply (type_subs Hy1 HA0).
	intros A0 a Ha.
	pose proof (term_press Ha) as [_ HA0].
	rewrite (eq_term_subs_comp Hy0 Hy1 Ha).
	rewrite (eq_type_subs_comp Hy0 Hy1 HA0).
	transitivity (a [y1] [y0'])%term.
	apply (eq_term_subs_mor HeqY0).
	apply (term_subs Hy1 Ha).
	symmetry.
	rewrite (eq_type_subs_mor HeqY0 (type_subs Hy1 HA0)).
	rewrite <- (eq_type_subs_comp Hy0' Hy1 HA0).
	now apply (eq_term_subs_comp Hy0' Hy1 Ha).
Qed.

Lemma type_subs_mor_S {Δ Γ : preCtx} {y y' : preSubs} {A : preType}
	(HeqY : [ Δ ⊢ y == y' ~ Γ ]) (HeqA : [ Γ ⊢ A type ]) :
	[ Δ ⊢ A[y] == A [y'] type ].
Proof.
	dependent induction HeqY generalizing A.
	- specialize (IHHeqY _ HeqA).
		now symmetry.
	- specialize (IHHeqY1 _ HeqA).
		specialize (IHHeqY2 _ HeqA).
		now transitivity (A [y2])%ty.
	- admit.
	- rewrite (eq_type_subs_comp (subs_id (proj1 (subs_press H))) H HeqA).
		symmetry.
		apply (eq_type_subs_id (type_subs H HeqA)).
	- admit.
	- admit.
	- admit.
	- admit.




Lemma subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' y0 : preSubs}
	(HeqY1 : [ Γ ⊢ y1 == y1' ~ Θ ]) (Hy0 : [ Δ ⊢ y0 ~ Γ ]) :
	[ Δ ⊢ (y1 ∘ y0) == (y1' ∘ y0) ~ Θ ].
Proof.
	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
	apply substitution_extensionality.
	now apply (subs_comp Hy0 Hy1).
	now apply (subs_comp Hy0 Hy1').
	intros A0 HA0.
	rewrite (eq_type_subs_comp Hy0 Hy1 HA0).
	rewrite (eq_type_subs_comp Hy0 Hy1' HA0).
	apply (eq_type_subs_mor HeqY1).
	now apply (type_subs Hy0 HA0).
	intros A0 a Ha.
	pose proof (term_press Ha) as [_ HA0].
	rewrite (eq_term_subs_comp Hy0 Hy1 Ha).
	rewrite (eq_type_subs_comp Hy0 Hy1 HA0).
	transitivity (a [y1'] [y0])%term.
	apply (eq_term_subs_mor HeqY1).
	apply (term_subs Hy0 Ha).
	symmetry.
	rewrite (eq_type_subs_mor HeqY1 (type_subs Hy0 HA0)).
	rewrite <- (eq_type_subs_comp Hy0 Hy1' HA0).
	now apply (eq_term_subs_comp Hy0 Hy1' Ha).
(* Lemma aux  {Δ Γ Θ : preCtx} {y d : preSubs} {A : preType} {a : preTerm}
	(Hd : [ Δ ⊢ d ~ Γ ]) (Hy : [ Γ ⊢ y ~ Θ ]) (HA : [ Θ ⊢ A type ]) (Ha : [ Γ ⊢ a @ A[y] ]) :
	[Δ ⊢ (p ∘ y # a) ∘ d == y ∘ d ~ Θ].
Proof.
	dependent induction y; try (tauto). *)

Lemma eq_term_subs_mor_T {Δ Γ : preCtx} {y : preSubs} {A : preType} {a b : preTerm}
	(Hy : [ Δ ⊢ y ~ Γ ]) (Ha : [ Γ ⊢ a == b @ A ]) :
	[ Δ ⊢ a [y] == b [y] @ A[y] ]
with eq_type_subs_mor_T {Δ Γ : preCtx} {y : preSubs} {A B : preType}
	(Hy : [ Δ ⊢ y ~ Γ ]) (HA : [ Γ ⊢ A == B type ]) :
	[ Δ ⊢ A [y] == B [y] type ]
with subs_comp_mor_l {Δ Γ Θ : preCtx} {y1 y1' y0 : preSubs}
	(HeqY1 : [ Γ ⊢ y1 == y1' ~ Θ ]) (Hy0 : [ Δ ⊢ y0 ~ Γ ]) :
		[ Δ ⊢ (y1 ∘ y0) == (y1' ∘ y0) ~ Θ ]
with subs_ext_dist {Δ Γ Θ : preCtx} {y d : preSubs} {A : preType} {a : preTerm}
	(Hd : [ Δ ⊢ d ~ Γ ]) (Hy : [ Γ ⊢ y ~ Θ ]) (HA : [ Θ ⊢ A type ]) (Ha : [ Γ ⊢ a @ A[y] ]) :
	[ Δ ⊢ y # a ∘ d == (y ∘ d) # a [d] ~ Θ # A ]
.	Proof.
	(* eq_term_subs_mor_T *)
-	dependent induction Ha generalizing Δ y Hy.
	+	specialize (IHHa _ _ Hy).
		now symmetry.
	+	specialize (IHHa1 _ _ Hy).
		specialize (IHHa2 _ _ Hy).
		now transitivity (b [y])%term.
	+	rewrite <- (eq_type_subs_mor (eq_subs_id_left Hy) (proj2 (term_press H))).
		rewrite <- (eq_term_subs_comp Hy (subs_id (proj1 (term_press H))) H).
		now apply (eq_term_subs_mor (eq_subs_id_left Hy) H).
	+	rewrite <- (eq_type_subs_comp Hy (subs_comp H H0) (proj2 (term_press H1))).
		rewrite <- (eq_term_subs_comp Hy (subs_comp H H0) H1).
		pose proof (eq_term_subs_comp Hy H (term_subs H0 H1)).
		rewrite <- (eq_type_subs_comp (subs_comp Hy H) H0 (proj2 (term_press H1))) in H2.
		rewrite <- (eq_term_subs_comp (subs_comp Hy H) H0 H1) in H2.
		rewrite (eq_type_subs_mor (eq_subs_comp_assoc Hy H H0) (proj2 (term_press H1))) in H2.
		rewrite <- H2.
		pose proof (eq_subs_comp_assoc Hy H H0).
		symmetry in H3.
		apply (eq_term_subs_mor H3 H1).
	+	pose proof (proj2 (term_press H0)) as HA'.
		pose proof (eq_subs_press H) as [Hy0 Hy1].
		rewrite <- (eq_type_subs_comp Hy Hy0 HA').
		rewrite <- (eq_term_subs_comp Hy Hy0 H0).
		pose proof (eq_term_subs_comp Hy Hy1 H0).
		pose proof (subs_comp_mor_l _ _ _ _ _ _ H Hy).
		rewrite <- (eq_type_subs_mor H2 HA') in H1.
		rewrite <- H1.
		apply (eq_term_subs_mor H2 H0).
		(* Guarded. *)
	+	apply (term_subs Hy) in H1 as Hay.
		rewrite <- (eq_type_subs_comp Hy H H0) in Hay |- *.
		pose proof (subs_ext_dist _ _ _ _ _ _ _ Hy H H0 H1).
		apply (subs_comp_mor_r (subs_weak H0)) in H2 as H3.
		rewrite (eq_subs_beta (subs_comp Hy H) H0 Hay) in H3.
		rewrite <- (eq_term_beta_qar (subs_comp Hy H) H0 Hay).
		rewrite <- (eq_type_subs_mor H3 H0).
		rewrite (eq_type_subs_comp (subs_comp Hy (subs_ext H H0 H1)) (subs_weak H0) H0).
		rewrite <- (eq_term_subs_comp Hy (subs_ext H H0 H1) (term_qar H0)).
		apply (eq_term_subs_mor H2 (term_qar H0)).
		(* Guarded. *)
	+	apply IHHa.
		now rewrite H.
	+	specialize (IHHa _ _ Hy).
		now rewrite (eq_type_subs_mor_T _ _ _ _ _ Hy H) in IHHa.
		Guarded.

(* eq_type_subs_mor_T *)
- dependent induction HA generalizing Δ y Hy.
	+	specialize (IHHA _ _ Hy).
		now symmetry.
	+	specialize (IHHA1 _ _ Hy).
		specialize (IHHA2 _ _ Hy).
		now transitivity (B [y])%ty.
	+	rewrite <- (eq_type_subs_comp Hy (subs_id (type_press H)) H).
		now apply (eq_type_subs_mor (eq_subs_id_left Hy) H).
	+	rewrite <- (eq_type_subs_comp Hy (subs_comp H H0) H1).
		rewrite <- (eq_type_subs_comp Hy H (type_subs H0 H1)).
		rewrite <- (eq_type_subs_comp (subs_comp Hy H) H0 H1).
		symmetry.
		now apply (eq_type_subs_mor (eq_subs_comp_assoc Hy H H0) H1).
	+	pose proof (eq_subs_press H) as [Hy0 Hy1].
		rewrite <- (eq_type_subs_comp Hy Hy0 H0).
		rewrite <- (eq_type_subs_comp Hy Hy1 H0).
		now apply (eq_type_subs_mor (subs_comp_mor_l _ _ _ _ _ _ H Hy) H0).
	+	apply IHHA.
		now rewrite H.
		(* Guarded. *)

	(* subs_comp_mor_l *)
-	pose proof (eq_subs_press HeqY1) as [Hy1 Hy1'].
	apply substitution_extensionality.
	now apply (subs_comp Hy0 Hy1).
	now apply (subs_comp Hy0 Hy1').
	intros A HA.
	rewrite (eq_type_subs_comp Hy0 Hy1 HA).
	rewrite (eq_type_subs_comp Hy0 Hy1' HA).
	Guarded.
	apply (eq_type_subs_mor_T _ _ _ _ _ Hy0).
	Guarded.
	apply (eq_type_subs_mor HeqY1).
	Guarded.
	(* subs_comp_mor_l *)
-	dependent induction Hy1 generalizing Δ y0.
	+	specialize (IHHy1 _ _ Hy0).
		now symmetry.
	+	specialize (IHHy1_1 _ _ Hy0).
		specialize (IHHy1_2 _ _ Hy0).
		now transitivity (y2 ∘ y0)%subs.
	+	apply subs_press in H as HΓ.
		destruct HΓ as [HΔ HΓ].
		rewrite <- (eq_subs_comp_assoc Hy0 H (subs_id HΓ)).
		apply eq_subs_id_left.
		now apply (subs_comp Hy0 H).
	+	apply subs_press in H as HΓ.
		destruct HΓ as [HΔ HΓ].
		rewrite <- (eq_subs_comp_assoc Hy0 (subs_id HΔ) H).
		apply (subs_comp_mor_r H).
		symmetry.
		now apply (eq_subs_id_left Hy0).
	+	rewrite <- (eq_subs_comp_assoc Hy0 H (subs_comp H0 H1)).
		rewrite <- (eq_subs_comp_assoc Hy0 (subs_comp H H0) H1).
		rewrite <- (eq_subs_comp_assoc (subs_comp Hy0 H) H0 H1).
		(* Guarded. *)
		apply (subs_comp_mor_r H1).
		symmetry.
		now apply (eq_subs_comp_assoc Hy0 H H0).
	+	transitivity (!)%subs. symmetry.
		apply eq_subs_bang.
		apply (subs_comp Hy0).
		now apply (subs_bang (proj1 (subs_press H))).
		apply eq_subs_bang.
		now apply (subs_comp Hy0).
	+	pose proof (subs_ext H H0 H1).
		rewrite <- (eq_subs_comp_assoc Hy0 H2 (subs_weak H0)).
		pose proof (term_subs Hy0 H1).
		rewrite <- (eq_type_subs_comp Hy0 H H0) in H3.
		rewrite <- (eq_subs_beta (subs_comp Hy0 H) H0 H3).
		apply (@subs_comp_mor_r Δ (Γ # A)%ctx Γ p (y # a ∘ y0)%subs ((y ∘ y0)#a[y0])%subs (subs_weak H0)).
		now apply (subs_ext_dist _ _ _ _ _ _ _ Hy0 H H0 H1).
	+	rewrite (eq_subs_eta H (subs_comp Hy0 H0)).
		rewrite (subs_ext_dist _ _ _ _ _ _ _ Hy0 (subs_comp H0 (subs_weak H)) H).
		apply subs_ext_mor.
		apply (eq_subs_comp_assoc Hy0 H0 (subs_weak H)).
		apply H.
		rewrite (eq_type_subs_comp (subs_comp Hy0 H0) (subs_weak H) H).
		apply (eq_term_subs_comp Hy0 H0 (term_qar H)).
		rewrite (eq_type_subs_comp H0 (subs_weak H) H).
		now apply (term_subs H0 (term_qar H)).
	+	rewrite <- H in Hy0.
		now apply IHHy1.
	+	specialize (IHHy1 _ _ Hy0).
		now apply (eq_subs_over_ctx_quot_r H IHHy1).
	+	specialize (IHHy1 _ _ Hy0).
		apply eq_subs_press in Hy1 as Hyy'.
		destruct Hyy' as [Hy Hy'].
		pose proof (eq_term_press H0) as [Ha Hb].
		rewrite (subs_ext_dist _ _ _ _ _ _ _ Hy0 Hy H Ha).
		rewrite (eq_type_subs_mor Hy1 H) in Hb.
		rewrite (subs_ext_dist _ _ _ _ _ _ _ Hy0 Hy' H Hb).
		apply (subs_ext_mor).
		apply IHHy1.
		apply H.
		rewrite (eq_type_subs_comp Hy0 Hy H).
		apply (eq_term_subs_mor_T _ _ _ _ _ _ Hy0 H0).
		(* Guarded. *)


	(* subs_ext_dist *)
-	pose proof (subs_ext Hy HA Ha) as Hya.
	pose proof (subs_comp Hd Hya) as Hyad.
	rewrite (eq_subs_eta HA Hyad).
	apply subs_ext_mor.
	rewrite (eq_subs_comp_assoc Hd Hya (subs_weak HA)).
	Guarded.
	apply (subs_comp_mor_l _ _ _ _ _ _ (eq_subs_beta Hy HA Ha) Hd).
	Guarded.
		symmetry.
		pose proof (eq_subs_beta Hy HA Ha) as Hbeta.
		symmetry in Hbeta.
		(* Guarded. *)
		admit.
		apply HA.
		rewrite (eq_type_subs_comp Hyad (subs_weak HA) HA).
		apply (term_subs Hyad).
		Guarded.
		now apply (term_qar HA).
	+	apply eq_subs_ext_mor_T.
		apply (subs_comp Hd Hy).
		apply HA.
		pose proof (eq_term_subs_comp Hd Hya (term_qar HA)) as Heq.
		pose proof (eq_subs_beta Hy HA Ha) as Hbeta.
		Guarded.
		pose proof (subs_comp_mor_l _ _ _ _ _ _ Hbeta Hd) as Hbeta'.
		Guarded.
		rewrite <- (eq_subs_comp_assoc Hd Hya (subs_weak HA)) in Hbeta'.
		pose proof (eq_type_subs_mor Hbeta' HA) as Hty.
		rewrite (eq_type_subs_comp Hyad (subs_weak HA) HA) in Hty.
		rewrite Hty in Heq.
		rewrite Heq.
		rewrite (eq_type_subs_comp Hd Hy HA).
		apply (eq_term_subs_mor_T _ _ _ _ _ _ Hd).
		apply (eq_term_beta_qar Hy HA Ha).
		Guarded.
Qed.






(** Helpers and derived operators *)



Lemma subs_id_inv {Δ Γ : preCtx}:
	[ Δ ⊢ id ~ Γ ] -> (eq_ctx Δ Γ /\ [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]).
Proof.
	intros H.
	dependent induction H; try (tauto).
	apply eq_ctx_refl in H as HeqΓ.
	now tauto.
	specialize (IHSubsJG eq_refl) as [Heq [HcxΔ HcxΓ]].
	rewrite H in HcxΔ, Heq.
	now tauto.
	specialize (IHSubsJG eq_refl) as [Heq [HcxΔ HcxΓ]].
	rewrite H in HcxΓ, Heq.
	now tauto.
Qed.

Lemma subs_weak_inv {Δ Γ : preCtx} :
	[ Δ ⊢ p ~ Γ ] -> (exists (Δ0 : preCtx) (A : preType),
		Δ = (Δ0 # A)%ctx /\ eq_ctx Δ0 Γ /\ [ Γ ⊢ A type ]).
Proof.
	intros H.
	dependent induction H; try (tauto).
	-	apply type_press in H as HΓ.
		apply eq_ctx_refl in HΓ.
		now exists Γ,A.
	- specialize (IHSubsJG eq_refl) as [Δ0 [A [HeqΔ [HeqΓ HA]]]].
		subst.
		inversion H; subst.
		exists Δ, B.
		split. reflexivity.
		split.
		now rewrite <- H3.
		apply (eq_type_over_ctx_quot HeqΓ) in H5.
		now rewrite <- H5.
	- specialize (IHSubsJG eq_refl) as [Δ0 [A [HeqΔ [HeqΓ HA]]]].
		subst.
		rewrite H in HeqΓ, HA.
		now exists Δ0, A.
Qed.

Lemma subs_comp_inv {Δ Γ : preCtx} {y1 y0 : preSubs}:
	[ Δ ⊢ y1 ∘ y0 ~ Γ ] -> (exists (Γ0 : preCtx), [ Δ ⊢ y0 ~ Γ0 ] /\ [ Γ0 ⊢ y1 ~ Γ ]).
Proof.
	intros H.
	dependent induction H; try (tauto).
	- now exists Γ1.
	- specialize (IHSubsJG y1 y0 eq_refl) as [Γ0 [Hy1 Hy0]].
		apply (subs_over_ctx_quot_l H) in Hy1.
		now exists Γ0.
	- specialize (IHSubsJG y1 y0 eq_refl) as [Γ0 [Hy1 Hy0]].
		apply (subs_over_ctx_quot_r H) in Hy0.
		now exists Γ0.
Qed.

Lemma SubsJG_core_inv : forall Δ Γ : preCtx, forall y : preSubs,
	[ Δ ⊢ y ~ Γ ] -> (
		(exists (Δ0 : preCtx) (A : preType), y = p /\ Δ = (Δ0 # A)%ctx /\ eq_ctx Δ0 Γ /\ [ Γ ⊢ A type ])
   \/ (y = id /\ eq_ctx Δ Γ /\ [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ])
   \/ (exists (Γ0 : preCtx) (y1 y0 : preSubs),
      y = (y0 ∘ y1)%subs /\ [ Δ ⊢ y1 ~ Γ0 ] /\ [ Γ0 ⊢ y0 ~ Γ ])
   \/ (exists (y0 : preSubs) (a0 : preTerm) (Γ0 : preCtx) (A0 : preType),
      y = (y0 # a0)%subs /\ [ Δ ⊢ y0 ~ Γ0 ] /\ [ Γ0 ⊢ A0 type ] /\ [ Δ ⊢ a0 @ A0[y0] ]
	)).
Proof.
	intros Δ Γ y Hy.
	dependent induction Hy.
	- left.
		apply type_press in H as HΓ.
		apply eq_ctx_refl in HΓ.
		now exists Γ, A.
	- right. left. apply eq_ctx_refl in H as HΓ. now tauto.
	- right. right. left. now exists Γ1, y1, y0.
	- right. right. right. now exists y, a, Γ, A.
	- destruct IHHy as [IH | [ IH | [ IH | IH ]]].
		+ left. destruct IH as [Θ [A [HeqY H1]]]. subst.
			apply (subs_over_ctx_quot_l H) in Hy.
			apply subs_weak_inv in Hy.
			destruct Hy as [Θ' [A' [HeqΔ' [HeqΓ' HA']]]].
			now exists Θ', A'.
		+ right. left.
			destruct IH as [HeqY [HeqΓ [HcxΔ HcxΓ]]].
			rewrite H in HcxΔ, HeqΓ.
			now tauto.
		+ right. right. left.
			destruct IH as [Γ0 [y1 [y0 [HeqY [Hy1 Hy0]]]]].
			subst.
			apply (subs_over_ctx_quot_l H) in Hy.
			apply subs_comp_inv in Hy as [Θ [Hy3 Hy4]].
			now exists Θ, y1, y0.
		+ right. right. right.
			destruct IH as [y0 [a0 [Γ0 [A0 [HeqY [Hy0 [Htya0 HA0]]]]]]].
			apply (subs_over_ctx_quot_l H) in Hy0.
			rewrite H in HA0.
			now exists y0, a0, Γ0, A0.
	- destruct IHHy as [IH | [ IH | [ IH | IH ]]].
		+ left. destruct IH as [Θ [A [HeqY H1]]]. subst.
			apply (subs_over_ctx_quot_r H) in Hy.
			apply subs_weak_inv in Hy.
			destruct Hy as [Θ' [A' [HeqΔ' [HeqΓ' HA']]]].
			now exists Θ', A'.
		+ right. left.
			destruct IH as [HeqY [HeqΓ [HcxΔ HcxΓ]]].
			rewrite H in HcxΓ, HeqΓ.
			now tauto.
		+ right. right. left.
			destruct IH as [Γ0 [y1 [y0 [HeqY [Hy1 Hy0]]]]].
			subst.
			apply (subs_over_ctx_quot_r H) in Hy.
			apply subs_comp_inv in Hy as [Θ [Hy3 Hy4]].
			now exists Θ, y1, y0.
		+ right. right. right.
			destruct IH as [y0 [a0 [Γ0 [A0 [HeqY [Hy0 [Htya0 HA0]]]]]]].
			(* apply (subs_over_ctx_quot_r H) in Hy0. *)
			now exists y0, a0, Γ0, A0.
Qed.

Lemma type_subs_inv (Δ : preCtx) (y : preSubs) (A : preType) :
	 [ Δ ⊢ A [y] type ] -> (exists Γ : preCtx, [ Δ ⊢ y ~ Γ ] /\ [ Γ ⊢ A type ]).
Proof.
	intros HA.
	dependent induction HA; try (tauto).
	- now exists Γ.
	- specialize (IHHA y A eq_refl) as [Γ' [Hsubs Hty]].
		apply (subs_over_ctx_quot_l H) in Hsubs.
		now exists Γ'.
Qed.

Lemma TypeJG_core_inv : forall Γ : preCtx, forall A : preType,
	[ Γ ⊢ A type ] -> ((A = b /\ [ ⊢ Γ cx ])
	\/ (exists (Γ0 : preCtx) (y : preSubs) (A0 : preType), A = (A0 [y])%ty /\ [ Γ ⊢ y ~ Γ0 ] /\  [ Γ0 ⊢ A0 type ] )
	).
Proof.
	intros Γ A HA.
	dependent induction HA.
	- left. now split.
	- right. now exists Γ, y, A.
	- destruct IHHA as [H1 | H2].
		+ left. destruct H1 as [Heq Hcx]. subst.
			split. reflexivity. now apply (eq_ctx_press H).
		+ right. destruct H2 as [Γ0 [y0 [A0 [Heq [Hsubs Hty]]]]].
			apply (subs_over_ctx_quot_l H) in Hsubs.
			now exists Γ0, y0, A0.
Qed.


Lemma TypeJG_core_ind : forall P : preCtx -> preType -> Prop,
	(forall Γ : preCtx, [ ⊢ Γ cx ] -> P Γ b) ->
	(forall (Δ Γ : preCtx) (y : preSubs) (A : preType),
		[Δ ⊢ y ~ Γ] -> [Γ ⊢ A type ] -> P Γ A -> P Δ A [y]%ty) ->
	forall (Γ : preCtx) (A : preType), [Γ ⊢ A type ] -> P Γ A.
Proof.
	intros P Hbase Hsubs.
	intros Γ A HA.
	dependent induction A generalizing Γ; try (tauto).
		apply Hbase.
		now apply type_press in HA.
		apply type_subs_inv in HA as [Γ0 [Hy HA]].
		apply (Hsubs _ Γ0 y A Hy HA).
		now apply IHA.
Qed.

Check SubsJG_ind.

Lemma SubsJG_core_ind :	forall P : preCtx -> preCtx -> preSubs -> Prop,
	(forall (Γ : preCtx) (A : preType), [Γ ⊢ A type ] ->
			P (Γ # A)%ctx Γ p) ->
	(forall Γ : preCtx,	 [ ⊢ Γ cx ] -> P Γ Γ id) ->
	(forall (Γ2 Γ1 Γ0 : preCtx) (y1 y0 : preSubs),
	[Γ2 ⊢ y1 ~ Γ1] -> P Γ2 Γ1 y1 -> [Γ1 ⊢ y0 ~ Γ0] -> P Γ1 Γ0 y0
	-> P Γ2 Γ0 (y0 ∘ y1)%subs) ->
	(forall (Δ Γ : preCtx) (y : preSubs) (a : preTerm) (A : preType),
		[Δ ⊢ y ~ Γ] ->	P Δ Γ y -> [Γ ⊢ A type ] -> [Δ ⊢ a @ A [y]]
		-> P Δ (Γ # A)%ctx (y # a)%subs) ->
	forall (Δ Γ : preCtx) (y : preSubs), [Δ ⊢ y ~ Γ] -> P Δ Γ y.
Proof.
	intros P Hweak Hid Hcomp Hext.
	apply SubsJG_ind; try (tauto).
	intros Δ Γ Δ' y HeqΔ Hy IH.
	rewrite HeqΔ in Hy.
	dependent induction Hy generalizing Δ HeqΔ.
	- now apply Hweak.
	- now apply Hid.
Abort.

Lemma subs_ext_mor {Δ Γ : preCtx} {y : preSubs} {A : preType} {a b : preTerm}:
	[ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a == b @ A[y] ] ->
	[ Δ ⊢ y # a == y # b ~ Γ # A ].
Proof.
	intros Hy HA Ha.
	dependent induction Ha generalizing y A Hy HA.

Qed.

Lemma subs_comp_ext_dist {Δ Γ Θ : preCtx} {y d : preSubs} {A: preType} {a : preTerm}:
	[ Θ ⊢ d ~ Δ ] -> [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a @ A [y] ] ->
	[ Θ ⊢ (y # a) ∘ d == (y ∘ d) # a[d] ~ Γ # A ].
Proof.
	intros Hd Hy HA Ha.
	rewrite eq_subs_eta.
	apply (subs_ext Hy HA) in Ha.
	apply (subs_comp Hd) in Ha.
Qed.

(* Add Parametric Morphism Δ Γ Θ : psub_comp
	with signature (eq_subs Δ Γ) ==> eq_subs Γ Θ ==> eq_subs Δ Θ
	as subs_comp_mor.
Proof.
	intros y1 y1' Hy1 y0 y0' Hy0. *)

(* Lemma subs_comp_mor_l {y1 y0 y0' : preSubs} {Δ Γ Θ : preCtx}
	(Hy : [ Δ ⊢ y1 ~ Γ ]) (HeqY : [ Γ ⊢ y0 == y0' ~ Θ ]) :
		[ Δ ⊢ y0 ∘ y1 == y0' ∘ y1 ~ Θ ].
Proof.
	dependent induction HeqY generalizing Δ y1 Hy; try (tauto).
	- specialize (IHHeqY _ _ Hy) as Hy1.
		now symmetry.
	- specialize (IHHeqY1 _ _ Hy) as Hy1.
		specialize (IHHeqY2 _ _ Hy) as Hy2.
		now transitivity (y2 ∘ y1)%subs.
	-	apply subs_press in H as Hx.
		destruct Hx as [HΔ0 HΓ].
		rewrite <- (eq_subs_comp_assoc Hy H (subs_id HΓ)).
		apply eq_subs_id_left.
		now apply (subs_comp Hy H).
	-	apply subs_press in H as Hx.
		destruct Hx as [HΔ0 HΓ].
		rewrite <- (eq_subs_comp_assoc Hy (subs_id HΔ0) H).
		admit.
	- admit.
	- admit.
	- admit.
	- apply IHHeqY.
Qed. *)
Lemma  type_subs_homo_T
	{y : preSubs}
	{Δ Γ : preCtx}
	{A B : preType}
	(Hy : [ Δ ⊢ y ~ Γ ]) (HeqA : [ Γ ⊢ A == B type ]) :
		[ Δ ⊢ A [y] == B [y] type ]
with subs_comp_mor_l
	{y1 y0 y0' : preSubs}
	{Δ Γ Θ : preCtx}
	(Hy : [ Δ ⊢ y1 ~ Γ ]) (HeqY : [ Γ ⊢ y0 == y0' ~ Θ ]) :
		[ Δ ⊢ y0 ∘ y1 == y0' ∘ y1 ~ Θ ]
. Proof.
	(* Substitution over left quotient *)
	(* Type Substitution Homogeneity *)
	-	dependent induction HeqA generalizing Δ y Hy.
		+	specialize (IHHeqA _ _ Hy).
			now symmetry.
		+	specialize (IHHeqA1 _ _ Hy).
			specialize (IHHeqA2 _ _ Hy).
			now transitivity (B [y])%ty.
		+	pose proof (subs_id (type_press H)) as Hid.
			rewrite <- (eq_type_subs_comp Hy Hid H).
			now apply (eq_type_subs_mor (eq_subs_id_left Hy) H).
		+	rewrite <- (eq_type_subs_comp Hy (subs_comp H H0) H1).
			rewrite <- (eq_type_subs_comp Hy H (type_subs H0 H1)).
			rewrite <- (eq_type_subs_comp (subs_comp Hy H) H0 H1).
			symmetry.
			apply (eq_type_subs_mor (eq_subs_comp_assoc Hy H H0) H1).
		+
			apply eq_subs_press in H as Hyy.
			destruct Hyy as [Hy0 Hy'].
			rewrite <- (eq_type_subs_comp Hy Hy0 H0).
			rewrite <- (eq_type_subs_comp Hy Hy' H0).
			apply (eq_type_subs_mor
						(subs_comp_mor_l _ _ _ _ _ _ Hy H)
						H0).
		+	apply IHHeqA.
			now rewrite H.

	-	dependent induction HeqY.
		specialize (IHHeqY Hy).
		now symmetry.
		specialize (IHHeqY1 Hy).
		specialize (IHHeqY2 Hy).
		now transitivity (y2 ∘ y1)%subs.
		pose proof (subs_id (proj2 (subs_press H))) as Hid.
		rewrite <- (eq_subs_comp_assoc Hy H Hid).
		apply eq_subs_id_left.
		now apply (subs_comp Hy H).
		admit.
		admit.
Admitted.


(******************************************************************************)
(** Proof of pressupositions For Jugements **)
Lemma type_comp_inv {Γ : preCtx} {A : preType} {y0 y1} :
   [ Γ ⊢ A [y0 ∘ y1] type ] <-> [ Γ ⊢ A [y0] [y1] type ].
Proof.
   split; intro HA.
   dependent induction HA using TypeJG_core_ind.
	apply subs_comp_inv in H as [Γ0 [Hy1 Hy0]].
   apply (type_subs Hy1 (type_subs Hy0 HA)).
   apply type_subs_inv in HA as [Γ1 [Hy1 HA]].
   apply type_subs_inv in HA as [Γ0 [Hy0 HA]].
   apply (type_subs (subs_comp Hy1 Hy0) HA).
Qed.

Lemma type_id_inv {Γ : preCtx} {A} :
   [ Γ ⊢ A [id] type ] <-> [ Γ ⊢ A type ].
Proof.
   split;
      intro HA.
		apply type_subs_inv in HA as [Γ' [Hy HA]].
		apply subs_id_inv in Hy as [HeqΓ _].
		now rewrite HeqΓ.
      apply type_press in HA as HΓ.
      now apply (type_subs (subs_id HΓ)).
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
(*
Lemma subs_bang_inv {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ] -> (!)%subs = δ.
Abort. * should we do something for bang ? * *)

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


