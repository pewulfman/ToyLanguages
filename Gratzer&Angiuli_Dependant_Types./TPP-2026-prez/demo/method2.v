(* TPP 2026 demo -- Method 2: one inductive per judgement, tied with `with`

   The FULL judgements of the calculus of substitutions (8 judgements:
   4 basic + 4 equality, all rules), as in
   ../2.3 - Calculus of Substitution/definitions.v
   (Angiuli & Gratzer, Principles of Dependent Type Theory, Sec. 2.3).

   Method 2: copied verbatim from definitions.v (pre-syntax, notations,
   judgements).

   Compile:  rocq compile demo/<this file>    (or `make check`)
   Step through it in your IDE to see the proof states.                 *)

From Stdlib Require Import Program.Equality.  (* dependent induction *)

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

(******************************************************************************)
(** * Experiments *)

(** Induction on one judgement (slide 7). *)
Lemma wf Γ A : [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
  intros H. dependent induction H.
  (* One goal per TypeJG rule.  In the type_subs case, the type premise
     only gives the TARGET context, and the premise [Δ ⊢ y ~ Γ] has NO
     induction hypothesis: TypeJG_ind is not mutual. *)
  Show.
Abort.

Check TypeJG_ind.

(** Mutual principle (slide 9). *)
Scheme cx'   := Minimality for CtxJG   Sort Prop
with   sb'   := Minimality for SubsJG  Sort Prop
with   ty'   := Minimality for TypeJG  Sort Prop
with   tm'   := Minimality for TermJG  Sort Prop
with   eqcx' := Minimality for eq_ctx  Sort Prop
with   eqsb' := Minimality for eq_subs Sort Prop
with   eqty' := Minimality for eq_type Sort Prop
with   eqtm' := Minimality for eq_term Sort Prop.
Combined Scheme JG_ind from cx', sb', ty', tm', eqcx', eqsb', eqty', eqtm'.
Check JG_ind.

(******************************************************************************)
(** * Full-syntax checks of the techniques on the slides: Method 2 (slides 6, 9, 11, 12)

    The slides show an abridged syntax (4 rules); these proofs check the same
    techniques on all 8 judgements and all rules of 2.3. *)
Lemma subs_wf Δ Γ y (H : [ Δ ⊢ y ~ Γ ]) : [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
with type_wf Γ A (H : [ Γ ⊢ A type ]) : [ ⊢ Γ cx ]
with eqcx_wf Γ Δ (H : eq_ctx Γ Δ) : [ ⊢ Γ cx ] /\ [ ⊢ Δ cx ]
with eqty_wf Γ A B (H : [ Γ ⊢ A == B type ]) : [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
- dependent induction H.
  + split; assumption.
  + tauto.
  + pose proof (type_wf _ _ H). split; [apply ctx_ext; assumption | assumption].
  + destruct IHSubsJG. split; [assumption | apply ctx_ext; assumption].
  + destruct (eqcx_wf _ _ H). tauto.
  + destruct (eqcx_wf _ _ H). tauto.
- dependent induction H.
  + exact (proj1 (subs_wf _ _ _ H)).
  + assumption.
  + exact (proj2 (eqcx_wf _ _ H)).
- dependent induction H.
  + split; apply ctx_one.
  + destruct (eqty_wf _ _ _ H0) as [HA HB]. destruct IHeq_ctx.
    split; apply ctx_ext; [assumption | exact HA | assumption | exact (type_over_ctx_quot H HB)].
- dependent induction H.
  + tauto.
  + tauto.
  + split; [exact (type_subs (subs_id (type_wf _ _ H)) H) | exact H].
  + split; [exact (type_subs (subs_comp H H0) H1) | exact (type_subs H (type_subs H0 H1))].
  + destruct (subs_wf _ _ _ H) as [HD HG].
    split; [exact (type_subs H (type_unit HG)) | exact (type_unit HD)].
  + destruct IHeq_type. split; apply (type_over_ctx_quot H); assumption.
Qed.

(** The catch, on the full syntax: a circular proof is accepted step by step. *)
Lemma type_bad Γ A (H : [ Γ ⊢ A type ]) : [ ⊢ Γ cx ]
with  subs_bad Δ Γ y (H : [ Δ ⊢ y ~ Γ ]) : [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ].
Proof.
- exact (type_bad Γ A H).
  Fail Guarded.
- exact (subs_bad Δ Γ y H).
Fail Qed.
Abort.
