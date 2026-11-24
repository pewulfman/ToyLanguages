(* TPP 2026 demo -- Method 1: one family indexed by a sort

   The FULL judgements of the calculus of substitutions (8 judgements:
   4 basic + 4 equality, all rules), as in
   ../2.3 - Calculus of Substitution/definitions.v
   (Angiuli & Gratzer, Principles of Dependent Type Theory, Sec. 2.3).

   Method 1: the same pre-syntax and the same rules, translated to a single
   inductive J : Sort -> Prop (mechanical translation of definitions.v).

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
(** Method 1: one constructor per judgement form (a "sort") ... *)
Inductive Sort :=
| CX   (Γ : preCtx)
| SB   (Δ Γ : preCtx) (y : preSubs)
| TY   (Γ : preCtx) (A : preType)
| TM   (Γ : preCtx) (A : preType) (a : preTerm)
| EQCX (Γ Δ : preCtx)
| EQSB (Δ Γ : preCtx) (y y' : preSubs)
| EQTY (Γ : preCtx) (A B : preType)
| EQTM (Γ : preCtx) (A : preType) (a b : preTerm).

(** ... and ONE inductive J indexed by it.  The rules are those of
    definitions.v unchanged: the same notations now unfold to [J (...)];
    bare [eq_ctx X Y] became [J (EQCX X Y)]. *)
Inductive J : Sort -> Prop :=
   | ctx_one :
      [ ⊢ 1 cx ]
   | ctx_ext {Γ : preCtx} {A : preType} :
      [ ⊢ Γ cx ] -> [ Γ ⊢ A type ]
      -> [ ⊢  Γ # A cx]

(**** Substitution Judgments ****)
  (* ---- (was: SubsJG) ---- *)
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
		J (EQCX Δ Δ') -> [ Δ ⊢ y ~ Γ ]	-> [ Δ' ⊢ y ~ Γ ]
	| subs_over_ctx_quot_r {Δ Γ : preCtx} {Γ' : preCtx} {y : preSubs} :
		J (EQCX Γ Γ') -> [ Δ ⊢ y ~ Γ ]	-> [ Δ ⊢ y ~ Γ' ]

(*** Type Judgments ****)
  (* ---- (was: TypeJG) ---- *)
   | type_subs {Δ Γ : preCtx} {y : preSubs} {A : preType} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
      -> [ Δ ⊢ A [y] type ]
	| type_unit {Γ : preCtx} :
		[ ⊢ Γ cx ]
		-> [ Γ ⊢ Unit type ]
	(** compatibility with quotient **)
	| type_over_ctx_quot {Δ Γ : preCtx} {A : preType} :
		J (EQCX Δ Γ) -> [ Δ ⊢ A type ] -> [ Γ ⊢ A type ]

(*** Term Judgments ****)
  (* ---- (was: TermJG) ---- *)
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
		J (EQCX Δ Γ) -> [ Δ ⊢ a @ A ] -> [ Γ ⊢ a @ A ]
	| term_over_type_quot {Γ : preCtx} {A B : preType} {a : preTerm} :
		[ Γ ⊢ A == B type ] -> [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ B ]

(******************************************************************************)
(** Equivalence Relations **)

(*** Context Equivalence ****)
  (* ---- (was: eq_ctx) ---- *)
(* | eq_ctx_sym {Γ Δ : preCtx} : J (EQCX Γ Δ) -> J (EQCX Δ Γ) *)
(* | eq_ctx_trans {Γ Δ Θ : preCtx} : J (EQCX Γ Δ) -> J (EQCX Δ Θ) -> J (EQCX Γ Θ) *)
	| eq_ctx_one : J (EQCX pctx_one pctx_one)
	| eq_ctx_ext {Γ Δ : preCtx} {A B : preType} :
		J (EQCX Γ Δ) -> [ Γ ⊢ A == B type ]
		(* -> [ Δ ⊢ A == B type ] *)
		-> J (EQCX (Γ # A) (Δ # B))

(**** Substitution Equivalence ****)
  (* ---- (was: eq_subs) ---- *)
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
		J (EQCX Δ Δ') ->	[ Δ ⊢ y == y' ~ Γ ] -> [ Δ' ⊢ y == y' ~ Γ ]
	| eq_subs_over_ctx_quot_r {Δ Γ : preCtx} {Γ' : preCtx} {y y' : preSubs} :
		J (EQCX Γ Γ') -> [ Δ ⊢ y == y' ~ Γ ] -> [ Δ ⊢ y == y' ~ Γ' ]
	(** Morphism Property ? not clearly stated but implied, also don't know how to prove it **)
	| subs_ext_mor {Δ Γ : preCtx} {y y' : preSubs} {A : preType} {a b : preTerm}:
		[ Δ ⊢ y == y' ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ a == b @ A[y] ] ->
		[ Δ ⊢ y # a == y' # b ~ Γ # A ]

(**** Type Equivalence ****)
  (* ---- (was: eq_type) ---- *)
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
		J (EQCX Δ Γ) -> [ Δ ⊢ A == B type ] -> [ Γ ⊢ A == B type ]


(**** Term Equivalence ****)
  (* ---- (was: eq_term) ---- *)
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
		J (EQCX Δ Γ) -> [ Δ ⊢ a == b @ A ] ->
			[ Γ ⊢ a == b @ A ]
	| eq_term_over_type_quot {Γ : preCtx} {A B : preType} {a b : preTerm} :
		[ Γ ⊢ A == B type ] -> [ Γ ⊢ a == b @ A ] ->
		[ Γ ⊢ a == b @ B ]


where "[ ⊢ Γ 'cx' ]"          := (J (CX Γ))
and   "[ Γ ⊢ A 'type' ]"      := (J (TY Γ A))
and   "[ Γ ⊢ a @ A ]"         := (J (TM Γ A a))
and   "[ Δ ⊢ y ~ Γ ]"         := (J (SB Δ Γ y))
and   "[ Γ ⊢ A == B 'type' ]" := (J (EQTY Γ A B))
and   "[ Γ ⊢ a == b @ A ]"    := (J (EQTM Γ A a b))
and   "[ Δ ⊢ y == y' ~ Γ ]"   := (J (EQSB Δ Γ y y'))
.

(******************************************************************************)
(** * Experiments *)

(** Induction on one judgement (slide 7).  The index is always a
    constructor, so we use [dependent induction]. *)
Lemma wf Γ A : [ Γ ⊢ A type ] -> [ ⊢ Γ cx ].
Proof.
  intros H. dependent induction H.
  (* Only the TY rules remain; the IHs are guarded by the index equations.
     In the type_subs case (first goal), beware: the Γ bound inside the IHs
     is a FRESH variable (Rocq reuses the name).
     - IHJ2 (type premise):  specialize (IHJ2 _ _ eq_refl) gives the
       well-formedness of the TARGET context only, not the goal's;
     - IHJ1 (substitution premise): needs SB .. = TY .., never true. *)
  Show.
Abort.

(** Why are the IHs above useless for the substitution premise?
    [dependent induction] proves the motive
        P f := forall Γ A, f = TY Γ A -> [ ⊢ Γ cx ]
    for EVERY sort f, and each premise gets P at its own index:
    - premise [Γ0 ⊢ A0 type]  : IHJ2 needs TY Γ0 A0 = TY _ _   (usable, eq_refl)
    - premise [Γ ⊢ y ~ Γ0]    : IHJ1 needs SB .. = TY _ _      (never true!)
    So the IH for the substitution premise exists but is vacuous:
    exactly the same missing lemma as in Method 2.

    The Method-1 fix: choose the motive yourself, by cases on the sort,
    i.e. state the lemma for every judgement at once (workaround (c)). *)
Definition wf_motive (f : Sort) : Prop :=
  match f with
  | TY Γ _     => [ ⊢ Γ cx ]
  | SB Δ Γ _   => [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
  | TM Γ _ _   => [ ⊢ Γ cx ]
  | _          => True
  end.

Lemma wf_all : forall f, J f -> wf_motive f.
Proof.
  apply J_ind; simpl.
  (* One goal per rule of every judgement, and now the IH of a
     substitution premise is [ [⊢ Δ cx] /\ [⊢ Γ cx] ]: usable. *)
  Show.
Abort.

(** The generated principle (slide 9): one predicate over all forms. *)
Check J_ind.

(******************************************************************************)
(** * Full-syntax checks of the techniques on the slides: Method 1 (slide 13 and its pop-up)

    The slides show an abridged syntax (4 rules); these proofs check the same
    techniques on all 8 judgements and all rules of 2.3. *)
Definition press (f : Sort) : Prop :=
  match f with
  | SB Δ Γ _     => [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
  | TY Γ _       => [ ⊢ Γ cx ]
  | TM Γ _ _     => [ ⊢ Γ cx ]
  | EQCX Γ Δ     => [ ⊢ Γ cx ] /\ [ ⊢ Δ cx ]
  | EQTY Γ A B   => [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ]
  | _            => True
  end.

Lemma press_all f (H : J f) : press f.
Proof.
  induction H; simpl in *; intuition (eauto using J).
Qed.

(** Lemma ... with, in method 1: remember + destruct *)
Lemma subs1 Δ Γ y (H : J (SB Δ Γ y)) : [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
with type1 Γ A (H : J (TY Γ A)) : [ ⊢ Γ cx ]
with eqcx1 Γ Δ (H : J (EQCX Γ Δ)) : [ ⊢ Γ cx ] /\ [ ⊢ Δ cx ]
with eqty1 Γ A B (H : J (EQTY Γ A B)) : [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
all: lazymatch goal with
     | H : J ?f |- _ => remember f as g eqn:E
     end;
     destruct H; try discriminate; injection E; intros; subst;
     repeat match goal with
       | h : J (SB ?a ?b ?c) |- _ =>
           lazymatch goal with _ : [ ⊢ a cx ] /\ [ ⊢ b cx ] |- _ => fail
                             | _ => pose proof (subs1 _ _ _ h) end
       | h : J (TY ?a ?b) |- _ =>
           lazymatch goal with _ : [ ⊢ a cx ] |- _ => fail
                             | _ => pose proof (type1 _ _ h) end
       | h : J (EQCX ?a ?b) |- _ =>
           lazymatch goal with _ : [ ⊢ a cx ] /\ [ ⊢ b cx ] |- _ => fail
                             | _ => pose proof (eqcx1 _ _ h) end
       | h : J (EQTY ?a ?b ?c) |- _ =>
           lazymatch goal with _ : J (TY a b) /\ J (TY a c) |- _ => fail
                             | _ => pose proof (eqty1 _ _ _ h) end
     end;
     clear subs1 type1 eqcx1 eqty1;
     intuition (eauto using J).
Qed.

(** Same with dependent destruction: the guard fails at Qed *)
Lemma subs2 Δ Γ y (H : J (SB Δ Γ y)) : [ ⊢ Δ cx ] /\ [ ⊢ Γ cx ]
with type2 Γ A (H : J (TY Γ A)) : [ ⊢ Γ cx ]
with eqcx2 Γ Δ (H : J (EQCX Γ Δ)) : [ ⊢ Γ cx ] /\ [ ⊢ Δ cx ]
with eqty2 Γ A B (H : J (EQTY Γ A B)) : [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
all: lazymatch goal with
     | H : J ?f |- _ => dependent destruction H
     end;
     repeat match goal with
       | h : J (SB ?a ?b ?c) |- _ =>
           lazymatch goal with _ : [ ⊢ a cx ] /\ [ ⊢ b cx ] |- _ => fail
                             | _ => pose proof (subs2 _ _ _ h) end
       | h : J (TY ?a ?b) |- _ =>
           lazymatch goal with _ : [ ⊢ a cx ] |- _ => fail
                             | _ => pose proof (type2 _ _ h) end
       | h : J (EQCX ?a ?b) |- _ =>
           lazymatch goal with _ : [ ⊢ a cx ] /\ [ ⊢ b cx ] |- _ => fail
                             | _ => pose proof (eqcx2 _ _ h) end
       | h : J (EQTY ?a ?b ?c) |- _ =>
           lazymatch goal with _ : J (TY a b) /\ J (TY a c) |- _ => fail
                             | _ => pose proof (eqty2 _ _ _ h) end
     end;
     clear subs2 type2 eqcx2 eqty2;
     intuition (eauto using J).
Fail Qed.
Abort.
