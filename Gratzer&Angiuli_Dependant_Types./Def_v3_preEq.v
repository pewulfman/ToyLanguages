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
(* Check ( λ ( q ) ). *)
(* Check ( app( λ ( q ) , q ) ). *)

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

Inductive pre_eq_type : preType -> preType -> Prop :=
| pre_eq_type_refl {A} : pre_eq_type A A
(* | pre_eq_type_sym {A B} : pre_eq_type A B -> pre_eq_type B A
| pre_eq_type_trans {A B C} : pre_eq_type A B -> pre_eq_type B C -> pre_eq_type A C *)
| pre_eq_type_subs_id {A} : pre_eq_type A (A [ Id ])%ty
| pre_eq_type_subs_comp {A} {y1 y0} : pre_eq_type (A [ y0 ∘ y1 ])%ty (A [ y0 ] [ y1 ])%ty
| pre_eq_type_prod_distrib {A B y} : pre_eq_type ( (A * B) [ y ]) (A [ y ] * B [ y ])%ty
| pre_eq_type_func_distrib {A B y} : pre_eq_type ( (A --> B) [ y ]) (A [ y ] --> B [ y ])%ty
.

Inductive pre_eq_term : relation (preTerm) :=
| pre_eq_term_refl {e} : pre_eq_term e e
| pre_eq_term_subs_id {e} : pre_eq_term e (e [ Id ])%term
| pre_eq_term_subs_comp {y1 y0} {e} : pre_eq_term (e [ y0 ∘ y1 ])%term (e [ y0 ] [ y1 ])%term
| pre_eq_term_pair_distrib {a b y} : pre_eq_term ( (a, b) [ y ]) (a [ y ], b [ y ])%term
| pre_eq_term_fst_distrib {p y} : pre_eq_term (fst p [ y ]) (fst (p [ y ]))%term
| pre_eq_term_snd_distrib {p y} : pre_eq_term (snd p [ y ]) (snd (p [ y ]))%term
| pre_eq_term_func_distrib {b y} : pre_eq_term ( λ (b) [ y ]) (λ (b [ y ]) )%term
| pre_eq_term_app_distrib {f a y} : pre_eq_term ( app(f, a) [ y ]) (app(f [ y ], a [ y ]) )%term
.

Inductive pre_eq_subs : preSubs -> preSubs -> Prop :=
| pre_eq_subs_refl {y} : pre_eq_subs y y
(* | pre_eq_subs_sym {y1 y2} : pre_eq_subs y1 y2 -> pre_eq_subs y2 y1 *)
(* | pre_eq_subs_trans {y1 y2 y3} : pre_eq_subs y1 y2 -> pre_eq_subs y2 y3 -> pre_eq_subs y1 y3 *)
| pre_eq_subs_left_id {y} : pre_eq_subs (Id ∘ y) y
| pre_eq_subs_right_id {y} : pre_eq_subs (y ∘ Id) y
| pre_eq_subs_comp_assoc {y0 y1 y2} : pre_eq_subs (y0 ∘ (y1 ∘ y2)) ((y0 ∘ y1) ∘ y2)
.

Add Relation preType pre_eq_type
   reflexivity proved by (@pre_eq_type_refl)
   as pre_eq_type_rel
.

Add Relation preTerm pre_eq_term
   reflexivity proved by (@pre_eq_term_refl)
   as pre_eq_term_rel
.

Add Relation preSubs pre_eq_subs
   reflexivity proved by (@pre_eq_subs_refl)
   as pre_eq_subs_rel
.

Reserved Notation "[ ⊢ Γ 'Cx' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"     (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]" (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y ~ Γ ]" (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A1 == A2 'type' ]" (at level 0, no associativity) .
Reserved Notation "[ Γ ⊢ a '==' b @ A ]" (at level 0, no associativity) .
Reserved Notation "[ Δ ⊢ y == y' ~ Γ ]" (at level 0, no associativity).


Section Symmetric_Transitive_Closure.
   Variable A : Type.
   Variable R : relation A.

  Inductive clos_sym_trans : relation A :=
    | st_step (x y:A) : R x y -> clos_sym_trans x y
    | st_sym (x y:A) : clos_sym_trans x y -> clos_sym_trans y x
    | st_trans (x y z:A) :
        clos_sym_trans x y ->
        clos_sym_trans y z -> clos_sym_trans x z.

End Symmetric_Transitive_Closure.

(** Judgments **)

Inductive  ContextJG : preContext -> Prop :=
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
      [ Γ ⊢ B type ] -> [ Γ # A ⊢ b @ B [p] ]
      -> [ Γ ⊢ λ (b) @ (A --> B) ]
   | term_app {Γ A B f a} :
      [ Γ ⊢ a @ A ] -> [ Γ ⊢ B type ] -> [ Γ ⊢ f @ (A --> B) ]
      -> [ Γ ⊢ app(f, a) @ B ]
   | term_subs {Δ Γ} {y} {A} {a} :
      [ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
      -> [ Δ ⊢ (a [y]) @ (A [y]) ]
   | term_conv {Γ} {A B} {e} :
      [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ]
      -> [ Γ ⊢ e @ B ]
   (* | term_unconv {Γ} {A} {e} :
      [ Γ ⊢ conv e @ A ]
       -> [ Γ ⊢ e @ A ] *)

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
| eq_type_step {Γ A B} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ B type ] -> pre_eq_type A B
   -> [ Γ ⊢ A == B type ]
| eq_type_sym {Γ} {A B} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == A type ]
| eq_type_trans {Γ} {A B C} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == C type ]
   -> [ Γ ⊢ A == C type ]
(** Enforce distributivity of substitution over type constructors **)
(* | eq_type_subst_prod {Δ Γ A B y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A * B) [ y ] == A [y] * B [y] type ]%ty
| eq_type_subst_func {Δ Γ A B y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A --> B) [ y ] == A [y] --> B [y] type ]%ty *)
(** Enforce compatibility with substitution **)
(* | eq_type_subs_id {Γ A} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A [ Id ] == A type ]%ty
| eq_type_subs_comp {Γ Γ1 Γ0} {A} {y1} {y0} :
   [ Γ ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]%ty *)

with eq_term : preContext -> preType -> relation (preTerm) :=
(** Enforce equivalence **)
| eq_term_step {Γ A} a b :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ A ] -> pre_eq_term a b
   -> [ Γ ⊢ a == b @ A ]
(** Enforce compatibility with term constructors **)
| eq_term_pair {Γ} {A B} {a1 a2 b1 b2} :
   [ Γ ⊢ a1 == a2 @ A ] -> [ Γ ⊢ b1 == b2 @ B ]
   -> [ Γ ⊢ (a1, b1) == (a2, b2) @ A * B ]
| eq_term_func {Γ} {A B} {b1 b2} :
   [ Γ ⊢ B type ] -> [ Γ # A ⊢ b1 == b2 @ B [p] ]
   -> [ Γ ⊢ λ (b1) == λ (b2) @ A --> B ]
| eq_term_subs {Δ Γ} {y} {A a1 a2} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a1 == a2 @ A ]
   -> [ Δ ⊢ a1 [y] == a2 [y] @ A [y] ]
(** Compatibility for substitution **)
| eq_term_id {Γ} {A a} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ Id ] == a @ A ]
| eq_term_comp {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1] == a [y0] [y1] @ A [y0 ∘ y1] ]
(** βη-equivalence for pairs **)
| eq_term_beta_fst {Γ} {A B} a b :
   [ Γ ⊢ a @ A] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ fst (a, b) == a @ A ]
| eq_term_beta_snd {Γ} {A B} a b :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ snd (a, b) == b @ B ]
| eq_term_eta_pair {Γ} {A B} p :
   [ Γ ⊢ p @ A * B ]
   -> [ Γ ⊢ p == (fst p, snd p) @ A * B ]
(** βη-equivalence for abstractions **)
| eq_term_beta_app {Γ} {A B} {a b} :
   [Γ ⊢ B type] -> [ Γ # A ⊢ b @ B [p] ] -> [ Γ ⊢ a @ A ]
   (* [Γ ⊢ B type] -> [ Γ # A ⊢ b @ B [ (p o Id) # a] ] -> [ Γ ⊢ a @ A ] *)
   -> [ Γ ⊢ app( λ (b) , a ) == b [ Id # a] @ B ]
| eq_term_eta_app {Γ} {A B} {f} :
   [ Γ ⊢ B type] -> [ Γ ⊢ A type ] -> [ Γ ⊢ f @ (A --> B) ]
   -> [ Γ ⊢ f == (λ (app(f, q))) @ (A --> B) ]
(** βη-equivalence for substitution extension **)
| eq_beta_quar {Δ} {Γ} {y} {A} {a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ]

with eq_subs : preContext -> preContext -> relation (preSubs) :=
(** Enforce equivalence **)
| eq_subs_step {Δ Γ} {y1 y2}:
   [ Δ ⊢ y1 ~ Γ ] -> [ Δ ⊢ y2 ~ Γ ] -> pre_eq_subs y1 y2
   -> [ Δ ⊢ y1 == y2 ~ Γ ]
| eq_subs_sym {Δ Γ} {y1 y2} :
   [ Δ ⊢ y1 == y2 ~ Γ ]
   -> [ Δ ⊢ y2 == y1 ~ Γ ]
| eq_subs_trans {Δ Γ} {y1 y2 y3} :
   [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ]
   -> [ Δ ⊢ y1 == y3 ~ Γ ]
(** Compatibility with composition **)
(* | eq_subs_left_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ Id ∘ y == y ~ Γ ]
| eq_subs_right_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ y ∘ Id == y ~ Γ ]
| eq_subs_comp_assoc {Γ3 Γ2 Γ1 Γ0} {y0 y1 y2} :
   [ Γ3 ⊢ y2 ~ Γ2 ] -> [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0]
   -> [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ0 ] *)
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
and "[ Δ ⊢ y == y' ~ Γ ]" := (eq_subs Δ Γ y y') : subs_scope
.
(** End Jugements *)

Example Ex1 : ([1 ⊢ base * base --> base type ]).
Proof.
   apply type_func.
   - apply type_prod; apply type_base; apply context_empty.
   - apply type_base. apply context_empty.
Qed.

(** Scheme **)
Check eq_type_ind.

Add Parametric Relation Γ : (preType) (eq_type Γ)
   symmetry proved by (@eq_type_sym Γ)
   transitivity proved by (@eq_type_trans Γ)
   as eq_type_rel.

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
      + specialize (IHSubsJG2 IHTypeJG A H1 ).
         specialize (IHSubsJG1 IHSubsJG2 (A [y0])%ty ).
         apply IHSubsJG1.
         eapply type_subs;
         eassumption.
      + apply context_extend; assumption.
      + inversion IHTypeJG; subst.
        apply (IHSubsJG H5 A H6).
Qed.


Lemma eq_type_refl {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A == A type ]%ty.
Proof.
   intro H.
   constructor; try assumption.
   apply pre_eq_type_refl.
Qed.
Lemma eq_type_id {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A == A [Id] type ]%ty.
Proof.
   intro H.
   constructor.
   assumption.
   econstructor.
   apply subs_id.
   apply (type_coherence H).
   assumption.
   apply pre_eq_type_subs_id.
Qed.

Lemma type_id {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A [Id] type ]%ty.
Proof.
   intro H.
   eapply type_subs; try eassumption.
   apply subs_id.
   apply (type_coherence H).
Qed.

Lemma eq_type_comp {Γ Γ1 Γ0} {A} {y1 y0} :
   [ Γ ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]%ty.
Proof.
   intros H_y1 H_y0 H_A.
   constructor.
   eapply type_subs; try eassumption.
   eapply subs_comp; eassumption.
   eapply type_subs; try eassumption.
   eapply type_subs; try eassumption.
   constructor.
Qed.

Lemma eq_type_prod {Γ A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A * B) == (C * D) type ]%ty.
Proof.
   intros H_A H_B.
   dependent induction H_A; dependent induction H_B.
   - inversion H1; subst.
      + inversion H4; subst.
         * apply eq_type_refl.
            constructor; assumption.
         *
      + eapply eq_type
   eapply type_subs; try eassumption.
   eapply type_subs; try eassumption.
   apply eq_type_refl.
   apply eq_type_refl.
Qed.

(** Quotient and Notations coherences **)

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
Qed.

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as preType_mor.
Proof.
   intros A B Heq.
   induction Heq.
   - tauto.
   - symmetry. assumption.
   - etransitivity; try (eassumption).
Qed.


Theorem term_coherence {Γ A a}:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
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
   - constructor.
      2: assumption.
      apply type_coherence in IHTermJG.
      inversion IHTermJG; subst.
       assumption.
   - inversion IHTermJG2; subst.
      assumption.
   - econstructor.
      eassumption.
      assumption.
   - rewrite <- H0.
      assumption.
Qed.

Lemma type_fundation Γ A B e:
   [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ] -> [ Γ ⊢ e @ B ].
Proof. apply term_conv. Qed.

Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_jug_eq_term_mor.
Proof.
   intros.
   split; intro; [ |symmetry in H] ; eapply type_fundation; eassumption.
Qed.

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

Add Parametric Morphism Γ : (eq_type Γ)
   with signature (eq ==> eq_type Γ ==> iff)
   as eq_type_mor1.
Proof.
   intros A B1 B2 H_eq1.
   split; intro;
   eapply eq_type_trans;
   try (eassumption);
   eapply eq_type_trans;
   try (eassumption);
   apply eq_type_sym.
   apply H_eq1.
   constructor.
   1-2: apply (eq_type_coherence H_eq1).
   reflexivity.
Qed.


Add Parametric Morphism Γ : (eq_type Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as eq_type_mor2.
Proof.
   intros A1 A2 H_eq1 B.
   split; intro;
   eapply eq_type_trans;
   try (eassumption);
   eapply eq_type_trans;
   try (eassumption);
   apply eq_type_sym.
   apply H_eq1.
   constructor.
   1-2: apply (eq_type_coherence H_eq1).
   reflexivity.
Qed.

Lemma eq_type_subs_1 {Δ Γ A y1 y2} :
   [ Δ ⊢ y1 == y2 ~ Γ ] ->
   [ Γ ⊢ A type ] ->
   [ Δ ⊢ A [ y1 ] == A [y2] type ]%ty.
Proof.
   intros H_eq H_A.
   dependent induction H_eq generalizing A.
   - inversion H1; subst.
      +  apply eq_type_refl.
         apply (type_subs H0 H_A).
      +  erewrite (eq_type_comp H0).
         remember (eq_type_id H_A) as H_eq_id.
         apply eq_type_subs.
         rewrite H_eq_id.

         apply (type_id H_A).
         apply (type_subs H0 H_A).

         apply (type_subs H0 H_A).
         reflexivity.
      +
   eapply type_subs; try eassumption.
   eapply eq_subs_left_id; try eassumption.
   eapply eq_subs_right_id; try eassumption.
   eapply type_subs; try eassumption.
   constructor.

Theorem eq_term_coherence :
   forall {Γ A a b}, [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
   intros Γ A a b Heq.
   dependent induction Heq.
   - tauto.
   - destruct IHHeq1 as [H_a1 H_a2].
      destruct IHHeq2 as [H_b1 H_b2].
      split; apply term_pair; assumption.
   - destruct IHHeq as [H_b1 H_b2].
      apply term_coherence in H_b1 as H_B.
       split; apply term_abs; try assumption.
   - split.
      assert (H_eq : [ Γ ⊢ A == A[Id] type]%ty).
         apply eq_type_id.
         apply (term_coherence H).
      rewrite H_eq.
      eapply term_subs.
         apply subs_id.
         apply (term_coherence) in H.
         apply (type_coherence H).
         assumption.
         assumption.
   - split.
      eapply term_subs.
      eapply subs_comp;
      eassumption.
      assumption.
      assert (H_eq : [ Γ2 ⊢ A [y0 ∘ y1] == A[y0] [y1] type]%ty).
         eapply eq_type_comp; try eassumption.
         apply (term_coherence H1).
      rewrite H_eq.
         eapply term_subs; try eassumption.
         eapply term_subs; try eassumption.
   - split; [apply @term_fst with (B:=B); constructor | ]; eassumption.
   - split; [apply @term_snd with (A:=A); constructor | ]; eassumption.
   - split. assumption.
      constructor; econstructor; try eassumption.
   -  remember (type_coherence H) as HΓ.
      remember (term_coherence H1) as HA.
       split.
      econstructor; try eassumption.
      econstructor; assumption.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      assumption.
      apply HA.
      apply (type_fundation _ A (A [Id]) _ H1).
      apply eq_type_id; assumption.
      apply H0.
      transitivity (B [p ∘ (Id # a)]%ty).
      symmetry. eapply eq_type_comp.
      constructor.
      constructor.
      assumption.
      apply HA.
      apply (type_fundation _ A (A [Id]) _ H1).
      apply eq_type_id; assumption.
      constructor.
      assumption.
      assumption.
      transitivity (B [Id]%ty).
      apply eq_type_subs.

      apply (type_fundation _ A (A [Id]) _ H1).
      apply eq_type_id; assumption.
      constructor;
      assumption.
      assumption.
      econstructor.
      constructor.
      assumption.
      assumption.




      remember (eq_type_id Γ B H) as H_eq_id.

      econstructor.
      apply HA.
      apply (type_fundation _ A (A [Id]) _ H1).
      apply eq_type_id; assumption.
      apply (term_coherence H0).



         assumption.

Lemma type_fundation Γ A B e:
   [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ] -> [ Γ ⊢ e @ B ].
Proof. apply term_conv. Qed.

Add Parametric Morphism Γ A : (TermJG Γ A)
   with signature (eq_term Γ A ==> iff)
   as type_jug_eq_type_mor.
Proof.
   intros a1 a2 H_eq.
   induction H_eq; intros.
   - tauto.
   - split; intro.
      inversion H; subst.
      apply IHH_eq1 in H4.
      apply IHH_eq2 in H6.
      apply term_pair; assumption.
      eapply IHTermJG; try eauto.


Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as type_jug_eq_type_mor.
Proof.
   intros A1 A2 H_eq.
   induction H_eq; intro.
   shelve.
   symmetry. apply IHH_eq.
   etransitivity.
      apply IHH_eq1.
      apply IHH_eq2.
      Unshelve.
   revert y0.
   induction H1; intros.
      + tauto.
      + split; intro.
      (* Requires rewriting y0 -> y0[Id] *)
Abort.

Lemma TypeFundation :
   forall Γ A B a, [ Γ ⊢ a @ A ] ->
    [ Γ ⊢ A == B type ] -> [ Γ ⊢ a @ B ].
Proof.
   intros.
   rewrite <- H0.
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


Add Parametric Morphism Γ : (eq_type Γ)
   with signature (pre_eq_type ==> eq_type Γ ==> iff)
   as type_jug_mor.
Proof.
   intros A1 A2 H_eq1.
   dependent induction H_eq1; intros B1 B2 H_eq2.
   - induction H_eq2.
      tauto.
      symmetry. assumption.
      rewrite IHH_eq2_1. assumption.
   - symmetry. apply IHH_eq1.
      symmetry. apply H_eq2.
   - etransitivity.
      apply IHH_eq1_1. apply H_eq2.
      apply IHH_eq1_2.
      constructor.
      apply (eq_type_coherence H_eq2).
   - rewrite <- H_eq2.
      split; intro.
      rewrite <- H.
      apply eq_type_subs_id. assumption.
      apply eq_type_subs_id. assumption.

Lemma eq_type_prod Γ A1 A2 B1 B2 :
   [ Γ ⊢ A1 == A2 type ] -> [ Γ ⊢ B1 == B2 type ]
   -> [ Γ ⊢ A1 * B1 == A2 * B2 type ].
Proof.
   intro H.
   revert B1 B2.
   induction H.
   - intros C D H0.
   revert A H.
   induction H0; intros.
   apply eq_type_refl. constructor; assumption.
   symmetry. apply IHeq_type. assumption.
   specialize (IHeq_type1 _ H) as IHeq1.
   specialize (IHeq_type2 _ H) as IHeq2.
   apply (eq_type_trans IHeq1 IHeq2).
   - intros C D H0.
    symmetry. apply IHeq_type. symmetry. assumption.
   - intros D E H1.
      specialize (IHeq_type1 _ _ H1) as IHeq1.
      etransitivity.
      apply IHeq1.
      apply IHeq_type2.
      constructor.
      apply (eq_type_coherence H1).
Qed.

Add Parametric Morphism Γ : (@ptyp_prod)
   with signature (eq_type Γ ==> eq_type Γ ==> eq_type Γ)
   as eq_type_prod_mor.
Proof. intros.
   apply eq_type_prod; assumption.
Qed.


Lemma typing_unicity_subs Γ A B a:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ B ]
   -> [ Γ ⊢ A == B type ].
Proof.
   revert Γ A B.
   induction a; intros.
   - inversion H; subst.
      inversion H0; subst.
      apply eq_type_refl.
      econstructor.
      econstructor.
      assumption.
      assumption.
   -  inversion H; subst.
      inversion H0; subst.
      apply eq_type_prod.
      apply IHa1; assumption.
      apply IHa2; assumption.
   - inversion H; subst.
      inversion H0; subst.
      specialize (IHa _ _ _ H4 H5) as IHeq.
      (* requires type_prod inversion *)
Abort.

Lemma subs_codomain_eq :
   forall y Δ Γ1 Γ0, [ Δ ⊢ y ~ Γ1 ] -> [ Δ ⊢ y ~ Γ0 ] -> Γ1 = Γ0.
Proof.
   induction y; intros.
   - inversion H; subst.
      inversion H0; subst.
      reflexivity.
   - inversion H; subst.
      inversion H0; subst.
      specialize (IHy2 _ _ _ H5 H7). subst.
      specialize (IHy1 _ _ _ H8 H6). subst.
      reflexivity.
   - inversion H; subst.
      inversion H0; subst.
      reflexivity.
   - inversion H; subst.
      inversion H0; subst.
      reflexivity.
   - inversion H; subst.
      inversion H0; subst.
      specialize (IHy _ _ _ H3 H4). subst.
      f_equal.
      (* requires typing unicity *)
   Abort.

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (pre_eq_type ==> iff)
   as type_jug_mor.
Proof.
   intros A B H.
   induction H.
   reflexivity.
   symmetry. apply IHpre_eq_type.
   transitivity [ Γ ⊢ B type ]; try assumption.
   -  split; intro.
      eapply type_subs. 2: eassumption.
      apply subs_id. apply type_coherence in H as H2. assumption.
      inversion H; subst.
      inversion H3; subst.
      assumption.
   - split; intro; inversion H; subst.
      inversion H4; subst.
      apply type_prod;
      eapply type_subs; try eassumption.
      inversion H3; subst.
      inversion H4; subst.
      apply (type_subs H5).
      apply type_prod. assumption.
    (* requites sub codomain unicity *)


Derive Inversion eq_type_prod_inversion with (forall Γ A B C D, [ Γ ⊢ A * B == C * D type ]) Sort Prop.

Theorem subs_coherence :
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
      apply subs_coherence in H.
      destruct H as [H1 H2].
      assumption.
   - split; intro.
      assumption.
      eapply subs_comp.
      apply subs_id.
      apply subs_coherence in H.
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
      apply subs_coherence in H as [H1 H2].
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
         eapply eq_type_subs_comp.
         apply H0.
         apply subs_weak.
         apply H.
         apply H.
      }
      rewrite H_eq.
      eapply term_subs.
      apply H0.
      constructor.
      assumption.
Qed.


Theorem eq_subs_coherence :
   forall {Δ Γ y y'}, [ Δ ⊢ y == y' ~ Γ ] -> [ Δ ⊢ y ~ Γ ].
Proof.
   intros.
   induction H.
   - assumption.
   - rewrite <- H.
      apply IHeq_subs.
   - assumption.
   -  econstructor.
      apply H.
      apply subs_id.
      apply subs_coherence in H as [H1 H2].
      assumption.
   -  econstructor.
      apply subs_id.
      apply subs_coherence in H as [H1 H2].
      assumption.
      assumption.
   -  econstructor.
      econstructor.
      apply H.
      apply H0.
      apply H1.
   -  econstructor.
      apply subs_coherence in H as [H1 H2].
      assumption.
   -  econstructor.
      econstructor.
      apply H.
      apply H0.
      apply H1.
      constructor.
      assumption.
   - assumption.
Qed.


Add Parametric Morphism Γ : (ptyp_prod)
   with signature (eq_type Γ ==> eq_type Γ ==> eq_type Γ)
   as eq_type_prod_mor.
Proof.
   intros A1 A2 H_eq1 B1 B2 H_eq2.
   apply eq_type_prod; assumption.

Derive Inversion prod_eq_inversion with (forall Γ A B C D, [ Γ ⊢ A * B == C * D type ]) Sort Prop.

Check prod_eq_inversion.


Lemma type_prod_injective_left Γ A1 A2 B :
   [ Γ ⊢ A1 * B == A2 * B type ]
   -> [ Γ ⊢ A1 == A2 type ].
Proof.
   intro.
   dependent induction H using eq_type_ind; intros.
   - inversion H; subst.
     constructor.
     apply H3.
   - symmetry.
      eapply IHeq_type; reflexivity.
   -
   remember (A2 * B) as T2.
   remember (A1 * B) as T1.
   revert A1 A2 B HeqT1 HeqT2 IHeq_type1 IHeq_type2.
   revert T1 H.
   dependent induction H0.
    + intros.
   eapply IHeq_type1; eauto.
    + intros.
   revert A A1 A2 B0 H0 HeqT1 HeqT2 IHeq_type1 IHeq_type2 IHeq_type.
   dependent induction H; intros.
   eapply IHeq_type2; eauto.
   eapply IHeq_type.
      inversion H0; subst.
      inversion H1.
      constructor; assumption.
      eapply IHeq_type2; eauto.
   remember (A1 * B) as T1.
   remember (A2 * B) as T2.
   (* apply eq_type_refl in H_T1, H_T2.
   rewrite HeqT1 in H_T1 at 2.
   rewrite HeqT2 in H_T2 at 2. *)
   (* clear HeqT1 HeqT2. *)
   revert A1 A2 B HeqT1 HeqT2.
   - inversion HeqT1; subst.
      inversion HeqT2; subst.
      inversion H.
      constructor; assumption.
   - symmetry.
      eapply IHeq_type; eassumption.
   - specialize (IHeq_type1 A1 A2 B0 HeqT1).
      specialize (IHeq_type2 A1 A2 B0).
      revert A A1 A2 B0 B H H0 HeqT1 HeqT2 IHeq_type1 IHeq_type2.
      dependent induction C; intros.
      +  inversion HeqT2.
      +
      eapply IHeq_type.
      symmetry. apply H0.
      apply IHeq_type2.
      intros. symmetry. eapply IHeq_type2; eassumption.
      revert A A1 A2 B0 H0 IHeq_type IHeq_type1 IHeq_type2 HeqAB1 HeqAB2.
      dependent induction H;
      intros.
      eapply IHeq_type2; eauto.
      eapply IHeq_type0.
      apply (eq_type_trans H0 H).
      apply IHeq_type0.

       inversion H; subst.
   -
        eapply eq_type_trans.

     + eapply IHeq_type1; eauto.

     + eapply IHHeq_type2; eauto.


Lemma type_prod_injective Γ A1 A2 B1 B2 :
   [ Γ ⊢ A1 * B1 == A2 * B2 type ]
   -> [ Γ ⊢ A1 == A2 type ].
Proof.
Admitted.

Lemma typing_unicity Γ A B a :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ B ]
   -> [ Γ ⊢ A == B type ].
Proof.
   intro.
   dependent induction H generalizing B; intro.
   - inversion H0; subst.
      apply eq_type_refl.
      econstructor.
      econstructor.
      assumption.
      assumption.
   - inversion H1; subst.
      specialize (IHTermJG1 _ H6) as IHeq1.
      specialize (IHTermJG2 _ H7) as IHeq2.
      apply eq_type_prod; assumption.
   - inversion H0; subst.
      specialize (IHTermJG _ H4) as IHeq.
      dependent induction IHeq.
      +  constructor.
         inversion H1; subst.
         assumption.
      + dependent induction H.
         inversion H; subst.
      constructor; assumption.
      eapply IHeq_type; try eassumption.
      setoid_rewrite IHeq.
      apply term_coherence in H0 as HC.

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

