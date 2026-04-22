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
| eq_type_refl {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A == A type ]
| eq_type_sym {Γ} {A B} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == A type ]
| eq_type_trans {Γ} {A B C} :
   [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == C type ]
   -> [ Γ ⊢ A == C type ]
(** Enforce compatibility with type constructors **)
| eq_type_prod {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A * B) == (C * D) type ]%ty
| eq_type_func {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A --> B) == (C --> D) type ]%ty
| eq_type_subs {Δ Γ} {y1 y2} {A1 A2} :
   [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Γ ⊢ A1 == A2 type ]
   -> [ Δ ⊢ A1 [y1] == A2 [y2] type ]%ty
(** Enforce compatibility with substitution **)
| eq_type_subs_id {Γ A} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A [ Id ] == A type ]%ty
| eq_type_subs_comp {Γ Γ1 Γ0} {A} {y1} {y0} :
   [ Γ ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]%ty
(** Enforce distributivity of substitution over type constructors **)
| eq_type_subs_prod {Δ Γ A B y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A * B) [ y ] == A [y] * B [y] type ]%ty
| eq_type_subs_func {Δ Γ A B y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A --> B) [ y ] == A [y] --> B [y] type ]%ty

with eq_subs : preContext -> preContext -> relation (preSubs) :=
(** Enforce equivalence **)
| eq_subs_refl {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y == y ~ Γ ]
| eq_subs_sym {Δ Γ} {y1 y2} :
   [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y1 ~ Γ ]
| eq_subs_trans {Δ Γ} {y1 y2 y3} :
   [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ]
   -> [ Δ ⊢ y1 == y3 ~ Γ ]
(** Enforce composition properties **)
| eq_subs_left_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ Id ∘ y == y ~ Γ ]
| eq_subs_right_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ]
   -> [ Δ ⊢ y ∘ Id == y ~ Γ ]
| eq_subs_comp_assoc {Γ3 Γ2 Γ1 Γ0} {y0 y1 y2} :
   [ Γ3 ⊢ y2 ~ Γ2 ] -> [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0]
   -> [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ0 ]
(** βη-equivalence for substitution extension **)
| eq_subs_beta {Δ Γ A a y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ p ∘ (y # a) == y ~ Γ ]
| eq_subs_eta {Δ Γ A y} :
   [ Γ ⊢ A type ] -> [ Δ ⊢ y ~ Γ # A ]
   -> [ Δ ⊢ y == ((p ∘ y) # (q[y])) ~ (Γ # A) ]
(** Unicity of bang **)
(* | eq_subs_bang {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ]
   -> [ Γ ⊢ ! == δ ~ 1 ] *)


with eq_term : preContext -> preType -> relation (preTerm) :=
(** Enforce equivalence **)
| eq_term_refl {Γ A a} : [ Γ ⊢ a @ A ] -> [ Γ ⊢ a == a @ A ]
| eq_term_sym {Γ A} {a b} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == a @ A ]
| eq_term_trans {Γ A} {a b c} :
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == c @ A ] -> [ Γ ⊢ a == c @ A ]
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
| eq_term_subs_id {Γ} {A a} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ Id ] == a @ A ]
| eq_term_subs_comp {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1] == a [y0] [y1] @ A [y0 ∘ y1] ]
(* don't know if needed
| pre_eq_term_pair_distrib {a b y} : pre_eq_term ( (a, b) [ y ]) (a [ y ], b [ y ])%term
| pre_eq_term_fst_distrib {p y} : pre_eq_term (fst p [ y ]) (fst (p [ y ]))%term
| pre_eq_term_snd_distrib {p y} : pre_eq_term (snd p [ y ]) (snd (p [ y ]))%term
| pre_eq_term_func_distrib {b y} : pre_eq_term ( λ (b) [ y ]) (λ (b [ y ]) )%term
| pre_eq_term_app_distrib {f a y} : pre_eq_term ( app(f, a) [ y ]) (app(f [ y ], a [ y ]) )%term *)

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
   -> [ Γ ⊢ f == (λ (app(f [p], q))) @ (A --> B) ]
(** βη-equivalence for substitution extension **)
| eq_beta_quar {Δ} {Γ} {y} {A} {a} :
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

Example Ex1 : ([1 ⊢ base * base --> base type ]).
Proof.
   apply type_func.
   - apply type_prod; apply type_base; apply context_empty.
   - apply type_base. apply context_empty.
Qed.

(** Register relations **)

Add Parametric Relation Γ : (preType) (eq_type Γ)
   symmetry proved by (@eq_type_sym Γ)
   transitivity proved by (@eq_type_trans Γ)
   as eq_type_rel.

Add Parametric Relation Δ Γ : (preSubs) (eq_subs Δ Γ)
   symmetry proved by (@eq_subs_sym Δ Γ)
   transitivity proved by (@eq_subs_trans Δ Γ)
   as eq_subs_rel.

Add Parametric Relation Γ A : (preTerm) (eq_term Γ A)
   symmetry proved by (@eq_term_sym Γ A)
   transitivity proved by (@eq_term_trans Γ A)
   as eq_term_rel.

(** End relations registration **)

(** Helpers Lemmas **)
Lemma type_fundation Γ A B e:
   [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ] -> [ Γ ⊢ e @ B ].
Proof. apply term_conv. Qed.


Corollary type_weak {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ # A ⊢ A [p] type ].
   (** End Helpers Lemmas **)
Proof. intros. apply (type_subs (subs_weak H) H). Qed.

(** Coherence Theorems **)
Theorem type_coherence :
   forall {Γ A}, [ Γ ⊢ A type ] -> [ ⊢ Γ Cx ].
Proof.
   intros.
   dependent induction H.
   - assumption.
   - assumption.
   - assumption.
   - dependent induction H generalizing A; intros; try (assumption).
      + specialize (IHSubsJG2 A H1 IHTypeJG ).
         specialize (IHSubsJG1 (A [y0]%ty) (type_subs H0 H1) IHSubsJG2).
         assumption.
      + apply context_extend; assumption.
      + inversion IHTypeJG; subst.
        apply (IHSubsJG A0 H6 H5).
Qed.


(**** helper ****)
Lemma type_id {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A [Id] type ]%ty.
Proof.
   intro H.
   eapply type_subs; try eassumption.
   apply subs_id.
   apply (type_coherence H).
Qed.

Lemma ctx_ext {Γ A} :
   [ Γ ⊢ A type ] -> [ ⊢ Γ # A Cx ].
Proof.
   intro H.
   apply type_coherence in H as H_ctx.
   apply context_extend; assumption.
Qed.
(**** Helpers ****)


Theorem subs_coherence :
   forall Δ Γ y, [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ Cx ] /\ [ ⊢ Γ Cx ].
Proof.
   intros.
   dependent induction H; try (assumption).
   - tauto.
   - tauto.
   - split. apply (ctx_ext H).
      apply (type_coherence H).
   - split. assumption.
      apply context_empty.
   - destruct IHSubsJG as [HΔ HΓ].
      split. assumption.
      apply (ctx_ext H0).
Qed.


Theorem eq_subs_coherence {Δ Γ y1 y0}:
   [ Δ ⊢ y1 == y0 ~ Γ ] -> [ Δ ⊢ y1 ~ Γ ] /\ [ Δ ⊢ y0 ~ Γ ].
Proof.
   intros.
   dependent induction H.
   - tauto.
   - apply and_comm. assumption.
   - destruct IHeq_subs1 as [H1 H2].
      destruct IHeq_subs2 as [H3 H4].
      split; assumption.
   -  split. 2:assumption.
      econstructor.
      apply H.
      apply subs_coherence in H as [HΔ HΓ].
      apply (subs_id HΓ).
   -  split. 2:assumption.
      apply subs_coherence in H as H2.
      destruct H2 as [HΔ HΓ].
      apply (subs_comp (subs_id (HΔ)) H).
   -  split.
      apply (subs_comp (subs_comp H H0) H1).
      apply (subs_comp H (subs_comp H0 H1)).
   -  split. 2:assumption.
      econstructor.
      apply (subs_ext H H0 H1).
      apply (subs_weak H0).
   -  split. assumption.
      remember (term_qar H) as H_q.
      remember (subs_weak H) as H_p.
      econstructor.
      apply (subs_comp H0 H_p).
      assumption.
      apply (type_fundation _ _ _ _ (term_subs H0 H_q)).
      symmetry.
      apply (eq_type_subs_comp H0 H_p H).
Qed.

Theorem eq_type_coherence :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
   intros.
   dependent induction H.
   - tauto.
   - apply and_comm. assumption.
   - destruct IHeq_type1 as [H_A1 H_A2].
      destruct IHeq_type2 as [H_A2' H_A3].
      split ; assumption.
   - destruct IHeq_type1 as [H_A1 H_A2].
      destruct IHeq_type2 as [H_B1 H_B2].
      split; apply type_prod; assumption.
   - destruct IHeq_type1 as [H_A1 H_A2].
      destruct IHeq_type2 as [H_B1 H_B2].
      split; apply type_func; assumption.
   - destruct IHeq_type as [H_A1 H_A2].
      apply eq_subs_coherence in H as [H_y1 H_y2].
      split. apply (type_subs H_y1 H_A1).
      apply (type_subs H_y2 H_A2).
   - split. apply (type_id H).
      assumption.
   - split.
      eapply type_subs; try eassumption.
      apply (subs_comp H H0).
      eapply type_subs; try eassumption.
      eapply type_subs; try eassumption.
   - split. apply (type_subs H); constructor; assumption.
      constructor; apply (type_subs H); assumption.
   - split. apply (type_subs H); constructor; assumption.
      constructor; apply (type_subs H); assumption.
Qed.

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as preType_mor.
Proof.
   intros A B Heq.
   apply eq_type_coherence in Heq as [H_A H_B].
   tauto.
Qed.


Theorem term_coherence {Γ A a}:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intros.
   dependent induction H.
   apply (type_weak H).
   apply type_prod; assumption.
   inversion IHTermJG; assumption.
   inversion IHTermJG; assumption.

   inversion IHTermJG; inversion H4; subst.
   apply (type_func H9 H).
   inversion IHTermJG2; assumption.
   apply (type_subs H IHTermJG).
   rewrite <- H0. assumption.
Qed.

Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_jug_eq_term_mor.
Proof.
   intros A B Heq e.
   split; intro; [ |symmetry in Heq] ; eapply type_fundation; eassumption.
Qed.


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
   apply (eq_type_coherence H_eq1).
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
   apply (eq_type_coherence H_eq1).
Qed.

Corollary term_id {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a [Id] @ A ].
Proof.
   intro H.
   apply term_coherence in H as H_A.
   rewrite <- (eq_type_subs_id H_A).
   apply type_coherence in H_A as H_ctx.
   apply (term_subs (subs_id H_ctx) H).
Qed.


Theorem eq_term_coherence :
   forall {Γ A a b}, [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
   intros Γ A a b Heq.
   dependent induction Heq.
   - tauto.
   - apply and_comm. assumption.
     (* apply (term_coherence H). *)
   - destruct IHHeq1 as [H_a1 H_a2].
      destruct IHHeq2 as [H_b1 H_b2].
      split; assumption.
   - destruct IHHeq1 as [H_a1 H_a2].
      destruct IHHeq2 as [H_b1 H_b2].
      split; apply term_pair; assumption.
   - destruct IHHeq as [H_b1 H_b2].
      apply term_coherence in H_b1 as H_B.
      split; apply term_abs; try assumption.
   - destruct IHHeq as [H_a1 H_a2].
      split. apply (term_subs H H_a1).
         apply (term_subs H H_a2).
   - split. apply (term_id H). apply H.
   - split.
      apply (term_subs (subs_comp H H0) H1).
      assert (H_eq : [ Γ2 ⊢ A [y0 ∘ y1] == A[y0] [y1] type]%ty).
         eapply eq_type_subs_comp; try eassumption.
         apply (term_coherence H1).
      rewrite H_eq.
         apply (term_subs H).
         apply (term_subs H0 H1).
   - split; [apply @term_fst with (B:=B); constructor | ]; eassumption.
   - split; [apply @term_snd with (A:=A); constructor | ]; eassumption.
   - split. assumption.
      constructor; econstructor; try eassumption.
   -  remember (type_coherence H) as HΓ.
      remember (term_coherence H1) as HA.
       split.
      econstructor; try eassumption.
      econstructor; assumption.
      remember (subs_id HΓ) as H_id.
      apply type_fundation with (B:= A[Id]%ty) in H1 as H_a.
      remember (subs_ext H_id HA H_a) as H_ext.
      apply (term_subs H_ext) in H0.
      apply (type_fundation _ _ _ _ H0).
      erewrite <- (eq_type_subs_comp).
      rewrite <- (eq_type_subs_id H) at 2.
      eapply eq_type_subs.
      eapply eq_subs_beta; eassumption.
      apply (eq_type_refl H).
      apply H_ext.
      apply subs_weak.
      assumption.
      assumption.
      symmetry.
      apply (eq_type_subs_id HA).
   -  split. assumption.
      remember (subs_weak H0) as H_weak.
      eapply term_abs.
      assumption.
      eapply term_app.
      eapply term_qar.
      assumption.
      eapply (type_subs H_weak H).
      apply (term_subs H_weak) in H1.
      apply (type_fundation _ _ _ _ H1).
      apply (eq_type_subs_func H_weak H0 H).
   - split. 2: assumption.
      apply (type_fundation _ (A [p][y#a])%ty ).
      eapply (term_subs).
      apply (subs_ext H H0 H1).
      apply (term_qar H0).
      erewrite <- (eq_type_subs_comp).
      eapply eq_type_subs.
      apply (eq_subs_beta H H0 H1).
      apply (eq_type_refl H0).
      apply (subs_ext H H0 H1).
      apply (subs_weak H0).
      assumption.
Qed.

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

(** End Notation Coherence **)

Lemma eq_type_prod_inversion Γ A B C D :
   [ Γ ⊢ A * B == C * D type ] -> [ Γ ⊢ A == C type ] /\ [ Γ ⊢ B == D type ].
Proof.
   intros H.
   dependent induction H.
   - inversion H.
   split; apply eq_type_refl; assumption.
   - specialize (IHeq_type C D A B eq_refl eq_refl).
      destruct IHeq_type as [H_AC H_BD].
      split; symmetry; assumption.
   -
Qed.

Lemma typing_unicity_subs Γ A B a:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ B ]
   -> [ Γ ⊢ A == B type ].
Proof.
   intro HA.
   dependent induction HA generalizing B; intros HB.
   - dependent induction HB; subst.
      apply eq_type_refl.
      econstructor.
      apply (subs_weak H).
      assumption.
      rewrite <- H0.
      apply IHHB.
      assumption.
      reflexivity.
      reflexivity.
   - dependent induction HB; subst.
      apply eq_type_prod.
      apply IHHA1; assumption.
      apply IHHA2; assumption.
      rewrite <- H.
      eapply IHHB; try(eassumption).
      reflexivity.
   - inversion HB; subst.
      specialize (IHHA _ H2) as IHeq.
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



