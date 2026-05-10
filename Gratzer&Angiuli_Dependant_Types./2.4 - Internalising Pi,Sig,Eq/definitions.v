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

with preSubs : Set :=
| psub_id   : preSubs
| psub_comp (y1 y2 : preSubs) : preSubs
| psub_weak : preSubs
| psub_Bang : preSubs
| psub_ext  (y : preSubs) (a : preTerm) : preSubs

with preType : Set :=
| ptyp_base : preType
| ptyp_prod (A B : preType) : preType
| ptyp_subs (A : preType) (y : preSubs) : preType
| ptyp_pi   (A : preType) (B : preType) : preType

with preTerm : Set :=
| ptrm_qar : preTerm
| ptrm_pair (a b : preTerm) : preTerm
| ptrm_fst  (p : preTerm) : preTerm
| ptrm_snd  (p : preTerm) : preTerm
| ptrm_subs (a : preTerm) (y : preSubs) : preTerm
| ptrm_dabs (b : preTerm) : preTerm
| ptrm_dapp (f a : preTerm) : preTerm
.
(** End Syntax definitions **)


(** Notations **)

Declare Scope ctx_scope.
Delimit Scope ctx_scope with ctx.
#[add_top] Bind Scope ctx_scope with preContext.

Declare Scope subs_scope.
Delimit Scope subs_scope with subs.
#[add_top] Bind Scope subs_scope with preSubs.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
#[add_top] Bind Scope ty_scope with preType.

Declare Scope term_scope.
Delimit Scope term_scope with term.
#[add_top] Bind Scope term_scope with preTerm.

Notation "1" := pctx_one : ctx_scope.
Notation "Γ # A" := (pctx_ext Γ A) (at level 2, left associativity) : ctx_scope.

Notation id        := psub_id.
Notation p         := psub_weak.
Notation "!"       := psub_Bang (at level 0) : subs_scope.
Notation "y1 ∘ y0" := (psub_comp y1 y0) (at level 100, right associativity) : subs_scope.
Notation "y # a"   := (psub_ext y a)(at level 2, left associativity) : subs_scope.

Notation b            := ptyp_base.
Notation "A * B"      := (ptyp_prod A B) (at level 40, left associativity): ty_scope.
Notation "A [ y ]"    := (ptyp_subs A y) (at level 1): ty_scope.
Notation "Π( A , B )" := (ptyp_pi A B) : ty_scope.

Notation q                 := ptrm_qar.
Notation "( a , b )"       := (ptrm_pair a b) (no associativity): term_scope.
Notation "'fst' p"         := (ptrm_fst p) (at level 60, right associativity): term_scope.
Notation "'snd' p"         := (ptrm_snd p) (at level 60, right associativity): term_scope.
Notation "a [ y ]"         := (ptrm_subs a y)(at level 1): term_scope.
Notation "'λ' ( b )"       := (ptrm_dabs b) (at level 20): term_scope.
Notation "'app' ( f , a )" := (ptrm_dapp f a) (at level 20): term_scope.

(** Unaxiomatic construction **)
Definition psub_ext_type (y : preSubs) (A : preType) : preSubs := (y ∘ p) # q .
Notation "y #! A" := (psub_ext_type y A)(at level 1, left associativity) : subs_scope.

Definition ptyp_func (A B : preType) : preType := Π(A, B [p]).
Notation "A -> B" := (ptyp_func A B) (at level 99, right associativity) : ty_scope.

Check (1)%ctx.
Check (1 # b)%ctx.

Check ( id ).
Check ( p ).
Check ( ! )%subs.
Check ( id ∘ p )%subs.
Check ( id#q )%subs.

Check (b).
Check (b * b -> b)%ty.
Check ( (b * b -> b) [ id ] )%ty.
Check ( b [ id ])%ty.

Check ( q ).
Check (q, q)%term.
Check ( fst ( q , q ) )%term.
Check ( snd ( q , q ) )%term.
Check ( q [ id ] )%term.
Check ( λ( q ) )%term.
Check ( app ( λ( q ) , q ) )%term.


Check ( id #! b )%subs.

(** End Notations **)

Reserved Notation "[ ⊢ Γ 'Cx' ]"          (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]"         (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y ~ Γ ]"         (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A == B 'type' ]" (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a == b @ A ]"    (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y == d ~ Γ ]"    (at level 0, no associativity).

(** Judgments **)
Inductive  ContextJG : preContext -> Prop :=
   | ctx_one :
      [ ⊢ 1 Cx ]
   | ctx_ext {Γ : preContext} {A : preType} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ A type ]
      -> [ ⊢  Γ # A Cx]

with SubsJG : preContext -> preContext -> preSubs -> Prop :=
   | subs_id {Γ} :
      [ ⊢ Γ Cx ]
      -> [ Γ ⊢ id ~ Γ ]
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
      -> [ Γ ⊢ b type ]
   | type_prod {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
      -> [ Γ ⊢ (A * B) type ]
   | type_subs {Δ Γ} {y} {A} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
      -> [ Δ ⊢ A [y] type ]
   (** Pi type p.36 **)
   | type_pi {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ]
      -> [ Γ ⊢ Π(A, B) type ]

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
   (** Pi type p.36 **)
   | term_dabs {Γ A B b} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ b @ B ]
      -> [ Γ ⊢ λ(b) @ (Π(A, B)) ]
   | term_dapp {Γ A B f a} :
   [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ f @ (Π(A, B)) ]
      -> [ Γ ⊢ app(f, a) @ B [id # a] ]
   | term_subs {Δ Γ} {y} {A} {a} :
      [ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
      -> [ Δ ⊢ (a [y]) @ A [y] ]
   (* TODO : Maybe provable using that 1 ⊢ A == B type, 1.A = 1.B, so A [Id] == B *)
   | term_conv {Γ} {A B} {e} :
      [ Γ ⊢ e @ A ] -> [ Γ ⊢ A == B type ]
      -> [ Γ ⊢ e @ B ]

(*** Equivalence Relations ***)
(**** Substitution Equivalence ****)
with eq_subs : preContext -> preContext -> preSubs -> preSubs -> Prop :=
(** Symmetric Transitive Closure **)
| eq_subs_sym {Δ Γ} {y1 y2} : [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y1 ~ Γ ]
| eq_subs_trans {Δ Γ} {y1 y2 y3} : [ Δ ⊢ y1 == y2 ~ Γ ] -> [ Δ ⊢ y2 == y3 ~ Γ ] -> [ Δ ⊢ y1 == y3 ~ Γ ]
(** Enforce composition properties (unital + associative) p.31 **)
| eq_subs_left_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ id ∘ y == y ~ Γ ]
| eq_subs_right_id {Δ Γ} {y}:
   [ Δ ⊢ y ~ Γ ] -> [ Δ ⊢ y ∘ id == y ~ Γ ]
| eq_subs_comp_assoc {Γ3 Γ2 Γ1 Γ0} {y0 y1 y2} :
   [ Γ3 ⊢ y2 ~ Γ2 ] -> [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0]
   -> [ Γ3 ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) ~ Γ0 ]
(** Constructor Rules **)
| eq_subs_comp {Γ2 Γ1 Γ0} {y d} {y' d'} :
   [ Γ1 ⊢ y == d ~ Γ0 ] -> [ Γ2 ⊢ y' == d' ~ Γ1 ]
   -> [ Γ2 ⊢ (y ∘ y') == (d ∘ d') ~ Γ0 ]
| eq_subs_ext {Δ Γ} {y d} {A a b} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Δ ⊢ a == b @ A [y] ]
   (* TODO: This could be derived from presuposition but this creates a loop *)
   -> [Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ] -> [ Δ ⊢ b @ A [d] ]
      -> [ Δ ⊢ (y # a) == (d # b) ~ (Γ # A) ]
(** βη-equivalence for substitution p.34 **)
| eq_subs_beta {Δ Γ A a y} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ p ∘ y # a == y ~ Γ ]
| eq_subs_eta {Δ Γ A y} :
   [ Γ ⊢ A type ] -> [ Δ ⊢ y ~ Γ # A ]
   -> [ Δ ⊢ y == (p ∘ y) # q[y] ~ (Γ # A) ]
(** Unicity of bang p.34 **)
| eq_subs_bang {Γ} {δ} :
   [ Γ ⊢ δ  ~ 1 ]
   -> [ Γ ⊢ ! == δ ~ 1 ]

(**** Type Equivalence ****)
with eq_type : preContext -> preType -> preType -> Prop :=
(** Symmetric Transitive Closure **)
| eq_type_sym {Γ} {A B} :  [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == A type ]
| eq_type_trans {Γ} {A B C} : [ Γ ⊢ A == B type ] -> [ Γ ⊢ B == C type ]   -> [ Γ ⊢ A == C type ]
(** Constructor Rules **)
| eq_type_prod {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A * B) == (C * D) type ]
| eq_type_pi {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ # A ⊢ B == D type ]
   -> [ Γ ⊢ Π(A, B) == Π(C, D) type ]
| eq_type_subs {Δ Γ} {y d} {A B} :
   [ Δ ⊢ y == d ~ Γ ] ->  [ Γ ⊢ A == B type ]
   -> [ Δ ⊢ A[y] == B[d] type ]
(** Compatibility with substitution p.32 **)
| eq_type_subs_id {Γ A} :
   [ Γ ⊢ A type ]
   -> [ Γ ⊢ A [id] == A type ]
| eq_type_subs_comp {Γ Γ1 Γ0} {A} {y1} {y0} :
   [ Γ ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ A type ]
   -> [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]
(** Substitution Distributivity *)
| eq_type_subs_prod {Δ Γ} {y} {A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A * B)[y] == (A[y] * B[y]) type ]
(** Pi type p.36 **)
| eq_type_pi_subs {Δ Γ y A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ]
   -> [ Δ ⊢ Π(A, B) [y] == Π(A[y], B[y #! A]) type ]%ty

(**** Term Equivalence ****)
with eq_term : preContext -> preType -> preTerm -> preTerm -> Prop :=
(** Symmetric Transitive Closure **)
| eq_term_sym {Γ A} {a b} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == a @ A ]
| eq_term_trans {Γ A} {a b c} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == c @ A ] -> [ Γ ⊢ a == c @ A ]
(** Constructor Rules **)
| eq_term_pair {Γ} {A B} {a b c d} :
  [ Γ ⊢ a == c @ A] -> [ Γ ⊢ b == d @ B ] -> [ Γ ⊢ (a, b) == (c, d) @ A * B ]
| eq_term_fst {Γ} {A B} {p q} :
   [ Γ ⊢ p == q @ A * B ] -> [ Γ ⊢ fst p == fst q @ A ]
| eq_term_snd {Γ} {A B} {p q} :
   [ Γ ⊢ p == q @ A * B ] -> [ Γ ⊢ snd p == snd q @ B ]
| eq_term_dabs {Γ} {A B} {a b} :
   [ Γ # A ⊢ a == b @ B ] -> [ Γ ⊢ λ(a) == λ(b) @ Π(A, B) ]
| eq_term_dapp  {Γ} {A B} {f g a b} :
   [ Γ ⊢ f == g @ Π(A, B) ] -> [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ app (f, a) == app (g, b) @ B [id#a] ]
| eq_term_subs {Δ Γ} {y d} {A} {a b} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ a == b @ A ]
   -> [ Δ ⊢ a [y] == b [d] @ A [y] ]
| eq_term_conv {Γ} {A B} {a b} :
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ A == B type ]
   -> [ Γ ⊢ a == b @ B ]
(** Compatibility with substitution p.32 **)
| eq_term_subs_id {Γ} {A a} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ id ] == a @ A ]
| eq_term_subs_comp {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1 ] == a [ y0 ] [ y1 ] @ A [y0 ∘ y1] ]
(** Substitution Distributivity **)
| eq_term_subs_pair {Δ Γ} {y} {A B} {a b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
   -> [ Δ ⊢ (a, b) [y] == (a [y], b [y]) @ A [y] * B [y] ]
|  eq_term_subs_fst {Δ Γ} {y} {A B} {p} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ p @ A * B ]
   -> [ Δ ⊢ (fst p) [y] == fst (p [y]) @ A [y]  ]
| eq_term_subs_snd {Δ Γ} {y} {A B} {p} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ p @ A * B ]
   -> [ Δ ⊢ (snd p) [y] == snd (p [y]) @ B [y] ]
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
(** βη-equivalence for substitution extension p.34 **)
| eq_term_beta_qar {Δ} {Γ} {y} {A} {a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ]
(** Pi type p.36 **)
| eq_term_subs_dabs {Δ Γ A B y b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] -> [ Γ # A ⊢ b @ B ]
   -> [ Δ ⊢ λ(b) [y] == λ(b[y #! A]) @ Π(A, B) [y] ]
| eq_term_subs_dapp { Δ Γ A B f a y } :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ f @ Π(A, B) ]
   -> [ Δ ⊢ app(f, a)[y] == app(f [y], a[y]) @ B[y # (a [y])] ]
(** βη-equivalence for dependent abstractions p.37 **)
| eq_term_beta_dapp {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ b @ B ]
   -> [ Γ ⊢ app( λ (b) , a ) == b [ id # a] @ B [id # a] ]
| eq_term_eta_dapp {Γ} {A B} {f} :
[ Γ ⊢ A type ] -> [ Γ # A ⊢ B type] -> [ Γ ⊢ f @  (Π(A, B)) ]
   -> [ Γ ⊢ f == (λ ( app(f [p], q))) @ (Π(A, B)) ]


where "[ ⊢ Γ 'Cx' ]"          := (ContextJG Γ)
and   "[ Γ ⊢ A 'type' ]"      := (TypeJG Γ A)
and   "[ Γ ⊢ a @ A ]"         := (TermJG Γ A a)
and   "[ Δ ⊢ y ~ Γ ]"         := (SubsJG Δ Γ y)
and   "[ Γ ⊢ A == B 'type' ]" := (eq_type Γ A B)
and   "[ Γ ⊢ a == b @ A ]"    := (eq_term Γ A a b)
and   "[ Δ ⊢ y == y' ~ Γ ]"   := (eq_subs Δ Γ y y')
.

(** End Jugements *)

(** Context Equality p.31, not sure what to do there **)
(** Idea, define a point-wise equality, but requires the rewrite the context as function, what function ? *)
Inductive eq_ctx : preContext -> preContext -> Prop :=
| eq_ctx_step {Γ} : [ ⊢ Γ Cx ] -> eq_ctx Γ Γ
| eq_ctx_ext {Γ A B} : eq_ctx Γ Γ -> [ Γ ⊢ A == B type ] -> eq_ctx (Γ # A) (Γ # B).
(** End Context Equality **)

Example Ex1 : ([1 ⊢ b * b -> b type ]).
Proof.
   set ctx_one as Hc.
   apply type_base in Hc as Hb.
   apply (type_prod Hb) in Hb as Hp.
   apply (type_pi Hp).
   apply (type_subs (subs_weak Hp) Hb).
Qed.

(** Setoid declarations **)
(*** Register equivalence relations ***)
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
(**** End relations registration ****)

(*** Fundamental property ***)
Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_jug_eq_type_mor.
Proof.
   intros A B Heq e.
   split; intro; [ | symmetry in Heq];
   apply (term_conv H Heq).
Qed.

(** Bug ? **)
Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> Basics.flip Basics.impl)
   as term_jug_eq_type_mor2.
Proof.
   intros A B Heq e H.
   symmetry in Heq.
   apply (term_conv H Heq).
Qed.

Add Parametric Morphism Γ : (eq_term Γ)
   with signature (eq_type Γ ==> eq ==> eq ==> iff)
   as eq_term_eq_type_mor.
Proof.
   intros A B Heq a b.
   split; intro; [ | symmetry in Heq];
   apply (eq_term_conv H Heq).
Qed.

Corollary subs_ext_type {Δ Γ y A} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ # A[y] ⊢ (y #! A) ~ (Γ # A) ].
Proof.
   intros Hsub Htype.
   unfold psub_ext_type.
   apply (subs_ext
      (subs_comp (subs_weak (type_subs Hsub Htype)) Hsub)
      Htype
      ).
   rewrite (eq_type_subs_comp
       (subs_weak (type_subs Hsub Htype)) Hsub Htype).
   apply (term_qar (type_subs Hsub Htype)).
Qed.
(** End Fundamental property **)

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

(** Construction helpers **)
Lemma eq_subs_comp_l {Γ2 Γ1 Γ0} {y d} {y'} :
   [ Γ1 ⊢ y == d ~ Γ0 ] -> [ Γ2 ⊢ y' ~ Γ1 ]
   -> [ Γ2 ⊢ (y ∘ y') == (d ∘ y') ~ Γ0 ].
Proof.
   intros Heq H.
   apply (eq_subs_comp Heq (eq_subs_refl H)).
Qed.
Lemma eq_subs_comp_r {Γ2 Γ1 Γ0} {y} {y' d'} :
   [ Γ1 ⊢ y ~ Γ0 ] -> [ Γ2 ⊢ y' == d' ~ Γ1 ]
   -> [ Γ2 ⊢ (y ∘ y') == (y ∘ d') ~ Γ0 ].
Proof.
   intros H Heq.
   apply (eq_subs_comp (eq_subs_refl H) Heq).
Qed.
Lemma eq_subs_ext_S {Δ Γ} {y d} {A a } :
   [ Δ ⊢ y == d ~ Γ ] -> [Γ ⊢ A type] -> [ Δ ⊢ a @ A [y] ]
      -> [ Δ ⊢ (y # a) == (d # a) ~ (Γ # A) ].
Proof.
   intros Heq H Ha.
   apply (eq_subs_ext Heq (eq_term_refl Ha) H Ha).
   apply (term_conv Ha).
   apply (eq_type_subs Heq (eq_type_refl H)).
Qed.

Lemma eq_type_prod_l {Γ} {A B D} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A * B) == (A * D) type ].
Proof.
   intros H Heq.
   apply (eq_type_prod (eq_type_refl H) Heq).
Qed.
Lemma eq_type_prod_r {Γ} {A B C} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B type ]
   -> [ Γ ⊢ (A * B) == (C * B) type ].
Proof.
   intros Heq H.
   apply (eq_type_prod Heq (eq_type_refl H)).
Qed.
Lemma eq_type_subs_S {Δ Γ} {y d} {A}
   : [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ A[y] == A[d] type ].
Proof.
   intros Heq H.
   apply (eq_type_subs Heq (eq_type_refl H)).
Qed.
Lemma eq_type_subs_T {Δ Γ} {y} {A B}
   : [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A  == B type ] -> [ Δ ⊢ A[y] == B[y] type ].
Proof.
   intros H Heq.
   apply (eq_type_subs (eq_subs_refl H) Heq).
Qed.
Lemma eq_term_pair_l {Γ} {A B} {a b d} :
  [ Γ ⊢ a @ A] -> [ Γ ⊢ b == d @ B ] -> [ Γ ⊢ (a, b) == (a, d) @ A * B ].
Proof.
   intros H Heq.
   apply (eq_term_pair (eq_term_refl H) Heq).
Qed.
Lemma eq_term_pair_r {Γ} {A B} {a b c} :
   [ Γ ⊢ a == c @ A] -> [ Γ ⊢ b @ B ] -> [ Γ ⊢ (a, b) == (c, b) @ A * B ].
Proof.
   intros Heq H.
   apply (eq_term_pair Heq (eq_term_refl H)).
Qed.
Lemma eq_term_subs_S {Δ Γ} {y d} {A} {a} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ a @ A ]
   -> [ Δ ⊢ a [y] == a [d] @ A [y] ].
Proof.
   intros Heq H.
   apply (eq_term_subs Heq (eq_term_refl H)).
Qed.
Lemma eq_term_subs_T {Δ Γ} {y} {A} {a b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a == b @ A ] -> [ Δ ⊢ a [y] == b [y] @ A [y] ].
Proof.
   intros H Heq.
   apply (eq_term_subs (eq_subs_refl H) Heq).
Qed.

(*** Rewriting under construction ***)
Add Parametric Morphism Γ2 Γ1 Γ0 : psub_comp with
   signature (eq_subs Γ1 Γ0 ==> eq_subs Γ2 Γ1 ==> eq_subs Γ2 Γ0)
as eq_subs_comp_mor.
Proof.
   intros y d Heq y' d' Heq'.
   apply (eq_subs_comp Heq Heq').
Qed.
(** Requires eq_term_press **)
Add Parametric Morphism Δ Γ A y (H : [Δ ⊢ y ~ Γ]) : (psub_ext y) with
   signature (eq_term Δ (A [y]) ==> eq_subs Δ (Γ # A))
as eq_subs_ext_mor.
Proof.
   intros a b Heq.
   (* apply (eq_subs_ext (eq_subs_refl H) Heq). *)
Abort.

Add Parametric Morphism Γ : ptyp_prod with
   signature (eq_type Γ ==> eq_type Γ ==> eq_type Γ)
as eq_type_prod_mor.
Proof.
   intros A B Heq C D Heq'.
   apply (eq_type_prod Heq Heq').
Qed.
(* Add Parametric Morphism Γ : ptyp_pi with
   signature (eq_type Γ ==> eq_type Γ ==> eq_type Γ)
as eq_type_pi_mor.
Proof.
   intros A B Heq C D Heq'.
   apply (eq_type_pi Heq Heq').
Qed. *)
Add Parametric Morphism Δ Γ : (ptyp_subs) with
   signature  (eq_type Γ ==> eq_subs Δ Γ ==> eq_type Δ)
as eq_type_subs_mor.
Proof.
   intros A B Heq y d Heq'.
   apply (eq_type_subs Heq' Heq).
Qed.
Add Parametric Morphism Δ Γ A (H : [Γ ⊢ A type ]) : (ptyp_subs A) with
   signature  (eq_subs Δ Γ ==> eq_type Δ)
as eq_type_subs_mor2.
Proof.
   intros y d Heq'.
   apply (eq_type_subs_S Heq' H).
Qed.

Add Parametric Morphism Γ A B : ptrm_pair with
   signature (eq_term Γ A ==> eq_term Γ B ==> eq_term Γ (A * B))
as eq_term_pair_mor.
Proof.
   intros a c Heq b d Heq'.
   apply (eq_term_pair Heq Heq').
Qed.
Add Parametric Morphism Γ A B : ptrm_fst with
   signature (eq_term Γ (A * B) ==> eq_term Γ A)
as eq_term_fst_mor.
Proof.
   intros p q Heq.
   apply (eq_term_fst Heq).
Qed.
Add Parametric Morphism Γ A B : ptrm_snd with
   signature (eq_term Γ (A * B) ==> eq_term Γ B)
as eq_term_snd_mor.
Proof.
   intros p q Heq.
   apply (eq_term_snd Heq).
Qed.
Add Parametric Morphism Γ A B : ptrm_dabs with
   signature (eq_term (Γ # A) B ==> eq_term Γ ( Π(A, B) ) )
as eq_term_dabs_mor.
Proof.
   intros a b Heq.
   apply (eq_term_dabs Heq).
Qed.
Add Parametric Morphism Γ A B : ptrm_dapp with
   signature (eq_term Γ (Π(A, B)) ==> eq_term Γ A ==> eq_term Γ B)
as eq_term_dapp_mor.
Proof.
   intros f g Heq a b Heq'.
   (* apply (eq_term_dapp Heq Heq'). *)
Abort.
Add Parametric Morphism Δ Γ A y (H : [Δ ⊢ y ~ Γ]) : (fun a => ptrm_subs a y) with
   signature (eq_term Γ A ==> eq_term Δ A[y])
as eq_term_subs_mor.
Proof.
   intros a b Heq.
   apply (eq_term_subs_T H Heq).
Qed.
(** End Rewriting **)


(*** "Presupositions" Theorems ***)
Theorem type_press {Γ A}:
   [ Γ ⊢ A type ] -> [ ⊢ Γ Cx ].
Proof.
   intros.
   dependent induction H; try (tauto).
   dependent induction H generalizing A; intros; try (tauto).
   - apply (IHSubsJG1 _ (type_subs H0 H1)
            (IHSubsJG2 A H1 IHTypeJG )).
   - apply (ctx_ext IHTypeJG H).
   - inversion IHTypeJG; subst.
      apply (IHSubsJG A0 H0 H5).
Qed.

(**** helper ****)
Corollary type_weak {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ # A ⊢ A [p] type ].
Proof. apply (fun H => type_subs (subs_weak H) H). Qed.

Corollary type_id {Γ A} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ A [id] type ].
Proof. apply (fun H => type_subs  (subs_id (type_press H)) H). Qed.

Corollary type_ctx_ext {Γ A} :
   [ Γ ⊢ A type ] -> [ ⊢ Γ # A Cx ].
Proof. apply (fun H => ctx_ext (type_press H) H). Qed.
(**** End Helpers ****)

Theorem subs_press_l {Δ Γ y}:
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Δ Cx ].
Proof.
   intros.
   dependent induction H; try(tauto).
   apply (ctx_ext (type_press H) H).
Qed.

Theorem subs_press_r {Δ Γ y}:
   [ Δ ⊢ y ~ Γ ] -> [ ⊢ Γ Cx ].
Proof.
   intros.
   dependent induction H; try(tauto).
   apply (type_press H).
   apply (ctx_one).
   apply (ctx_ext IHSubsJG H0).
Qed.

Theorem eq_subs_press {Δ Γ y1 y0}:
   [ Δ ⊢ y1 == y0 ~ Γ ] -> [ Δ ⊢ y1 ~ Γ ] /\ [ Δ ⊢ y0 ~ Γ ].
Proof.
   intros.
   dependent induction H; try (tauto).
   -  split. 2:assumption.
      apply (subs_comp H (subs_id (subs_press_r H))).
   -  split. 2:assumption.
      apply (subs_comp (subs_id (subs_press_l H)) H).
   -  split.
      apply (subs_comp (subs_comp H H0) H1).
      apply (subs_comp H (subs_comp H0 H1)).
   - destruct IHeq_subs1, IHeq_subs2.
      split; eapply (subs_comp); eassumption.
   - destruct IHeq_subs.
       split.
       eapply (subs_ext H4 H1 H2).
       eapply (subs_ext H5 H1 H3).
   -  split. 2:assumption.
      apply (subs_comp
         (subs_ext H H0 H1)
         (subs_weak H0)).
   -  split. assumption.
      apply (subs_ext (subs_comp H0 (subs_weak H)) H).
      rewrite (eq_type_subs_comp H0 (subs_weak H) H).
      apply (term_subs H0 (term_qar H)).
   - split. 2:assumption.
      apply (subs_bang (subs_press_l H)).
Qed.

Add Parametric Morphism Δ Γ : (SubsJG Δ Γ)
   with signature (eq_subs Δ Γ ==> iff)
   as subs_mor.
Proof.
   intros y d Heq.
   apply eq_subs_press in Heq as [H_y H_d].
   tauto.
Qed.


Theorem eq_type_press :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ] /\ [ Γ ⊢ B type ].
Proof.
   intros.
   dependent induction H; try (tauto).
   - destruct IHeq_type1, IHeq_type2.
      split; eapply (type_prod); assumption.
   - destruct IHeq_type1, IHeq_type2.
      split; eapply (type_pi); try assumption.
      admit.
   -  destruct IHeq_type.
      apply (eq_subs_press) in H as [H_y H_d].
      split; eapply (type_subs); eassumption.
   - split; [apply (type_id H) | apply H].
   - split.
      apply (type_subs (subs_comp H H0) H1).
      apply (type_subs H (type_subs H0 H1)).
   - split.
      apply (type_subs H (type_prod H0 H1)).
      apply (type_prod (type_subs H H0) (type_subs H H1)).
   - split.
      apply (type_subs H (type_pi H0 H1)).
      apply (type_pi (type_subs H H0)).
      apply (type_subs (subs_ext_type H H0) H1).
Admitted.

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as preType_mor.
Proof.
   intros A B Heq.
   apply eq_type_press in Heq.
   tauto.
Qed.


Theorem term_press {Γ A a}:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intros H.
   dependent induction H.
   apply (type_subs (subs_weak H) H).
   apply type_prod; [apply IHTermJG1 | apply IHTermJG2].
   inversion IHTermJG; assumption.
   inversion IHTermJG; assumption.
   apply (type_pi H IHTermJG).
   apply (type_subs
      (subs_ext (subs_id (type_press IHTermJG1))
         IHTermJG1
         (term_conv H (eq_type_sym (eq_type_subs_id IHTermJG1))))
      H0).
   apply (type_subs H IHTermJG).
   apply (eq_type_press H0).
Qed.

Corollary term_press_ctx {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ ⊢ Γ Cx ].
Proof. apply (fun H => type_press (term_press H)). Qed.


Corollary term_id {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a [id] @ A ].
Proof.
   intro H.
   rewrite <- (eq_type_subs_id (term_press H)).
   apply (term_subs (subs_id (term_press_ctx H)) H).
Qed.

Corollary term_subs_compose {Δ Γ A a y1 y0} :
   [ Δ ⊢ y0 ~ Γ ]
   -> [ Γ ⊢ a @ A [y1] ]
   -> [ Δ ⊢ a [y0] @ A [y1 ∘ y0] ].
Proof.
   intros H_y0 H_a.
   remember (term_press H_a) as HA.
   inversion HA; subst.
   rewrite (eq_type_subs_comp H_y0 H2 H3).
   apply (term_subs H_y0 H_a).
Qed.

Corollary term_id_type {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a @ A [id] ].
Proof.
   intro H.
   rewrite (eq_type_subs_id (term_press H)).
   apply H.
Qed.

Corollary self_extension {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ (id # a) ~ (Γ # A) ].
Proof.
   intro H.
   apply (subs_ext
            (subs_id (term_press_ctx H))
            (term_press H)
            (term_id_type H)).
Qed.

Corollary eq_subs_beta_id {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ p ∘ (id # a) == id ~ Γ ].
Proof.
   intro H.
   apply (eq_subs_beta
         (subs_id (term_press_ctx H))
         (term_press H)
         (term_id_type H)).
Qed.

Add Parametric Morphism Δ Γ A a (H:[ Γ ⊢ a @ A ]) : (fun y => psub_ext y (ptrm_subs a y)) with
   signature (eq_subs Δ Γ ==> eq_subs Δ (Γ#A))
as eq_subs_ext_mor.
Proof.
   intros y d Heq.
   apply (eq_subs_ext Heq).
   apply (eq_term_subs_S Heq H).
   apply (term_press H).
   all:apply eq_subs_press in Heq as [H_y H_d].
   apply (term_subs H_y H).
   apply (term_subs H_d H).
Qed.

Lemma Exercise_2_3 {Γ2 Γ1 Γ0 A a y δ} :
[ Γ1 ⊢ y ~ Γ0 ] -> [ Γ2 ⊢ δ ~ Γ1 ] -> [ Γ0 ⊢ A type ] -> [ Γ1 ⊢ a @ A[y] ]
-> [ Γ2 ⊢ (y # a) ∘ δ == (y ∘ δ) # a [δ] ~ Γ0 # A ].
Proof.
intros H_y H_δ H_A H_a.
   rewrite (eq_subs_eta H_A).
      assert([ Γ2 ⊢ p ∘ (y#a ∘ δ) == y ∘ δ ~ Γ0 ]).
      {
         rewrite (eq_subs_comp_assoc H_δ (subs_ext H_y H_A H_a) (subs_weak H_A)).
         eapply (eq_subs_comp_l (eq_subs_beta H_y H_A H_a) H_δ).
      }
      apply (eq_subs_ext H).
      rewrite (eq_type_subs_comp (subs_comp H_δ (subs_ext H_y H_A H_a)) (subs_weak H_A) H_A).
      rewrite (eq_term_subs_comp H_δ (subs_ext H_y H_A H_a) (term_qar H_A)).
      rewrite (eq_type_subs_comp H_δ (subs_ext H_y H_A H_a) (type_subs(subs_weak H_A) H_A)).
      apply (eq_term_subs_T H_δ).
      rewrite <- (eq_type_subs_comp (subs_ext H_y H_A H_a) (subs_weak H_A) H_A).
      rewrite (eq_type_subs_S (eq_subs_beta H_y H_A H_a) H_A).
      apply (eq_term_beta_qar H_y H_A H_a).
      apply H_A.
      rewrite (eq_type_subs_comp (subs_comp H_δ (subs_ext H_y H_A H_a)) (subs_weak H_A) H_A).
      apply (term_subs (subs_comp H_δ (subs_ext H_y H_A H_a)) (term_qar H_A)).
      apply (term_subs_compose H_δ H_a).
      apply (subs_comp H_δ (subs_ext H_y H_A H_a)).
Qed.

Lemma eq_subs_eta_id {Γ A} :
   [ Γ ⊢ A type ] ->
   [ Γ # A ⊢ id == p # q ~ Γ # A ].
Proof.
   intros HA.
   apply (subs_weak) in HA as Hw.
   rewrite (eq_subs_eta HA (subs_id (type_ctx_ext HA))).
   apply (eq_subs_ext (eq_subs_right_id Hw)).
   apply (eq_term_subs_id).
   rewrite (eq_type_subs_comp (subs_id (type_ctx_ext HA)) Hw HA).
   rewrite (eq_type_subs_id (type_subs Hw HA)).
   apply (term_qar HA).
   apply HA.
   apply (term_subs_compose (subs_id (type_ctx_ext HA)) (term_qar HA)).
   apply (term_qar HA).
Qed.

Lemma eq_subs_eta_id_type {Γ A} :
   [ Γ ⊢ A type ] ->
   [ Γ # A # A[p] ⊢ p #! A == p #! A ∘ p # q ~ Γ # A ].
Proof.
   intros HA.
   rewrite <- (eq_subs_right_id (subs_ext_type (subs_weak HA) HA)) at 1.
   apply (eq_subs_comp_r (subs_ext_type (subs_weak HA) HA)).
   apply eq_subs_eta_id.
   apply (type_weak HA).
Qed.

Lemma eq_subs_ext_type_beta {Δ Γ y A} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
   -> [Δ # A [y] ⊢ p ∘ y #! A == y ∘ p ~ Γ].
Proof.
   intros Hsub Htype.
   unfold psub_ext_type.
   apply (type_subs Hsub) in Htype as HA.
   apply (subs_weak) in HA as Hw.
   apply (subs_comp Hw) in Hsub as Hy.
   apply (eq_subs_beta Hy Htype).
   rewrite (eq_type_subs_comp Hw Hsub Htype).
   apply (term_qar HA).
Qed.



Theorem eq_term_press {Γ A a b}:
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   - destruct IHHeq1, IHHeq2.
       split; eapply (term_pair); eassumption.
   - destruct IHHeq.
         split; eapply (term_fst); eassumption.
   - destruct IHHeq.
         split; eapply (term_snd); eassumption.
   - destruct IHHeq. apply term_press_ctx in H as H1.
          inversion H1; subst.
         split; eapply (term_dabs); eassumption.
   - destruct IHHeq1, IHHeq2.
         apply term_press in H as Hpi.
         inversion Hpi; subst.
         split. eapply (term_dapp H1); eassumption.
         rewrite (eq_type_subs_S
            (eq_subs_ext
               (eq_subs_refl (subs_id (type_press H6)))
               (eq_term_conv Heq2 (eq_type_sym (eq_type_subs_id H6)))
               H6 (term_id_type H1) (term_id_type H2)) H7).
         apply (term_dapp H2); eassumption.
   - destruct IHHeq.
         apply eq_subs_press in H as H2.
         destruct H2 as [Hy Hd].
         split. apply (term_subs Hy H0).
         rewrite (eq_type_subs_S H (term_press H0)).
         apply (term_subs Hd H1).
   - destruct IHHeq.
       split; rewrite <- H; assumption.
   - split; [apply (term_id H) | apply H].
   - split.
      apply (term_subs (subs_comp H H0) H1).
      rewrite (eq_type_subs_comp H H0 (term_press H1)).
      apply (term_subs H (term_subs H0 H1)).
   - split.
      rewrite <- (eq_type_subs_prod H (term_press H0) (term_press H1)).
      apply (term_subs H (term_pair H0 H1)).
      apply (term_pair (term_subs H H0) (term_subs H H1)).
   - split.
      apply (term_subs H (term_fst H0)).
      apply term_press in H0 as H1.
      inversion H1; subst.
      apply (term_subs H) in H0 .
      rewrite (eq_type_subs_prod H H5 H6) in H0.
      apply (term_fst H0).
   - split.
      apply (term_subs H (term_snd H0)).
      apply term_press in H0 as H1.
      inversion H1; subst.
      apply (term_subs H) in H0 .
      rewrite (eq_type_subs_prod H H5 H6) in H0.
      apply (term_snd H0).
   - split; [apply (term_fst (term_pair H H0)) | apply H].
   - split; [apply (term_snd (term_pair H H0)) | apply H0].
   - split; [apply H | apply ( term_pair (term_fst H) (term_snd H))].
   - split.
      apply (subs_ext H H0) in H1 as H2.
      apply (eq_subs_beta H H0) in H1 as H3.
      rewrite <- (eq_type_subs_S H3 H0).
      rewrite (eq_type_subs_comp H2 (subs_weak H0) H0).
      apply (term_subs H2 (term_qar H0)).
      apply (H1).
   - split.
      apply (term_subs H (term_dabs H0 H2)).
      rewrite (eq_type_pi_subs H H0 H1).
      apply (term_dabs (type_subs H H0)).
      apply (term_subs (subs_ext_type H H0) H2).
   (* Exercise 2.6 *)
   -  remember (subs_id (subs_press_r H)) as id_subs.
      remember (term_press H0) as HA.
      remember (Exercise_2_3 id_subs H HA (term_id_type H0)) as H3.
      clear HeqH3.
      rewrite (eq_subs_ext_S (eq_subs_left_id H) HA (term_subs_compose H (term_id_type H0))) in H3.
      split.
      rewrite <- (eq_type_subs_S H3 H1).
      rewrite (eq_type_subs_comp H (self_extension H0) H1).
      apply (term_subs H).
      apply (term_dapp H0 H1 H2).
      remember (term_qar (type_subs H HA)) as Hq.
      clear HeqHq.
      rewrite <- (eq_type_subs_comp (subs_weak (type_subs H HA)) H HA) in Hq.
      remember (Exercise_2_3 (subs_comp (subs_weak (type_subs H HA)) H)
         (self_extension (term_subs H H0)) HA Hq) as H4.
         clear HeqH4.
      remember (eq_subs_sym (eq_subs_comp_assoc
               (self_extension (term_subs H H0))
               (subs_weak (type_subs H HA)) H)) as H5.
         clear HeqH5.
      rewrite (eq_subs_comp_r H (
         eq_subs_beta (subs_id (subs_press_l H))
                     (type_subs H HA)
                     (term_id_type (term_subs H H0))
                     )) in H5.
      rewrite (eq_subs_right_id H) in H5.
      remember (eq_term_beta_qar (subs_id (subs_press_l H)) (type_subs H HA) (term_id_type (term_subs H H0))) as H6.
         clear HeqH6.
      rewrite (eq_type_subs_id (type_subs H HA)) in H6.
      rewrite <- (eq_subs_ext
                     (eq_subs_sym H5)
                     (eq_term_sym H6)
                     HA
                     (term_subs H H0)
               ) in H4.
      rewrite <- (eq_type_subs_S H4 H1).
      rewrite (eq_type_subs_comp (self_extension (term_subs H H0)) (subs_ext (subs_comp (subs_weak (type_subs H HA)) H) HA Hq) H1).
      apply (term_dapp (term_subs H H0) (type_subs (subs_ext_type H HA) H1)).
      rewrite <- (eq_type_pi_subs H HA H1).
      apply (term_subs H H2).
      rewrite (eq_type_subs_comp (self_extension (term_subs H H0)) (subs_comp (subs_weak (type_subs H HA)) H) HA).
      apply (term_subs (self_extension (term_subs H H0)) Hq).
   - split.
      apply (term_dapp H (term_press H0) (term_dabs (term_press H) H0)).
      apply (term_subs (self_extension H) H0).
   (* Exercise 2.7 *)
   - split. assumption.
      apply (term_dabs H).
      apply (term_subs (subs_weak H)) in H1 as H2.
      rewrite (eq_type_pi_subs (subs_weak H) H H0) in H2.
      apply (term_dapp (term_qar H) (type_subs (subs_ext_type (subs_weak H) H) H0)) in H2.
      rewrite <- (eq_type_subs_id H0).
      rewrite <- (eq_type_subs_comp (self_extension (term_qar H)) (subs_ext_type (subs_weak H) H) H0) in H2.
      apply(term_conv H2).
      remember (term_qar (type_weak H)) as Hq.
      clear HeqHq.
      rewrite <- (eq_type_subs_comp (subs_weak (type_weak H)) (subs_weak H) H) in Hq.
      remember (Exercise_2_3 (subs_comp (subs_weak (type_weak H)) (subs_weak H)) (self_extension (term_qar H)) H Hq) as H3.
      clear HeqH3.
      remember (eq_term_beta_qar (subs_id (type_press H0)) (type_weak H) (term_id_type (term_qar H))) as H4.
      clear HeqH4.
      remember (eq_subs_comp_assoc (self_extension (term_qar H)) (subs_weak (type_weak H)) (subs_weak H)) as H5.
      clear HeqH5.
      rewrite (eq_subs_comp_r (subs_weak H) (eq_subs_beta_id (term_qar H))) in H5.
      rewrite (eq_subs_right_id (subs_weak H)) in H5.
      symmetry in H4.
      rewrite (eq_type_subs_id (type_weak H)) in H4.
      rewrite <- (eq_subs_ext H5 H4 H (term_qar H)) in H3.
      rewrite <- (eq_subs_eta_id H) in H3.
      apply (eq_type_subs_S H3 H0).
      apply (term_subs_compose (self_extension (term_qar H)) Hq).
Qed.

Add Parametric Morphism Γ A : (TermJG Γ A)
   with signature (eq_term Γ A ==> iff)
   as term_jug_eq_term_mor.
Proof.
   intros a b Heq.
   apply eq_term_press in Heq.
   tauto.
Qed.

Corollary eq_subs_ext2 {Δ Γ} {y d} {A a b} :
   [ Δ ⊢ y == d ~ Γ ] -> [Γ ⊢ A type] -> [ Δ ⊢ a == b @ A [y] ]
   -> [ Δ ⊢ y # a == d # b ~ Γ # A ].
Proof.
   intros Heq HA Heq'.
   apply eq_term_press in Heq' as Hab.
   destruct Hab as [Ha Hb].
   rewrite (eq_type_subs_S Heq HA) in Hb.
   apply (eq_subs_ext Heq Heq' HA Ha Hb).
Qed.
(** End "Presupositions" Theorems **)

(** Exercises **)
(** Proove formation and elimination of non-axiomatic contructors **)
Lemma type_func {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
      -> [ Γ ⊢ A -> B type ].
Proof.
   intros HtypeA HtypeB.
   apply (type_pi HtypeA).
   apply (type_subs (subs_weak HtypeA) HtypeB).
Qed.
Lemma term_abs {Γ A B b} :
      [ Γ # A ⊢ b @ B [p] ]
      -> [ Γ ⊢ λ(b) @ (A -> B) ].
Proof.
   intros H.
   apply term_press_ctx in H as H_ctx.
   inversion H_ctx; subst.
   apply (term_dabs H3 H).
Qed.

Lemma term_app {Γ A B f a} :
      [ Γ ⊢ f @ (A -> B) ] -> [ Γ ⊢ a @ A ]
      -> [ Γ ⊢ app (f, a) @ B ].
Proof.
   intros Hf Ha.
   apply term_press in Hf as Hf_type.
   inversion Hf_type; subst.
   apply (term_dapp Ha H3) in Hf as H4.
   inversion H3; subst.
   inversion H5; subst.
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak H2) H6) in H4.
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) H6) in H4.
   rewrite (eq_type_subs_id H6) in H4.
   apply H4.
Qed.


Lemma eq_term_abs {Γ} {A B} {a b} :
   [ Γ # A ⊢ a == b @ B [p] ] -> [ Γ ⊢ λ(a) == λ(b) @ A -> B ].
Proof.
   intros Heq.
   apply (eq_term_dabs Heq).
Qed.
Lemma eq_term_app  {Γ} {A B} {f g a b} :
   [ Γ ⊢ f == g @ A -> B ] -> [ Γ ⊢ a == b @ A ]
   -> [ Γ ⊢ app (f, a) == app (g, b) @ B ].
Proof.
   intros Heq_f Heq_a.
   apply eq_term_press in Heq_f as Hfg.
   destruct Hfg as [Hf Hg].
   apply term_press in Hf as Hf_type.
   inversion Hf_type; subst.
   inversion H3; subst.
   inversion H4; subst.
   apply (eq_term_dapp Heq_f) in Heq_a as H1.
   apply eq_term_press in Heq_a as Hab.
   destruct Hab as [Ha Hb].
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak H2) H5) in H1.
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) H5) in H1.
   rewrite (eq_type_subs_id H5) in H1.
   apply H1.
Qed.

Lemma eq_term_subs_app {Δ Γ} {y} {A B} {f a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ f @ A -> B ] -> [ Γ ⊢ a @ A ]
   -> [ Δ ⊢ app (f, a) [y] == app (f [y], a [y]) @ B[y] ].
Proof.
   intros Hsub Hf Ha.
   apply term_press in Hf as Hf_type.
   inversion Hf_type; subst.
   apply (eq_term_subs_dapp Hsub Ha H3 ) in Hf as H1.
   inversion H3; subst.
   inversion H5; subst.
   rewrite <- (eq_type_subs_comp (subs_ext Hsub H2 (term_subs Hsub Ha)) (subs_weak H2) H6) in H1.
   rewrite (eq_type_subs_S (eq_subs_beta Hsub H2 (term_subs Hsub Ha)) H6) in H1.
   exact H1.
Qed.


Lemma eq_type_func {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A -> B) == (C -> D) type ].
Proof.
   intros HAC HBD.
   apply (eq_type_pi HAC).
   apply eq_type_press in HAC as [HA HC].
   apply (eq_type_subs_T (subs_weak HA) HBD).
Qed.

Lemma eq_type_subs_func {Δ Γ} {y} {A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A -> B)[y] == (A[y] -> B[y]) type ].
Proof.
   intros Hsub HA HB.
   apply (type_subs (subs_weak HA)) in HB as HS.
   rewrite (eq_type_pi_subs Hsub HA HS).
   apply (eq_type_pi (eq_type_refl (type_subs Hsub HA))).
   rewrite <- (eq_type_subs_comp (subs_ext_type Hsub HA) (subs_weak HA) HB).
   rewrite <- (eq_type_subs_comp (subs_weak (type_subs Hsub HA)) Hsub HB).
   eapply (eq_type_subs_S (eq_subs_ext_type_beta Hsub HA) HB).
Qed.

Lemma eq_type_func_l {Γ} {A B D} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ B == D type ]
   -> [ Γ ⊢ (A -> B) == (A -> D) type ].
Proof.
   intros H Heq.
   apply (eq_type_func (eq_type_refl H) Heq).
Qed.
Lemma eq_type_func_r {Γ} {A B C} :
   [ Γ ⊢ A == C type ] -> [ Γ ⊢ B type ]
   -> [ Γ ⊢ (A -> B) == (C -> B) type ].
Proof.
   intros Heq H.
   apply (eq_type_func Heq (eq_type_refl H)).
Qed.
(** βη-equivalence for abstractions p.22 **)
Lemma eq_term_beta_app {Γ} {A B} {a b} :
   [ Γ # A ⊢ b @ B[p] ] -> [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ app (λ(b), a) == b [ id # a] @ B ].
Proof.
   intros H_b H_a.
   apply (term_press) in H_b as H_type.
   inversion H_type; subst.
   inversion H2; subst.
   apply (eq_term_beta_dapp H_a) in H_b as HS.
   rewrite <- (eq_type_subs_comp (self_extension H_a) (subs_weak H4) H3) in HS.
   rewrite (eq_type_subs_S (eq_subs_beta_id H_a) H3) in HS.
   rewrite (eq_type_subs_id H3) in HS.
   apply HS.
Qed.

Lemma eq_term_eta_app {Γ} {A B} {f} :
   [ Γ ⊢ f @ (A -> B) ]
   -> [ Γ ⊢ f == λ(app (f [p], q)) @ (A -> B) ].
Proof.
   intros Hf.
   apply (term_press) in Hf as Hf_type.
   inversion Hf_type; subst.
   apply (eq_term_eta_dapp H2 H3 Hf).
Qed.

Lemma eq_term_subs_abs {Δ Γ} {y} {A B} {b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ # A ⊢ b @ B [p] ]
   -> [ Δ ⊢ λ(b) [y] == λ(b [(y ∘ p)#q]) @ A[y] -> B[y] ].
Proof.
   intros Hsub Hb.
   apply (term_press) in Hb as HB.
   inversion HB; subst.
   inversion H2; subst.
   rewrite <- (eq_type_subs_func Hsub H4 H3).
   apply (eq_term_subs_dabs Hsub H4 HB ) in Hb as HS.
   apply HS.
Qed.

