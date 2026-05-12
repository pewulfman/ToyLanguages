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
| ptyp_subs (A : preType) (y : preSubs) : preType
| ptyp_pi   (A : preType) (B : preType) : preType
| ptyp_sig  (A : preType) (B : preType) : preType
| ptyp_eq   (A : preType) (a b : preTerm) : preType

with preTerm : Set :=
| ptrm_qar : preTerm
| ptrm_pair (a b : preTerm) : preTerm
| ptrm_fst  (p : preTerm) : preTerm
| ptrm_snd  (p : preTerm) : preTerm
| ptrm_subs (a : preTerm) (y : preSubs) : preTerm
| ptrm_abs (b : preTerm) : preTerm
| ptrm_app (f a : preTerm) : preTerm
| ptrm_refl : preTerm
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
Notation "A [ y ]"    := (ptyp_subs A y) (at level 1): ty_scope.
Notation "Π( A , B )" := (ptyp_pi A B) : ty_scope.
Notation "Σ( A , B )" := (ptyp_sig A B) : ty_scope.
Notation "Eqx( A , a , b )" := (ptyp_eq A a b) : ty_scope.


Notation q                 := ptrm_qar.
Notation "( a , b )"       := (ptrm_pair a b) (no associativity): term_scope.
Notation "'fst' p"         := (ptrm_fst p) (at level 60, right associativity): term_scope.
Notation "'snd' p"         := (ptrm_snd p) (at level 60, right associativity): term_scope.
Notation "a [ y ]"         := (ptrm_subs a y)(at level 1): term_scope.
Notation "'λ' ( b )"       := (ptrm_abs b) (at level 20): term_scope.
Notation "'app' ( f , a )" := (ptrm_app f a) (at level 20): term_scope.
Notation "'refl'"          := (ptrm_refl) (at level 0): term_scope.

(** Unaxiomatic construction **)
Definition psub_ext_type (y : preSubs) (A : preType) : preSubs := (y ∘ p) # q .
Notation "y #! A" := (psub_ext_type y A)(at level 1, left associativity) : subs_scope.

Definition ptyp_func (A B : preType) : preType := Π(A, B [p]).
Notation "A -> B" := (ptyp_func A B) (at level 99, right associativity) : ty_scope.

Definition ptyp_prod (A B : preType) : preType := Σ(A, B [p]).
Notation "A * B" := (ptyp_prod A B) (at level 40, left associativity): ty_scope.

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
   | type_subs {Δ Γ} {y} {A} :
      [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ]
      -> [ Δ ⊢ A [y] type ]
   (** Pi type p.36 **)
   | type_pi {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ]
      -> [ Γ ⊢ Π(A, B) type ]
   (** Sigma type p.43 **)
   | type_sig {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ]
      -> [ Γ ⊢ Σ(A, B) type ]
   (** Equality type p.46 **)
   | type_eq {Γ} {A} {a b} :
      [ ⊢ Γ Cx ] -> (* not in the book, loop breaker *)
      [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ A ]
      -> [ Γ ⊢ Eqx(A, a, b) type ]%ty

with TermJG : preContext -> preType -> preTerm -> Prop :=
   | term_qar {Γ A} :
      [ Γ ⊢ A type ]
      -> [ Γ # A ⊢ q @ A [p] ]
     (* The q term is a "generic element" of the type A, which can be substituted by any term of type A. *)
   (** Pi type p.36 **)
   | term_abs {Γ A B b} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ b @ B ]
      -> [ Γ ⊢ λ(b) @ (Π(A, B)) ]
   | term_app {Γ A B f a} :
   [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ f @ (Π(A, B)) ]
      -> [ Γ ⊢ app(f, a) @ B [id # a] ]
   | term_subs {Δ Γ} {y} {A} {a} :
      [ Δ ⊢ y ~ Γ ]  -> [ Γ ⊢ a @ A ]
      -> [ Δ ⊢ (a [y]) @ A [y] ]
   (** Sigma type p.44 **)
   | term_pair {Γ A B a b} :
      [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ b @ B [id # a] ]
      -> [ Γ ⊢ (a, b) @ Σ(A, B) ]
   | term_fst {Γ A B p} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ p @ Σ(A, B) ]
      -> [ Γ ⊢ fst p @ A ]
   | term_snd {Γ A B p} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ p @ Σ(A, B) ]
       -> [ Γ ⊢ snd p @ B [id # fst p] ]
   (** Equality type p.46 **)
   | term_refl {Γ A a} :
      [ Γ ⊢ a @ A ]
      -> [ Γ ⊢ refl @ Eqx(A, a, a) ]

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
| eq_type_pi {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ # A ⊢ B == D type ]
   -> [ Γ ⊢ Π(A, B) == Π(C, D) type ]
| eq_type_sig {Γ} {A B C D} :
   [ Γ ⊢ A == C type ] -> [ Γ # A ⊢ B == D type ]
   -> [ Γ ⊢ Σ(A, B) == Σ(C, D) type ]
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
(** Pi type p.36 **)
| eq_type_pi_subs {Δ Γ y A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ]
   -> [ Δ ⊢ Π(A, B) [y] == Π(A[y], B[y #! A]) type ]
(** Sigma type p.43 **)
| eq_type_sig_subs {Δ Γ y A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ]
   -> [ Δ ⊢ Σ(A, B) [y] == Σ(A[y], B[y #! A]) type ]
   (** Equality type p.46 **)
   | eq_type_refl_subs {Δ Γ y A a b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ A ]
   -> [ Δ ⊢ Eqx(A, a, b) [y] == Eqx(A[y], a[y], b[y]) type ]

(**** Term Equivalence ****)
with eq_term : preContext -> preType -> preTerm -> preTerm -> Prop :=
(** Symmetric Transitive Closure **)
| eq_term_sym {Γ A} {a b} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == a @ A ]
| eq_term_trans {Γ A} {a b c} : [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ b == c @ A ] -> [ Γ ⊢ a == c @ A ]
(** Constructor Rules **)
| eq_term_pair {Γ} {A B} {a b c d} :
  [ Γ ⊢ a == c @ A] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ b == d @ B [id # a] ] -> [ Γ ⊢ (a, b) == (c, d) @ Σ(A, B) ]
| eq_term_fst {Γ} {A B} {p q} :
   [Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] ->
   [ Γ ⊢ p == q @ Σ(A, B) ]
   -> [ Γ ⊢ fst p == fst q @ A ]
| eq_term_snd {Γ} {A B} {p q} :
   [Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] ->
   [ Γ ⊢ p == q @ Σ(A, B) ]
   -> [ Γ ⊢ snd p == snd q @ B[id # fst p] ]
| eq_term_abs {Γ} {A B} {a b} :
   [ Γ # A ⊢ a == b @ B ] -> [ Γ ⊢ λ(a) == λ(b) @ Π(A, B) ]
| eq_term_app  {Γ} {A B} {f g a b} :
   [ Γ ⊢ f == g @ Π(A, B) ] -> [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ app (f, a) == app (g, b) @ B [id#a] ]
| eq_term_subs {Δ Γ} {y d} {A} {a b} :
   [ Δ ⊢ y == d ~ Γ ] -> [ Γ ⊢ a == b @ A ]
   -> [ Δ ⊢ a [y] == b [d] @ A [y] ]
(** Compatibility with substitution p.32 **)
| eq_term_subs_id {Γ} {A a} :
   [ Γ ⊢ a @ A ]
   -> [ Γ ⊢ a [ id ] == a @ A ]
| eq_term_subs_comp {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 ~ Γ1 ] -> [ Γ1 ⊢ y0 ~ Γ0 ] -> [ Γ0 ⊢ a @ A ]
   -> [ Γ2 ⊢ a [ y0 ∘ y1 ] == a [ y0 ] [ y1 ] @ A [y0 ∘ y1] ]
(** βη-equivalence for substitution extension p.34 **)
| eq_term_beta_qar {Δ} {Γ} {y} {A} {a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type  ] -> [ Δ ⊢ a @ A [y] ]
   -> [ Δ ⊢ q [ y # a ] == a @ A[y] ]
(** Pi type p.36 **)
| eq_term_subs_abs {Δ Γ A B y b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] -> [ Γ # A ⊢ b @ B ]
   -> [ Δ ⊢ λ(b) [y] == λ(b[y #! A]) @ Π(A, B) [y] ]
| eq_term_subs_app { Δ Γ A B f a y } :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ f @ Π(A, B) ]
   -> [ Δ ⊢ app(f, a)[y] == app(f [y], a[y]) @ B[y # (a [y])] ]
(** Sigma type p.45 **)
| eq_term_subs_pair {Δ Γ} {y} {A B} {a b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a @ A ] -> [Γ # A ⊢ B type ] -> [ Γ ⊢ b @ B [id # a] ]
   -> [ Δ ⊢ (a, b) [y] == (a [y], b [y]) @ Σ(A, B) [y] ]
(* TODO : derive those two rules from the previous ones *)
|  eq_term_subs_fst {Δ Γ} {y} {A B} {p} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ p @ Σ(A, B) ]
   -> [ Δ ⊢ (fst p) [y] == fst (p [y]) @ A [y]  ]
| eq_term_subs_snd {Δ Γ} {y} {A B} {p} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ p @ Σ(A, B) ]
   -> [ Δ ⊢ (snd p) [y] == snd (p [y]) @ B [ y #! A ∘ id # fst (p [y])] ]
(** βη-equivalence for dependent abstractions p.37 **)
| eq_term_beta_dapp {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ b @ B ]
   -> [ Γ ⊢ app( λ (b) , a ) == b [ id # a] @ B [id # a] ]
| eq_term_eta_dapp {Γ} {A B} {f} :
[ Γ ⊢ A type ] -> [ Γ # A ⊢ B type] -> [ Γ ⊢ f @  (Π(A, B)) ]
   -> [ Γ ⊢ f == (λ ( app(f [p], q))) @ (Π(A, B)) ]
(** βη-equivalence for dependent pairs p.45 **)
| eq_term_beta_fst {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A] -> [Γ # A ⊢ B type] -> [ Γ ⊢ b @ B [id # a] ]
   -> [ Γ ⊢ fst (a, b) == a @ A ]
| eq_term_beta_snd {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ b @ B [id # a] ]
   -> [ Γ ⊢ snd (a, b) == b @ B [id # a] ]
| eq_term_eta_pair {Γ} {A B} {p} :
  [Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ p @ Σ(A, B) ]
   -> [ Γ ⊢ p == (fst p, snd p) @ Σ(A, B) ]
   (** Equality type p.46 **)
| equality_reflextion {Γ} {A a b p} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ A ] -> [ Γ ⊢ p @ Eqx(A, a, b) ]
   -> [ Γ ⊢ a == b @ A ]


where "[ ⊢ Γ 'Cx' ]"          := (ContextJG Γ)
and   "[ Γ ⊢ A 'type' ]"      := (TypeJG Γ A)
and   "[ Γ ⊢ a @ A ]"         := (TermJG Γ A a)
and   "[ Δ ⊢ y ~ Γ ]"         := (SubsJG Δ Γ y)
and   "[ Γ ⊢ A == B 'type' ]" := (eq_type Γ A B)
and   "[ Γ ⊢ a == b @ A ]"    := (eq_term Γ A a b)
and   "[ Δ ⊢ y == y' ~ Γ ]"   := (eq_subs Δ Γ y y')
.
(** End Jugements *)

Example Ex1 : ([1 ⊢ (b * b) -> b type ]).
Proof.
   set ctx_one as Hc.
   apply type_base in Hc as Hb.
   apply (type_subs (subs_weak Hb)) in Hb as Hbp.
   apply (type_pi (type_sig Hb Hbp)).
   apply (type_subs (subs_weak (type_sig Hb Hbp)) Hb).
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

(** Building term_conv. **)
Lemma subs_pq {Γ} {A} :
   [ Γ ⊢ A type ] -> [ Γ # A ⊢ p # q ~ Γ # A ].
Proof.
   apply (fun HA => subs_ext (subs_weak HA) HA (term_qar HA)).
Qed.

Lemma magic_q {Γ} {A B}:
   [Γ ⊢ A == B type ]
   -> [ Γ # A ⊢ q @ B [p]].
Proof.
Admitted.

(*** Fundamental property ***)
Lemma eq_ctx_ext {Γ A B} :
   [ Γ ⊢ A == B type ] -> A = B.
Proof.
   intros Heq.
   apply magic_q in Heq as HS.
   inversion HS; subst.
   tauto.
Qed.

Lemma term_conv {Γ A B a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A == B type ] ->
   [ Γ ⊢ a @ B ].
Proof.
   intros Ha Heq.
   apply eq_ctx_ext in Heq; subst.
   tauto.
Qed.

Add Parametric Morphism Γ : (TypeJG Γ)
   with signature (eq_type Γ ==> iff)
   as eq_type_mor.
Proof.
   intros A B Heq.
   apply eq_ctx_ext in Heq; subst.
   tauto.
Qed.


Lemma eq_type_conv {Γ A B C } :
   [ Γ ⊢ A == B type ] -> [ Γ # A ⊢ C type ] -> [ Γ # B ⊢ C type ].
Proof.
   intros Heq HC.
   apply eq_ctx_ext in Heq; subst.
   tauto.
Qed.

Add Parametric Morphism Γ B : (fun A => TypeJG (Γ # B) A)
   with signature (eq_type Γ ==> iff)
   as eq_type_etx_mor.
Proof.
   intros A C Heq.
   apply eq_ctx_ext in Heq; subst.
   tauto.
Qed.

Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> iff)
   as term_jug_eq_type_mor.
Proof.
   intros A B Heq.
   apply eq_ctx_ext in Heq; subst.
   tauto.
Qed.

(** Bug ? **)
Add Parametric Morphism Γ : (TermJG Γ)
   with signature (eq_type Γ ==> eq ==> Basics.flip Basics.impl)
   as term_jug_eq_type_mor2.
Proof.
   intros A B Heq.
   apply eq_ctx_ext in Heq; subst.
   unfold Basics.flip, Basics.impl.
   tauto.
Qed.

Add Parametric Morphism Γ : (eq_term Γ)
   with signature (eq_type Γ ==> eq ==> eq ==> iff)
   as eq_term_eq_type_mor.
Proof.
   intros A B Heq.
   apply eq_ctx_ext in Heq; subst.
   tauto.
Qed.
Corollary term_id_type {Γ A a} :
   [Γ ⊢ a @ A ] -> [ Γ ⊢ A type ]
   -> [ Γ ⊢ a @ A [id] ].
Proof.
   intros Ha HA.
   rewrite (eq_type_subs_id HA).
   apply Ha.
Qed.
Theorem term_press {Γ A a}:
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ].
Proof.
   intros H.
   dependent induction H.
   apply (type_subs (subs_weak H) H).
   apply (type_pi H IHTermJG).
   apply (type_subs (subs_ext (subs_id (type_press IHTermJG1))
   IHTermJG1 (term_id_type H IHTermJG1)) H0).
   apply (type_subs H IHTermJG).
   apply type_sig; [apply IHTermJG1 | apply H0].
   apply H.
   apply (type_subs (subs_ext (subs_id (type_press H)) H (term_conv (term_fst H H0 H1) (eq_type_sym (eq_type_subs_id H)))) H0).
   apply (type_eq (type_press IHTermJG) H H).
Qed.

(** End Fundamental property **)

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
   apply eq_type_refl in H as HS.
   apply (eq_type_subs Heq) in HS.
   apply eq_ctx_ext in HS; subst.
   inversion HS; subst.
   apply (eq_subs_ext Heq (eq_term_refl Ha) H Ha).
   exact Ha.
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
   apply (eq_subs_ext (eq_subs_refl H) Heq).
Abort.

(* Add Parametric Morphism Γ : ptyp_pi with
   signature (eq_type Γ ==> eq_type Γ ==> eq_type Γ)
as eq_type_pi_mor.
Proof.
   intros A B Heq C D Heq'.
   apply (eq_type_pi Heq Heq').
Qed.
*)
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

Add Parametric Morphism Γ A B : ptrm_abs with
   signature (eq_term (Γ # A) B ==> eq_term Γ ( Π(A, B) ) )
as eq_term_abs_mor.
Proof.
   intros a b Heq.
   apply (eq_term_abs Heq).
Qed.
Add Parametric Morphism Γ A B : ptrm_app with
   signature (eq_term Γ (Π(A, B)) ==> eq_term Γ A ==> eq_term Γ B)
as eq_term_app_mor.
Proof.
   intros f g Heq a b Heq'.
   apply (eq_term_app Heq) in Heq'.
Abort.
Add Parametric Morphism Δ Γ A y (H : [Δ ⊢ y ~ Γ]) : (fun a => ptrm_subs a y) with
   signature (eq_term Γ A ==> eq_term Δ A[y])
as eq_term_subs_mor.
Proof.
   intros a b Heq.
   apply (eq_term_subs_T H Heq).
Qed.
(** End Rewriting **)

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
      rewrite (eq_type_subs_comp H_δ H_y H_A).
      apply (term_subs H_δ H_a).
      apply (subs_comp H_δ (subs_ext H_y H_A H_a)).
Qed.

Lemma eq_subs_eta_id { Γ A} :
   [ ⊢ Γ Cx ] -> [ Γ ⊢ A type]
   -> [ Γ # A ⊢ id == p # q ~ Γ # A ].
Proof.
   intros HΓ HA.
   apply (ctx_ext HΓ) in HA as HΓA.
   rewrite (eq_subs_eta HA (subs_id HΓA)).
   apply term_qar in HA as Hq.
   apply subs_weak in HA as Hw.
   apply (type_subs Hw) in HA as HAp.
   apply (eq_subs_ext); try assumption.
   apply (eq_subs_right_id Hw).
   rewrite (eq_type_subs_comp (subs_id HΓA) Hw HA).
   rewrite (eq_type_subs_id HAp).
   apply (eq_term_subs_id Hq).
   rewrite (eq_type_subs_comp (subs_id HΓA) Hw HA).
   apply (term_subs (subs_id HΓA) Hq).
Qed.

Lemma eq_subs_beta_id {Γ A} :
   [ ⊢ Γ Cx ] -> [Γ ⊢ A type] ->
    [ Γ # A # A[p] ⊢ (id # q) ∘ p == id ~ Γ # A # A[p]].
Proof.
   intros H HA.
   (* dependent induction H. *)
   apply subs_weak in HA as Hw.
   apply term_qar in HA as Hq.
   apply (type_subs Hw) in HA as HAp.
   apply (term_subs (subs_id (ctx_ext H HA))) in Hq as Hqid.
   rewrite <-(eq_type_subs_id HAp) in Hq.
   rewrite (Exercise_2_3 (subs_id (ctx_ext H HA)) (subs_weak HAp) HAp Hq).
   rewrite (eq_type_subs_id HAp) in Hqid.
   apply (term_subs (subs_weak HAp)) in Hq as Hqp.
   rewrite <- (eq_type_subs_comp (subs_weak HAp) (subs_id (ctx_ext H HA)) HAp) in Hqp.
   rewrite (eq_subs_ext_S (eq_subs_left_id (subs_weak HAp)) HAp Hqp).
Abort.



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

(*** "Presupositions" Theorems ***)

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

Theorem eq_type_press_l :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ A type ].
Proof.
   intros.
   dependent induction H; try (tauto).
   - rewrite H in IHeq_type.
      assumption.
   - apply (type_pi); try assumption.
   - apply (type_sig); try assumption.
   - apply (eq_subs_press) in H as [H_y H_d].
      eapply (type_subs); eassumption.
   - apply (type_id H).
   - apply (type_subs (subs_comp H H0) H1).
   - apply (type_subs H (type_pi H0 H1)).
   - apply (type_subs H (type_sig H0 H1)).
   - apply (type_subs H (type_eq (subs_press_r H) H0 H1)).
Qed.

Theorem eq_type_press_r :
   forall {Γ A B}, [ Γ ⊢ A == B type ] -> [ Γ ⊢ B type ].
Proof.
   intros.
   apply eq_type_press_l in H as HS.
   rewrite H in HS.
   assumption.
Qed.

Corollary term_press_ctx {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ ⊢ Γ Cx ].
Proof. apply (fun H => type_press (term_press H)). Qed.

Corollary term_subs_compose {Δ Γ A a y1 y0} :
   [ Δ ⊢ y0 ~ Γ ]
   -> [ Γ ⊢ a @ A [y1] ]
   -> [ Δ ⊢ a [y0] @ A [y1 ∘ y0] ].
Proof.
   intros Hy0 Ha.
   apply term_press in Ha as HA.
   inversion HA; subst.
   rewrite (eq_type_subs_comp Hy0 H2 H3).
   apply (term_subs Hy0 Ha).
Qed.

Corollary term_id {Γ A a} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ a [id] @ A ].
Proof.
   intro H.
   rewrite <- (eq_type_subs_id (term_press H)).
   apply (term_subs (subs_id (term_press_ctx H)) H).
Qed.


Corollary self_extension {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ (id # a) ~ (Γ # A) ].
Proof.
   intro H.
   apply (subs_ext
            (subs_id (term_press_ctx H))
            (term_press H)
            (term_id_type H (term_press H))).
Qed.

Corollary eq_subs_beta_id {Γ a A} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ p ∘ (id # a) == id ~ Γ ].
Proof.
   intro H.
   apply (eq_subs_beta
         (subs_id (term_press_ctx H))
         (term_press H)
         (term_id_type H (term_press H))).
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


Lemma eq_subs_eta_id_type {Γ A} :
   [ Γ ⊢ A type ] ->
   [ Γ # A # A[p] ⊢ p #! A == p #! A ∘ p # q ~ Γ # A ].
Proof.
   intros HA.
   rewrite <- (eq_subs_right_id (subs_ext_type (subs_weak HA) HA)) at 1.
   apply (eq_subs_comp_r (subs_ext_type (subs_weak HA) HA)).
   apply eq_subs_eta_id.
   apply (type_ctx_ext HA).
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

Lemma eq_subs_ext_type_eta {Δ Γ y A a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ a @ A  ]
   -> [Δ ⊢ y #! A ∘ id # a[y]== id # a ∘ y ~ Γ # A ].
Proof.
   intros Hy HA Ha.
   unfold psub_ext_type.
   rewrite (Exercise_2_3
         (subs_comp (subs_weak (type_subs Hy HA)) Hy)
         (self_extension (term_subs Hy Ha))
         HA
         ).
   rewrite (Exercise_2_3 (subs_id (type_press HA) ) Hy HA (term_id_type Ha (term_press Ha))).
   symmetry.
   apply (eq_subs_ext).
   rewrite (eq_subs_left_id Hy).
   rewrite <- (eq_subs_right_id Hy) at 1.
   rewrite <- (eq_subs_comp_assoc (self_extension (term_subs Hy Ha)) (subs_weak (type_subs Hy HA)) Hy).
   symmetry.
   apply (eq_subs_comp_r Hy).
   apply (eq_subs_beta
            (subs_id (subs_press_l Hy))
            (type_subs Hy HA)
            (term_id_type (term_subs Hy Ha) (type_subs Hy HA))).
   symmetry.
   rewrite (eq_type_subs_S (eq_subs_left_id Hy) HA).
   rewrite <- (eq_type_subs_id (type_subs Hy HA)).
   apply (eq_term_beta_qar (subs_id (subs_press_l Hy)) (type_subs Hy HA) (term_id_type (term_subs Hy Ha) (type_subs Hy HA))).
   apply HA.
   apply (term_subs_compose Hy (term_id_type Ha (term_press Ha))).
   apply (term_subs_compose (self_extension (term_subs Hy Ha))).
   all: rewrite (eq_type_subs_comp (subs_weak (type_subs Hy HA)) Hy HA);
   apply (term_qar (type_subs Hy HA)).
Qed.


Lemma eq_subs_beta_type {Γ A} :
   [ Γ ⊢ A type ] ->
   [ Γ # A ⊢ p #! A ∘ id # q == id ~ Γ # A ].
Proof.
   intros HA.
   apply (subs_weak) in HA as Hw.
   apply (term_qar) in HA as Hq.
   apply (type_subs Hw) in HA as HAp.
   apply (subs_weak) in HAp as Hw2.
   apply (term_qar) in HAp as Hq2.
   rewrite <- (eq_type_subs_comp Hw2 Hw HA) in Hq2.
   rewrite (Exercise_2_3 (subs_comp Hw2 Hw) (self_extension Hq) HA Hq2).
   remember (eq_term_beta_qar (subs_id (type_press HAp) ) HAp (term_id_type Hq (type_subs Hw HA))) as H4.
   clear HeqH4.
   remember (eq_subs_comp_assoc (self_extension Hq) Hw2 Hw) as H5.
   clear HeqH5.
   rewrite (eq_subs_comp_r Hw (eq_subs_beta_id Hq)) in H5.
   rewrite (eq_subs_right_id Hw) in H5.
   rewrite (eq_type_subs_id HAp) in H4.
   symmetry in H4.
   rewrite <- (eq_subs_ext H5 H4 HA Hq).
   symmetry.
   apply (eq_subs_eta_id (type_press HA) HA).
   apply (term_subs_compose (self_extension Hq) Hq2).
Qed.

Theorem eq_term_press {Γ A a b}:
   [ Γ ⊢ a == b @ A ] -> [ Γ ⊢ a @ A ] /\ [ Γ ⊢ b @ A ].
Proof.
   intros Heq.
   dependent induction Heq; try (tauto).
   - destruct IHHeq1, IHHeq2.
       split; eapply (term_pair); try eassumption.
       rewrite <- (eq_type_subs_id (term_press H0)) in Heq1.
       rewrite <- (eq_type_subs (eq_subs_ext (eq_subs_refl (subs_id (term_press_ctx H0))) Heq1 (term_press H0) (term_id_type H0 (term_press H0)) (term_id_type H1 (term_press H1))) (eq_type_refl H)).
       apply H3.
   - destruct IHHeq.
         split; eapply (term_fst); eassumption.
   - destruct IHHeq.
         split. eapply (term_snd); try eassumption.
         apply (term_conv (term_snd H H0 H2)).
         symmetry.
         eapply eq_type_subs_S.
         eapply (eq_subs_ext (eq_subs_refl (subs_id (type_press H)))).
         rewrite (eq_type_subs_id H).
         apply (eq_term_fst H H0 Heq).
         apply H.
         apply (term_id_type (term_fst H H0 H1) H).
         apply (term_id_type (term_fst H H0 H2) H).
         apply H0.
   - destruct IHHeq. apply term_press_ctx in H as H1.
          inversion H1; subst.
         split; eapply (term_abs); eassumption.
   - destruct IHHeq1, IHHeq2.
         apply term_press in H as Hpi.
         inversion Hpi; subst.
         split. eapply (term_app H1); eassumption.
         rewrite <- (eq_type_subs_id H6) in Heq2.
         rewrite (eq_type_subs_S
            (eq_subs_ext
               (eq_subs_refl (subs_id (type_press H6)))
               Heq2
               H6 (term_id_type H1 H6) (term_id_type H2 H6)) H7).
         apply (term_app H2); eassumption.
   - destruct IHHeq.
         apply eq_subs_press in H as H2.
         destruct H2 as [Hy Hd].
         split. apply (term_subs Hy H0).
         rewrite (eq_type_subs_S H (term_press H0)).
         apply (term_subs Hd H1).
   - split; [apply (term_id H) | apply H].
   - split.
      apply (term_subs (subs_comp H H0) H1).
      rewrite (eq_type_subs_comp H H0 (term_press H1)).
      apply (term_subs H (term_subs H0 H1)).
   - split.
      apply (subs_ext H H0) in H1 as H2.
      apply (eq_subs_beta H H0) in H1 as H3.
      rewrite <- (eq_type_subs_S H3 H0).
      rewrite (eq_type_subs_comp H2 (subs_weak H0) H0).
      apply (term_subs H2 (term_qar H0)).
      apply (H1).
   - split.
      apply (term_subs H (term_abs H0 H2)).
      rewrite (eq_type_pi_subs H H0 H1).
      apply (term_abs (type_subs H H0)).
      apply (term_subs (subs_ext_type H H0) H2).
   (* Exercise 2.6 *)
   -  remember (subs_id (subs_press_r H)) as id_subs.
      remember (term_press H0) as HA.
      remember (Exercise_2_3 id_subs H HA (term_id_type H0 HA)) as H3.
      clear HeqH3.
      rewrite (eq_subs_ext_S (eq_subs_left_id H) HA (term_subs_compose H (term_id_type H0 HA))) in H3.
      split.
      rewrite <- (eq_type_subs_S H3 H1).
      apply (term_subs_compose H).
      apply (term_app H0 H1 H2).
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
                     (term_id_type (term_subs H H0) (type_subs H HA))
                     )) in H5.
      rewrite (eq_subs_right_id H) in H5.
      remember (eq_term_beta_qar (subs_id (subs_press_l H)) (type_subs H HA) (term_id_type (term_subs H H0) (type_subs H HA))) as H6.
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
      apply (term_app (term_subs H H0) (type_subs (subs_ext_type H HA) H1)).
      rewrite <- (eq_type_pi_subs H HA H1).
      apply (term_subs H H2).
      rewrite (eq_type_subs_comp (self_extension (term_subs H H0)) (subs_comp (subs_weak (type_subs H HA)) H) HA).
      apply (term_subs (self_extension (term_subs H H0)) Hq).
   - split.
      apply (term_subs H (term_pair H0 H1 H2)).
      rewrite (eq_type_sig_subs H (term_press H0) H1).
      apply (term_pair (term_subs H H0)).
      apply (type_subs (subs_ext_type H (term_press H0)) H1).
      rewrite <- (eq_type_subs_comp (self_extension (term_subs H H0)) (subs_ext_type H (term_press H0)) H1).
      rewrite (eq_type_subs_S (eq_subs_ext_type_eta H (term_press H0) H0) H1).
      apply (term_subs_compose H H2).
   - apply term_press in H0 as H_type.
      inversion H_type; subst.
      split.
      apply (term_subs H (term_fst H4 H5 H0)).
      apply (term_subs H) in H0 as Hpy.
      rewrite (eq_type_sig_subs H H4 H5) in Hpy.
      apply term_press in Hpy as Hpy_type.
      inversion Hpy_type; subst.
      apply (term_fst H6 H7 Hpy).
   - apply term_press in H0 as H_type.
      inversion H_type; subst.
      apply (term_subs H) in H0 as Hpy.
      rewrite (eq_type_sig_subs H H4 H5) in Hpy.
      apply term_press in Hpy as Hpy_type.
      inversion Hpy_type; subst.
      split.
      remember (eq_subs_ext_type_eta H H4 (term_fst H4 H5 H0)) as HS.
      clear HeqHS.
      remember (eq_term_subs_fst H H0) as Heq.
      clear HeqHeq.
      rewrite <- (eq_type_subs_id (type_subs H H4)) in Heq.
      rewrite (eq_subs_comp_r
                  (subs_ext_type H H4)
                  (eq_subs_ext
                     (eq_subs_refl (subs_id (subs_press_l H)))
                     Heq H6
                     (term_id_type (term_subs H (term_fst H4 H5 H0)) (type_subs H H4))
                     (term_id_type (term_fst H6 H7 Hpy) (type_subs H H4))
                  )) in HS.
      rewrite (eq_type_subs_S HS H5).
      apply (term_subs_compose H (term_snd H4 H5 H0)).
      rewrite (eq_type_subs_comp (self_extension (term_fst H6 H7 Hpy)) (subs_ext_type H H4) H5).
      apply (term_snd H6 H7 Hpy).
   - split.
      apply (term_app H (term_press H0) (term_abs (term_press H) H0)).
      apply (term_subs (self_extension H) H0).
   (* Exercise 2.7 *)
   - split. assumption.
      apply (term_abs H).
      apply (term_subs (subs_weak H)) in H1 as H2.
      rewrite (eq_type_pi_subs (subs_weak H) H H0) in H2.
      apply (term_app (term_qar H) (type_subs (subs_ext_type (subs_weak H) H) H0)) in H2.
      rewrite <- (eq_type_subs_id H0).
      rewrite <- (eq_type_subs_comp (self_extension (term_qar H)) (subs_ext_type (subs_weak H) H) H0) in H2.
      apply(term_conv H2).
      remember (term_qar (type_weak H)) as Hq.
      clear HeqHq.
      rewrite <- (eq_type_subs_comp (subs_weak (type_weak H)) (subs_weak H) H) in Hq.
      remember (Exercise_2_3 (subs_comp (subs_weak (type_weak H)) (subs_weak H)) (self_extension (term_qar H)) H Hq) as H3.
      clear HeqH3.
      remember (eq_term_beta_qar (subs_id (type_press H0)) (type_weak H) (term_id_type (term_qar H) (type_weak H))) as H4.
      clear HeqH4.
      remember (eq_subs_comp_assoc (self_extension (term_qar H)) (subs_weak (type_weak H)) (subs_weak H)) as H5.
      clear HeqH5.
      rewrite (eq_subs_comp_r (subs_weak H) (eq_subs_beta_id (term_qar H))) in H5.
      rewrite (eq_subs_right_id (subs_weak H)) in H5.
      symmetry in H4.
      rewrite (eq_type_subs_id (type_weak H)) in H4.
      rewrite <- (eq_subs_ext H5 H4 H (term_qar H)) in H3.
      rewrite <- (eq_subs_eta_id (type_press H) H) in H3.
      apply (eq_type_subs_S H3 H0).
      apply (term_subs_compose (self_extension (term_qar H)) Hq).
   - split; [apply (term_fst (term_press H) H0 (term_pair H H0 H1)) | apply H].
   - split.
      apply (term_conv
               (term_snd (term_press H) H0 (term_pair H H0 H1))
               ).
      apply (eq_term_beta_fst H H0) in H1 as H2.
      rewrite (eq_type_sym (eq_type_subs_id (term_press H))) in H2.
      apply (eq_type_subs_S
               (eq_subs_ext
                  (eq_subs_refl (subs_id (term_press_ctx H)))
                  H2
                  (term_press H)
                  (term_id_type (term_fst (term_press H) H0 (term_pair H H0 H1)) (term_press H))
                  (term_id_type H (term_press H))) H0).
      apply H1.
   - split; [apply H1 | apply ( term_pair (term_fst H H0 H1) H0 (term_snd H H0 H1))].
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
Lemma term_NDabs {Γ A B b} :
      [ Γ # A ⊢ b @ B [p] ]
      -> [ Γ ⊢ λ(b) @ (A -> B) ].
Proof.
   intros H.
   apply term_press_ctx in H as H_ctx.
   inversion H_ctx; subst.
   apply (term_abs H3 H).
Qed.

Lemma term_NDapp {Γ A B f a} :
      [ Γ ⊢ f @ (A -> B) ] -> [ Γ ⊢ a @ A ]
      -> [ Γ ⊢ app (f, a) @ B ].
Proof.
   intros Hf Ha.
   apply term_press in Hf as Hf_type.
   inversion Hf_type; subst.
   apply (term_app Ha H3) in Hf as H4.
   inversion H3; subst.
   inversion H5; subst.
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak H2) H6) in H4.
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) H6) in H4.
   rewrite (eq_type_subs_id H6) in H4.
   apply H4.
Qed.


Lemma eq_term_NDabs {Γ} {A B} {a b} :
   [ Γ # A ⊢ a == b @ B [p] ] -> [ Γ ⊢ λ(a) == λ(b) @ A -> B ].
Proof.
   intros Heq.
   apply (eq_term_abs Heq).
Qed.
Lemma eq_term_NDapp  {Γ} {A B} {f g a b} :
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
   apply (eq_term_app Heq_f) in Heq_a as H1.
   apply eq_term_press in Heq_a as Hab.
   destruct Hab as [Ha Hb].
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak H2) H5) in H1.
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) H5) in H1.
   rewrite (eq_type_subs_id H5) in H1.
   apply H1.
Qed.

Lemma eq_term_subs_NDapp {Δ Γ} {y} {A B} {f a} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ f @ A -> B ] -> [ Γ ⊢ a @ A ]
   -> [ Δ ⊢ app (f, a) [y] == app (f [y], a [y]) @ B[y] ].
Proof.
   intros Hsub Hf Ha.
   apply term_press in Hf as Hf_type.
   inversion Hf_type; subst.
   apply (eq_term_subs_app Hsub Ha H3 ) in Hf as H1.
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
   apply eq_type_press_l in HAC as HA.
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

Lemma eq_term_subs_NDabs {Δ Γ} {y} {A B} {b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ # A ⊢ b @ B [p] ]
   -> [ Δ ⊢ λ(b) [y] == λ(b [(y ∘ p)#q]) @ A[y] -> B[y] ].
Proof.
   intros Hsub Hb.
   apply (term_press) in Hb as HB.
   inversion HB; subst.
   inversion H2; subst.
   rewrite <- (eq_type_subs_func Hsub H4 H3).
   apply (eq_term_subs_abs Hsub H4 HB ) in Hb as HS.
   apply HS.
Qed.


Lemma type_prod {Γ} {A B} :
   [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Γ ⊢ (A * B) type ].
Proof.
   intros HA HB.
   apply (type_sig HA).
   apply (type_subs (subs_weak HA) HB).
Qed.

Lemma term_NDpair {Γ A B a b} :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ (a, b) @ (A * B) ].
Proof.
   intros Ha Hb.
   apply (term_pair Ha).
   apply (type_subs (subs_weak (term_press Ha)) (term_press Hb)).
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak (term_press Ha)) (term_press Hb)).
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) (term_press Hb)).
   apply (term_id_type Hb (term_press Hb)).
Qed.


Lemma term_NDfst {Γ A B p} :
   [ Γ ⊢ p @ (A * B) ] -> [ Γ ⊢ fst p @ A ].
Proof.
   intros H.
   apply term_press in H as H_type.
   inversion H_type; subst.
   apply (term_fst H3 H4 H).
Qed.
Lemma term_NDsnd {Γ A B p} :
   [ Γ ⊢ p @ (A * B) ] -> [ Γ ⊢ snd p @ B ].
Proof.
   intros H.
   apply term_press in H as H_type.
   inversion H_type; subst.
   inversion H4; subst.
   inversion H5; subst.
   apply (term_snd H3 H4) in H as HS.
   rewrite <- (eq_type_subs_comp (self_extension (term_NDfst H)) (subs_weak H3) H6) in HS.
   rewrite (eq_type_subs_S (eq_subs_beta_id (term_NDfst H)) H6) in HS.
   rewrite (eq_type_subs_id H6) in HS.
   apply HS.
Qed.

Lemma eq_type_subs_prod {Δ Γ} {y} {A B} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ A type ] -> [ Γ ⊢ B type ]
   -> [ Δ ⊢ (A * B)[y] == (A[y] * B[y]) type ].
Proof.
   intros Hsub HA HB.
   apply (type_subs (subs_weak HA)) in HB as HS.
   rewrite (eq_type_sig_subs Hsub HA HS).
   apply (eq_type_sig (eq_type_refl (type_subs Hsub HA))).
   rewrite <- (eq_type_subs_comp (subs_ext_type Hsub HA) (subs_weak HA) HB).
   rewrite <- (eq_type_subs_comp (subs_weak (type_subs Hsub HA)) Hsub HB).
   eapply (eq_type_subs_S (eq_subs_ext_type_beta Hsub HA) HB).
Qed.

Lemma eq_term_subs_NDpair {Δ Γ} {y} {A B} {a b} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
   -> [ Δ ⊢ (a, b) [y] == (a [y], b [y]) @ A [y] * B [y] ].
Proof.
   intros Hsub Ha Hb.
   apply (term_press) in Ha as HA.
   apply (term_press) in Hb as HB.
   rewrite <- (eq_type_subs_prod Hsub HA HB).
   apply (eq_term_subs_pair Hsub Ha).
   apply (type_subs (subs_weak HA) HB).
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak HA) HB).
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) HB).
   apply (term_id_type Hb (term_press Hb)).
Qed.


Lemma eq_term_subs_NDfst {Δ Γ} {y} {A B} {p} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ p @ A * B ]
   -> [ Δ ⊢ (fst p) [y] == fst (p [y]) @ A [y]  ].
Proof.
   intros Hy Hp.
   apply (eq_term_subs_fst Hy Hp).
Qed.

Lemma eq_term_subs_NDsnd {Δ Γ} {y} {A B} {p} :
   [ Δ ⊢ y ~ Γ ] -> [ Γ ⊢ p @ A * B ]
   -> [ Δ ⊢ (snd p) [y] == snd (p [y]) @ B [y] ].
Proof.
   intros Hy Hp.
   apply term_press in Hp as Hp_type.
   inversion Hp_type; subst.
   inversion H3; subst.
   inversion H4; subst.
   apply (term_subs Hy) in Hp as Hpy.
   rewrite (eq_type_subs_prod Hy H2 H5) in Hpy.
   enough (Heq_type : [ Δ ⊢ B [definitions.p] [y #! A ∘ id # (fst p [y])] == B [y] type ]).
   rewrite <- Heq_type.
   apply (eq_term_subs_snd Hy Hp).
   rewrite (eq_type_subs_comp
               (self_extension (term_NDfst Hpy))
               (subs_ext_type Hy H2)
               H3).
   rewrite (eq_type_subs_T
               (self_extension (term_NDfst Hpy))
               (eq_type_sym (eq_type_subs_comp (subs_ext_type Hy H2) H4 H5))).
   rewrite (eq_type_subs_T
               (self_extension (term_NDfst Hpy))
               (eq_type_subs_S (eq_subs_ext_type_beta Hy H2) H5)).
   rewrite <- (eq_type_subs_comp
                  (self_extension (term_NDfst Hpy))
                  (subs_comp (subs_weak (type_subs Hy H2)) Hy) H5).
   rewrite <- (eq_type_subs_S (eq_subs_comp_assoc (self_extension (term_NDfst Hpy)) (subs_weak (type_subs Hy H2)) Hy) H5).
   rewrite (eq_type_subs_comp
                  (subs_comp
                  (self_extension (term_NDfst Hpy))
                  (subs_weak (type_subs Hy H2))
                  ) Hy H5).
   rewrite (eq_type_subs_S (eq_subs_beta_id (term_NDfst Hpy)) (type_subs Hy H5)).
   apply (eq_type_subs_id (type_subs Hy H5)).
Qed.

(** βη-equivalence for pairs p.22 **)
Lemma eq_term_beta_NDfst {Γ} {A B} a b :
   [ Γ ⊢ a @ A] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ fst (a, b) == a @ A ].
Proof.
   intros Ha Hb.
   apply (term_press) in Ha as HA.
   apply (term_press) in Hb as HB.
   apply (eq_term_beta_fst Ha (type_subs (subs_weak HA) HB)).
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak HA) HB).
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) HB).
   apply (term_id_type Hb (term_press Hb)).
Qed.

Lemma eq_term_beta_NDsnd {Γ} {A B} a b :
   [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ]
   -> [ Γ ⊢ snd (a, b) == b @ B ].
Proof.
   intros Ha Hb.
   apply (term_press) in Ha as HA.
   apply (term_press) in Hb as HB.
   rewrite <- (eq_type_subs_id HB).
   rewrite <- (eq_type_subs_S (eq_subs_beta_id Ha) HB).
   rewrite (eq_type_subs_comp (self_extension Ha) (subs_weak HA) HB).
   apply (eq_term_beta_snd Ha (type_subs (subs_weak HA) HB)).
   rewrite <- (eq_type_subs_comp (self_extension Ha) (subs_weak HA) HB).
   rewrite (eq_type_subs_S (eq_subs_beta_id Ha) HB).
   apply (term_id_type Hb (term_press Hb)).
Qed.

Lemma eq_term_eta_NDpair {Γ} {A B} p :
   [ Γ ⊢ p @ A * B ]
   -> [ Γ ⊢ p == (fst p, snd p) @ A * B ].
Proof.
   intros Hp.
   apply (term_press) in Hp as Hp_type.
   inversion Hp_type; subst.
   apply (eq_term_eta_pair H2 H3 Hp).
Qed.
