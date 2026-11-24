(* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

(* Forward chaining of applications, to facilitate "saturating" the known facts
without specializing. See Clément's thesis
http://pit-claudel.fr/clement/MSc/#org036d20e for a nicer explanation. *)
Module Learn.
  Inductive Learnt {P:Prop} :=
  | AlreadyLearnt (H:P).

  Local Ltac learn_fact H :=
    let P := type of H in
    lazymatch goal with
    (* matching the type of H with the Learnt hypotheses means the
    learning fails even when the proposition is known by a different
    but unifiable type term *)
    | [ Hlearnt: @Learnt P |- _ ] =>
      fail 0 "already knew" P "through" Hlearnt
    | _ => pose proof H; pose proof (AlreadyLearnt H)
    end.

  Tactic Notation "learn" constr(H) := learn_fact H.
End Learn.

Import Learn.

Require Export Setoid.
Require Export Relation_Definitions.

(** Pre-syntax definitions **)

(** Convention For syntax sorts. On the left is fonction parameters, on the right construction to stay true to the textbook
   Contexts ctx: greek uppercase letters: 𝚪, Δ, ...
   Types t : uppercase letters: A, B, ...
   Terms e : lowercase letters: a, b, ...
   Substitutions g :  greak lowercase :γ, δ, μ ...
**)

Inductive preContext : Set :=
| pctx_one : preContext
| pctx_ext : preContext -> preType -> preContext

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

with preSubs : Set :=
| psub_id   : preSubs
| psub_comp (y1 y2 : preSubs) : preSubs
| psub_weak : preSubs
| psub_Bang : preSubs
| psub_ext  (y : preSubs) (a : preTerm) : preSubs
.

Declare Scope ctx_scope.
Open Scope ctx_scope.

Notation "1" := pctx_one.
Notation "Γ # A" := (pctx_ext Γ A) (at level 1, left associativity, format "Γ # A") : ctx_scope.

#[add_top] Bind Scope ctx_scope with preContext preType.


Check (1).

Declare Scope ty_scope.
Open Scope ty_scope.

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

Notation q := ptrm_qar.
Notation "( a , b )" := (ptrm_pair a b) (no associativity): term_scope.
Notation "'fst' p" := (ptrm_fst p) (at level 20): term_scope.
Notation "'snd' p" := (ptrm_snd p) (at level 20): term_scope.
Notation "'λ' ( b )" := (ptrm_abs b) (at level 20): term_scope.
Notation "app( f , a )" := (ptrm_app f a) (at level 20): term_scope.
Notation "a [ y ]" := (ptrm_subs a y): term_scope.

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

Reserved Notation "[ ⊢ Γ 'Cx' ]"       (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ A 'type' ]"     (at level 0, no associativity).
Reserved Notation "[ Γ ⊢ a @ A ]" (at level 0, no associativity).
Reserved Notation "[ Δ ⊢ y 'to' Γ ]" (at level 0, no associativity).

Print Scopes.
Print Visibility.

Inductive  ContextJG : preContext -> Prop :=
   | context_empty : [ ⊢ 1 Cx ]
   | context_extend {Γ : preContext} {A : preType} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ A type ] -> [ ⊢  Γ # A Cx]

with TypeJG : preContext -> preType -> Prop :=
   | type_base {Γ} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ base type ]
   | type_prod {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ ⊢ B type ] -> [ Γ ⊢ (A * B) type ]
   | type_func {Γ} {A B} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ B type ] -> [ Γ ⊢ A --> B type ]
   | type_subs {Δ Γ} {y} {A} :
      [ Δ ⊢ y to Γ ] -> [ Γ ⊢ A type ] -> [ Δ ⊢ A [y] type ]

with TermJG : preContext -> preType -> preTerm -> Prop :=
   | term_qar {Γ A} : [ Γ ⊢ A type ] -> [ Γ # A ⊢ q @ A [p] ]
   | term_pair {Γ A B a b} :
      [ Γ ⊢ a @ A ] -> [ Γ ⊢ b @ B ] -> [ Γ ⊢ (a, b) @ (A * B) ]
   | term_fst {Γ A B p} :
      [ Γ ⊢ p @ (A * B) ] -> [ Γ ⊢ fst p @ A ]
   | term_snd {Γ A B p} :
      [ Γ ⊢ p @ (A * B) ] -> [ Γ ⊢ snd p @ B ]
   | term_abs {Γ A B b} :
      [ Γ # A ⊢ b @ B ] -> [ Γ ⊢ λ (b) @ (A --> B) ]
   | term_app {Γ A B f a} :
      [ Γ ⊢ f @ (A --> B) ] -> [ Γ ⊢ a @ A ] -> [ Γ ⊢ app(f, a) @ (B) ]
   | term_subs {Δ Γ} {y} {A} {a} :
      [ Δ ⊢ y to Γ ]  ->
      [ Γ ⊢ a @ A ] ->
      [ Δ ⊢ (a [y]) @ (A [y]) ]

with SubsJG : preContext -> preContext -> preSubs -> Prop :=
   | subs_id {Γ} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ Id to Γ ]
   | subs_comp {Γ0 Γ1 Γ2} {y0 y1} :
       [ Γ2 ⊢ y1 to Γ1 ] ->
       [ Γ1 ⊢ y0 to Γ0 ] ->
       [ Γ2 ⊢ (y0 ∘ y1) to Γ0 ]
   | subs_weak {Γ A} :
      [ Γ ⊢ A type ] -> [ Γ # A ⊢ p to Γ ]
   | subs_Bang {Γ} :
      [ ⊢ Γ Cx ] -> [ Γ ⊢ ! to 1 ]
   | subs_ext {Δ Γ} {y} {a A} :
      [ Δ ⊢ y to Γ ] ->
      [ Γ ⊢ A type ] ->
      [ Δ ⊢ a @ A[y] ] ->
      [ Δ ⊢ (y # a) to (Γ # A) ]

where "[ ⊢ Γ 'Cx' ]"       := (ContextJG Γ) : ctx_scope
and "[ Γ ⊢ A 'type' ]"     := (TypeJG Γ A) : ty_scope
and "[ Γ ⊢ a @ A ]" := (TermJG Γ A a): term_scope
and "[ Δ ⊢ y 'to' Γ ]" := (SubsJG Δ Γ y): subs_scope
.

Example Ex1 : ([1 ⊢ base * base --> base type ]).
Proof.
   apply type_func.
   - apply type_prod; apply type_base; apply context_empty.
   - apply type_base. apply context_extend.
       + apply context_empty.
       + apply type_prod;
         apply type_base; apply context_empty.
Qed.

(* Well-formed grammar and coercions *)
Definition wfCtx : Set := { Γ : preContext | [ ⊢ Γ Cx ] }.
#[reversible] Coercion wfctx_to_preCtx (Γ : wfCtx) : preContext := proj1_sig Γ.

Definition jug_to_wfCtx : forall Γ, [ ⊢ Γ Cx ] -> wfCtx.
   intros.
   exists Γ.
   assumption.
Qed.
#[reversible] Coercion jug_to_wfCtx : ContextJG >-> wfCtx.

Check wfCtx.


Definition wfTypes {Γ} : Set :=  { A: preType | TypeJG Γ A }  .
#[reversible] Coercion wfType_to_preType {Γ} (A : @wfTypes Γ) : preType := proj1_sig A.
#[reversible] Coercion wfType_to_TypeJG {Γ} (A : @wfTypes Γ) : TypeJG Γ (proj1_sig A) := proj2_sig A.

Definition jug_to_wfType : forall {Γ} (A : preType), [ Γ ⊢ A type ] -> @wfTypes Γ.
   intros.
   exists A.
   assumption.
Qed.
#[reversible] Coercion jug_to_wfType : TypeJG >-> wfTypes .

Check wfTypes.

Definition wfTerms {Γ A} : Set := { a : preTerm | TermJG Γ A a }.
#[reversible] Coercion wfTerm_to_preTerm {Γ A} (a : @wfTerms Γ A) : preTerm := proj1_sig a.

Definition jug_to_wfTerm : forall {Γ A} (a : preTerm), [ Γ ⊢ a @ A ] -> @wfTerms Γ A.
   intros.
   exists a.
   assumption.
Qed.
#[reversible] Coercion jug_to_wfTerm : TermJG >-> wfTerms.
Check wfTerms.

Definition wfSubs {Δ Γ} : Set := { y : preSubs | SubsJG Δ Γ y }.
#[reversible] Coercion wfSubs_to_preSubs {Δ Γ} (y : @wfSubs Δ Γ) : preSubs := proj1_sig y.
#[reversible] Coercion wfSubs_to_SubsJG {Δ Γ} (y : @wfSubs Δ Γ) : SubsJG Δ Γ (proj1_sig y) := proj2_sig y.

Definition jug_to_wfSubs : forall {Δ Γ} (y : preSubs), [ Δ ⊢ y to Γ ] -> @wfSubs Δ Γ.
   intros.
   exists y.
   assumption.
Qed.
#[reversible] Coercion jug_to_wfSubs : SubsJG >-> wfSubs.
Check wfSubs.



Lemma verif_wfTypes : forall Γ (A : @wfTypes Γ), TypeJG Γ A.
   intros.
   exact A.
Qed.


(** Equational Rules  **)

(*** Equality for Types ***)
Reserved Notation "[ Γ ⊢ A1 == A2 'type' ]" (at level 0, no associativity).
Inductive eq_type : preContext -> relation (preType) :=
(** Enforce equivalence **)
| EqSymType : forall Γ A1 A2,
   [ Γ ⊢ A1 == A2 type ] -> [ Γ ⊢ A2 == A1 type ]
| EqTransType : forall Γ A1 A2 A3,
   [ Γ ⊢ A1 == A2 type ] ->
   [ Γ ⊢ A2 == A3 type ] ->
   [ Γ ⊢ A1 == A3 type ]
(** Enforce compatibility with substitution **)
| EqSubstIdType {Γ} {A} :
   [ Γ ⊢ A type ] ->
   [ Γ ⊢ A [ Id ] == A type ]
| EqSubstCompType {Γ Γ1 Γ0} {A} {y1} {y0} :
   [ Γ ⊢ y1 to Γ1 ] ->
   [ Γ1 ⊢ y0 to Γ0 ] ->
   [ Γ0 ⊢ A type ] ->
   [ Γ ⊢ A [ y0 ∘ y1] == A [y0] [y1] type ]

where "[ Γ ⊢ A1 == A2 'type' ]" := (eq_type Γ A1 A2) : ty_scope.


Lemma TypeEqJG_sym {Γ} : symmetric preType (@eq_type Γ).
Proof.
   unfold symmetric.
   apply EqSymType.
Qed.

Lemma TypeEqJG_trans {Γ} : transitive preType (@eq_type Γ).
Proof.
   unfold transitive.
   apply EqTransType.
Qed.

Add Parametric Relation (Γ : wfCtx) : (preType) (@eq_type Γ)
   symmetry proved by (@TypeEqJG_sym Γ)
   transitivity proved by (@TypeEqJG_trans Γ)
   as TypeEqJG_rel.

Add Parametric Morphism (Γ : preContext) : (TypeJG Γ)
   with signature (@eq_type Γ  ==> Basics.impl)
   as TypeEqJG_mor.
Proof.
   intros. unfold Basics.impl.
   induction H;
   try (intro; assumption).
   - intro. apply (type_subs H).
      apply (type_subs H0).
      assumption.
Qed.

(* Add Parametric Morphism (Γ : preContext) : (TermJG Γ)
   with signature (@eq_type Γ  ==> eq  ==> Basics.flip Basics.impl)
   as TermEqJG_mor.
Proof.
   unfold Basics.impl.
   intros.
   induction H. assumption.
   shelve.
   apply IHeq_type1.
   apply IHeq_type2.
   assumption.
   - apply term_subs.
       apply H.
       apply H0.
       assumption.
      +  apply term_qar.
      + intro. eapply term_pair; eassumption.
      + intro. eapply term_fst; eassumption.
      + intro. eapply term_snd; eassumption.
      + intro. eapply term_abs; eassumption.
      + intro. eapply term_app; eassumption.

   - intro. apply (term_qar H). *)

(*** End Equality for Types ***)

(*** Equality of substitutions ***)
Reserved Notation "[ Δ ⊢ y == y' 'to' Γ ]" (at level 0, no associativity).
Inductive eq_subs : preContext -> preContext -> relation (preSubs) :=
(** Enforce equivalence **)
| EqReflSub {Δ Γ} {y}: [ Δ ⊢ y to Γ ] -> [ Δ ⊢ y == y to Γ ]
| EqSymSub {Δ Γ} {y1 y2} :
   [ Δ ⊢ y1 to Γ ] ->
   [ Δ ⊢ y2 to Γ ] ->
   [ Δ ⊢ y1 == y2 to Γ ] ->
   [ Δ ⊢ y2 == y1 to Γ ]
| EqTransSub {Δ Γ} {y1 y2 y3} :
   [ Δ ⊢ y1 to Γ ] ->
   [ Δ ⊢ y2 to Γ ] ->
   [ Δ ⊢ y3 to Γ ] ->
   [ Δ ⊢ y1 == y2 to Γ ] ->
   [ Δ ⊢ y2 == y3 to Γ ] ->
   [ Δ ⊢ y1 == y3 to Γ ]
(** Compatibility with composition **)
| EqLeftId {Δ Γ} {y}:
   [ Δ ⊢ y to Γ ] ->
   [ Δ ⊢ Id ∘ y == y to Γ ]
| EqRightId {Δ Γ} {y}:
   [ Δ ⊢ y to Γ ] ->
   [ Δ ⊢ y ∘ Id == y to Γ ]
| EqCompAssoc {Δ Γ2 Γ1 Γ0} {y0 y1 y2} :
   [ Δ ⊢ y2 to Γ2 ] ->
   [ Γ2 ⊢ y1 to Γ1 ] ->
   [ Γ1 ⊢ y0 to Γ0] ->
   [ Δ ⊢ (y0 ∘ (y1 ∘ y2)) == ((y0 ∘ y1) ∘ y2) to Γ0 ]
(** Unicity of bang **)
| EqBang {Δ} {δ} :
   [ Δ ⊢ δ  to 1 ] ->
   [ Δ ⊢ ! == δ to 1 ]

(** Substitution former **)
| EqSubstBeta {Δ Γ A a y} :
   [ Δ ⊢ y to Γ ] ->
   [ Γ ⊢ A type] ->
   [ Γ ⊢ a @ A ] ->
   [ Δ ⊢ p ∘ (y # a) == y to Γ ]
| EqSubstEta {Δ Γ A y} :
   [ Γ ⊢ A type ] ->
   [ Δ ⊢ y to Γ # A ] ->
   [ Δ ⊢ y == ((p ∘ y) # (q[y])) to (Γ # A) ]

where "[ Δ ⊢ y == y' 'to' Γ ]" := (@eq_subs Δ Γ y y') : ty_scope.


Definition SubsEqJG {Δ : wfCtx} {Γ : wfCtx} : relation (@wfSubs Δ Γ) := @eq_subs Δ Γ.

Lemma SubsEqJG_refl {Δ : wfCtx} {Γ : wfCtx} (gamma : @wfSubs Δ Γ) :
   [ Δ ⊢ gamma == gamma to Γ ].
Proof.
   apply EqReflSub.
   exact gamma.
Qed.

Lemma SubsEqJG_sym {Δ Γ : wfCtx} (y y' : @wfSubs Δ Γ) :
   SubsEqJG y y'  ->
   SubsEqJG y' y.
Proof.
   apply EqSymSub.
   exact y.
   exact y'.
Qed.

Lemma SubsEqJG_trans {Δ Γ : wfCtx} (y1 y2 y3 : @wfSubs Δ Γ) :
   SubsEqJG y1 y2 ->
   SubsEqJG y2 y3 ->
   SubsEqJG y1 y3.
Proof.
   apply EqTransSub;
   [exact y1 | exact y2 | exact y3].
Qed.

Add Parametric Relation (delta ctx :wfCtx) : (@wfSubs delta ctx) (@SubsEqJG delta ctx)
   reflexivity proved by (@SubsEqJG_refl delta ctx)
   symmetry proved by (@SubsEqJG_sym delta ctx)
   transitivity proved by (@SubsEqJG_trans delta ctx)
   as SubsEqJG_rel.

(* Add Parametric Morphism (Δ mid Γ : wfCtx) : (@sub_compose Δ mid Γ)
   with signature (@SubsEqJG mid Γ  ==> @SubsEqJG Δ mid ==> @SubsEqJG Δ Γ)
   as SubsEqJG_mor.
Proof.
   unfold SubsEqJG in *.
   simpl.
   intros gamma1 gamma2 H12.
   intros gamma1' gamma2' H12'.
   apply EqCompSub; assumption.
Qed. *)


(*** End Equality of substitutions ***)


(*** Equality for Terms ***)
Reserved Notation "[ Γ ⊢ a '==' b @ A ]".
Inductive eq_term : preContext -> preType -> relation preTerm :=
(** Enforce equivalence **)
| EqReflTerm {Γ A e} : [ Γ ⊢ e @ A ] -> [ Γ ⊢ e == e @ A ]
| EqSymTerm {Γ A e1 e2} :
   [ Γ ⊢ e1 @ A ] ->
   [ Γ ⊢ e2 @ A ] ->
   [ Γ ⊢ e1 == e2 @ A ] -> [ Γ ⊢ e2 == e1 @ A ]
| EqTransTerm {Γ A e1 e2 e3} :
   [ Γ ⊢ e1 @ A ] -> [ Γ ⊢ e2 @ A ] -> [ Γ ⊢ e3 @ A ] ->
   [ Γ ⊢ e1 == e2 @ A ] ->
   [ Γ ⊢ e2 == e3 @ A ] ->
   [ Γ ⊢ e1 == e3 @ A ]
(** βη-equivalence for pairs **)
| EqBetaFst {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A ] ->
   [ Γ ⊢ b @ B ] ->
   [ Γ ⊢ fst (a, b) == a @ A ]
| EqBetaSnd {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A ] ->
   [ Γ ⊢ b @ B ] ->
   [ Γ ⊢ snd (a, b) == b @ B ]
| EqEtaPair {Γ} {A B} {p} :
   [ Γ ⊢ p @ (A * B) ] ->
   [ Γ ⊢ (fst p, snd p) == p @ (A * B) ]
(** βη-equivalence for abstractions **)
| EqBetaApp {Γ} {A B} {a b} :
   [ Γ ⊢ a @ A ] ->
   [ Γ # A ⊢ b @ B ] ->
   [ Γ ⊢ app( λ (b) , a ) == b [ Id # a ] @ B ]
| EqEtaApp {Γ} {A B} {f} :
   [ Γ ⊢ f @ (A --> B) ] ->
   [ Γ ⊢ f == λ (app(f [p], q)) @ (A --> B) ]
(** Compatibility for substitution **)
| EqSubstIdTerm {Γ} {A a} :
   [ Γ ⊢ a @ A ] ->
   [ Γ ⊢ a [ Id ] == a @ A ]
| EqSubstCompTerm {Γ2 Γ1 Γ0} {y1 y0} {A a} :
   [ Γ2 ⊢ y1 to Γ1 ] ->
   [ Γ1 ⊢ y0 to Γ0 ] ->
   [ Γ0 ⊢ a @ A ] ->
   [ Γ2 ⊢ a [ y0 ∘ y1] == a [y0] [y1] @ A [y0 ∘ y1] ]
| EqBetaQuar {Δ} {Γ} {y} {A} {a} :
   [ Δ ⊢ y to Γ ] ->
   [ Γ ⊢ A type  ] ->
   [ Δ ⊢ a @ A [y] ] ->
   [ Δ ⊢ q [ y # a ] == a @ A[y] ]
where "[ Γ ⊢ a '==' b @ A ]" := (@eq_term Γ A a b) : term_scope.

Definition TermEqJG {Γ : wfCtx} {A : @wfTypes Γ} : relation (@wfTerms Γ A) := @eq_term Γ A.
Lemma TermEqJG_refl {Γ : wfCtx} {A : @wfTypes Γ} (e : @wfTerms Γ A) :
    [Γ ⊢ e == e @ A].
Proof.
   constructor.
   destruct e.
   assumption.
Qed.
Lemma TermEqJG_sym {Γ : wfCtx} {A : @wfTypes Γ} (e1 e2 : @wfTerms Γ A) :
   [Γ ⊢ e1 == e2 @ A ] ->
   [Γ ⊢ e2 == e1 @ A ].
Proof.
   apply EqSymTerm;
   [destruct e1 | destruct e2].
   all: assumption.
Qed.
Lemma TermEqJG_trans {ctx : wfCtx} {A : @wfTypes ctx} (e1 e2 e3 : @wfTerms ctx A) :
   TermEqJG e1 e2 ->
   TermEqJG e2 e3 ->
   TermEqJG e1 e3.
Proof.
   apply EqTransTerm;
   [destruct e1 | destruct e2 | destruct e3].
   all: assumption.
Qed.

Add Parametric Relation (ctx :wfCtx) (A : @wfTypes ctx) : (@wfTerms ctx A) (@TermEqJG ctx A)
   reflexivity proved by (@TermEqJG_refl ctx A)
   symmetry proved by (@TermEqJG_sym ctx A)
   transitivity proved by (@TermEqJG_trans ctx A)
   as TermEqJG_rel.

(*** End Equality for Terms ***)


(** Morphisms **)



Add Parametric Morphism (Γ : preContext) {A} : (TermJG Γ)
   with signature (@eq_type Γ ==> @eq_term Γ A  ==> Basics.impl)
   as TermSubst_mor.
Proof.
   unfold Basics.impl.
   intros.
   induction H;
   try (assumption).
   - intro. eapply term_subs.
   - split; intro. assumption.
      eapply term_snd.
      apply term_pair; eassumption.
   - split; intro. assumption.
      eapply term_pair.
      apply term_abs. assumption.
      apply IHeq_term. assumption.

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

(** End Morphisms **)

(** End Equality Judgements **)


(** Notation coherence **)
Theorem notation_coherence : forall Γ,(
   (forall A, [ Γ ⊢ A type ] -> [ ⊢ Γ Cx ]) /\
   (forall a A, [ Γ ⊢ a @ A ] -> [ Γ ⊢ A type ] ) /\
   (forall Δ y, [ Δ ⊢ y to Γ ] -> [ ⊢ Δ Cx ])
).
Proof.
   intros.
   induction Γ.
   - repeat split.
      + intros. apply context_empty.
      + intros a A; generalize dependent a.   induction A; intros.
         * apply type_base. apply context_empty.
         * apply type_prod; [apply (IHA1 (fst a)) | apply (IHA2 (snd a))].
            apply (term_fst H). apply (term_snd H).
         * rewrite EqEtaAbs in H.
            i
            -- apply (IHA1 (fst a)).
           -- apply (IHA1 (app())).
           --

         apply context_extend.
         apply IHΓ.
         apply type
         * inversion H; subst. assumption.
         * inversion H; subst. apply (IHA1 _ H3).
         * inversion H; subst. apply (IHA1 _ H3).
         * rewrite <- (@type_id_subs A) in H.
            induction y; intros.
               -- rewrite<- EqSubstIdType in H.
               assumption.
               -- apply EqSubst
                  eapply (IHy2).
               -- inversion H; subst. apply context_extend; try assumption.

           apply IHA in H3. assumption.
         * apply context_empty.
         * generalize dependent Γ; induction A; intros.
            -- inversion H; subst. assumption.
            -- inversion H; subst. apply (IHA1 _ IHΓ H3).
            -- inversion H; subst. apply (IHA1 _ IHΓ H3).
            -- apply IHA.
            -- apply IHA.
               inversion H; subst.
               apply IHA in H3. assumption.
            -- assumption.
            -- assumption.
            -- assumption.
            -- assumption.

         * inversion H; subst. apply IHA1 in H3. assumption.
         * inversion H; subst. apply context_extend; try assumption.
           apply IHA in H3. assumption.
      + induction a; intros.
         * inversion H.
         * inversion H; subst.
            apply type_prod.
             apply IHa1 in H4. assumption.
             apply IHa2 in H5. assumption.
         * inversion H; subst.
            apply IHa in H3.
            inversion H3; subst. assumption.
         * inversion H; subst.
            apply IHa in H3.
            inversion H3; subst. assumption.
         * inversion H; subst.
            destruct H3; subst.
            apply type_func.
            -- assumption.
            --
             apply IHa1 in H4. assumption.
             apply IHa2 in H6. assumption.

         * apply type_base. apply context_empty.
         * induction a; intros.
           -- inversion H.
           -- inversion H; subst.
               apply type_prod.
             apply IHA1 in H4. assumption.
             apply IHA2 in H6. assumption.
            -- inversion H; subst.
               apply type_func.
             apply IHA1 in H4. assumption.
             apply IHA2 in H6. assumption.
            eapply IHA1. eassumption.
            destruct H. apply H. assumption.
         apply (IHa2 B); assumption.
         * apply IHa in H3. inversion H3; subst. assumption.
         * apply IHa in H3. inversion H3; subst. assumption.
         * apply type_func.
         induction H3; subst; try assumption.
         apply (IHa1 A); assumption.
           apply IHa in H5. inversion H5; subst. assumption.
   - apply term_subs; assumption.

Lemma wf_subs_wf_context : forall {Δ Γ : preContext} {y: preSubs}, [ Δ ⊢ y # Γ ] -> [ ⊢ Δ Cx ] /\ [ ⊢ Γ Cx ].
   intros Δ Γ y.
   generalize dependent Δ.
   generalize dependent Γ.
   induction y; intros.
   - inversion H; subst. tauto.
   - inversion H; subst.
      apply IHy1 in H3. apply IHy2 in H5.
      destruct H3. destruct H5.
      tauto.
   - inversion H; subst.
      split.
      + apply type_base. assumption.
      + apply type_prod; try assumption.
      + apply type_func; try assumption.
      +
         * apply type_base. assumption.
         * apply type_base. assumption.
      inversion H0; subst.
   - apply IHy1 in H3.
     apply IHy2 in H5.
     destruct H3. destruct H5.
     tauto.
Qed.



Corollary wf_type_wf_context : forall {Γ A}, [ Γ ⊢ A type ] -> [ ⊢ Γ ].
Proof.
   induction Γ; intros.
   - apply context_empty.
   - generalize dependent Γ.
      induction A; intros.
      + inversion H; subst. assumption.
      + inversion H; subst. apply IHA2; assumption.
      + inversion H; subst. apply IHA1; assumption.
      + inversion H; subst. apply context_extend; try assumption.
         apply IHA; assumption.
Qed.


Lemma wf_term_wf_type : forall ctx A t, (wf_Term ctx A t) -> (ctx ⊢ A)%lang.
   intros.
   induction H; try assumption.
   - apply type_prod; assumption.
   - inversion IHwf_Term; assumption.
   - inversion IHwf_Term; assumption.
   - apply type_func. 1,3: assumption.
      inversion IHwf_Term;
      inversion H1;
      try assumption;
      inversion H2;
      try assumption.
   - inversion IHwf_Term1. subst.
      eapply type_subs.
      shelve.
      assumption.
      eapply subs_weak.
      apply H6.
      assumption.
      Unshelve.
      apply (wf_type_wf_context H7).
   -  eapply type_subs.
      3: apply H.
      apply (wf_type_wf_context IHwf_Term).
      2: apply IHwf_Term.
      apply (wf_subs_wf_context H).
Qed.




