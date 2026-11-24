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
| psub_weak : preSubs
| psub_Bang : preSubs
| psub_comp (y1 y2 : preSubs) : preSubs
| psub_ext  (y : preSubs) (a : preTerm) : preSubs
.

Declare Scope ctx_scope.
Open Scope ctx_scope.

Notation "1" := pctx_one.
Notation "Γ & A" := (pctx_ext Γ A) (at level 1, left associativity, format "Γ & A") : ctx_scope.

#[add_top] Bind Scope ctx_scope with preContext preType.


Check (1).

Declare Scope ty_scope.
Open Scope ty_scope.

Notation base := ptyp_base.
Infix "*"      := ptyp_prod (at level 40,left associativity): ty_scope.
Infix "->"     := ptyp_func : ty_scope.
Notation "A [ y ]" := (ptyp_subs A y) : ty_scope.

#[add_top] Bind Scope ty_scope with preType preSubs preContext.

Check (base).
Check (1 & base).
Check (base * base -> base).
Check ( (base * base -> base) [ psub_id ] ).

Declare Scope term_scope.
Open Scope term_scope.

Notation q := ptrm_qar.
Notation "( a , b )" := (ptrm_pair a b) (no associativity): term_scope.
Notation "'fst' p" := (ptrm_fst p) (at level 20): term_scope.
Notation "'snd' p" := (ptrm_snd p) (at level 20): term_scope.
Notation "'λ' ( b )" := (ptrm_abs b) (at level 20): term_scope.
Notation "app( f , a )" := (ptrm_app f a) (at level 20): term_scope.
Notation "a [ y ]" := (ptrm_subs a y): term_scope.

#[add_top] Bind Scope term_scope with preTerm preSubs.

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
Notation "y & a" := (psub_ext y a)(at level 1, left associativity, format "y & a") : subs_scope.

#[add_top] Bind Scope subs_scope with preSubs preTerm.

Check ( Id ).
Check ( p ).
Check ( ! ).
Check ( Id ∘ p ).
Check ( Id & q ).

Print Scopes.
Print Visibility.

Fixpoint ContextJG (Γ : preContext) {struct Γ} : Prop :=
   match Γ with
   | 1 => True
   | pctx_ext Γ0 A => ContextJG Γ0 /\ TypeJG Γ0 A
   end

with TypeJG (Γ : preContext) (T : preType) {struct T} : Prop :=
   match T with
   | base => True
   | A * B => TypeJG Γ A /\ TypeJG Γ B
   | A -> B => TypeJG Γ A /\ TypeJG (Γ & A) B
   | ptyp_subs A y => exists Δ, SubsJG Δ y Γ /\ TypeJG Δ A
   end

with TermJG (Γ : preContext) (T : preType) (e : preTerm) {struct e} : Prop :=
   match e with
   | ptrm_qar => True
   | ptrm_pair a b =>
      exists A B,
         TermJG Γ A a /\
         TermJG Γ B b /\
         A * B = T
   | ptrm_fst ab =>
      exists B,
         TermJG Γ (T * B) ab
   | ptrm_snd ab =>
      exists A,
         TermJG Γ (A * T) ab
   | ptrm_abs b =>
      exists A B,
         TermJG (Γ & A) B b /\
         ptyp_func A B = T
   | ptrm_app f a =>
      exists A,
         TermJG Γ (ptyp_func A T) f /\
         TermJG Γ A a
   | ptrm_subs a y =>
      exists Δ A,
         SubsJG Δ y Γ /\
         TermJG Δ A a /\
         T = ptyp_subs A y
   end


with SubsJG (Δ : preContext) (y : preSubs) (Γ : preContext) {struct y} : Prop :=
   match y with
   | Id =>
       Δ = Γ
   | p =>
      exists A,
         Δ = pctx_ext Γ A
   | ! =>   Γ = 1
   | y1 ∘ y0 =>
         exists Γ1,
            SubsJG Δ y1 Γ1 /\
            SubsJG Γ1 y0 Γ
   | y & a =>
      exists A,
         TermJG Δ A a /\
         exists Γ0,
            SubsJG Δ y Γ0 /\
            Γ = pctx_ext Γ0 A
   end.

(** Well-formed syntax types **)
Record wfCtx : Type := {
  ctx :> preContext;
  ctx_judg : ContextJG ctx
}.

Inductive wfType {ctx : wfCtx}: Type := {
  t :> preType;
  t_asum : ContextJG ctx;
  t_judg : TypeJG ctx t
}.

Inductive wfSub {Δ Γ : wfCtx}: Type := {
  sub :> preSubs;
  sub_asum : ContextJG Δ /\ ContextJG Γ;
  sub_judg : SubsJG Δ sub Γ
}.

Inductive wfTerm {ctx : wfCtx} (A : @wfType ctx) : Type := {
  term :> preTerm;
  term_asum : ContextJG ctx /\ TypeJG ctx A;
  term_judg : TermJG ctx A term
}.


Notation "[ ⊢ Γ ]"       := (ContextJG Γ) : ctx_scope.
Notation "[ Γ ⊢ A ]"     := (ContextJG Γ /\ TypeJG Γ A) : ty_scope.
Notation "[ Γ ⊢ a @ A ]" := (ContextJG Γ /\ TypeJG Γ A /\ TermJG Γ A a) : term_scope.
Notation "[ Δ ⊢ y # Γ ]" := (ContextJG Δ /\ ContextJG Γ /\ SubsJG Δ y Γ) : subs_scope.




Example Ex1 : ([1 ⊢ base * base -> base]).
Proof.
   simpl.
   tauto.
Qed.


Corollary wf_type_wf_context : forall {Γ A}, [ Γ ⊢ A ] -> [ ⊢ Γ ].
   intros.
   inversion H; subst; try assumption.
Qed.


Lemma wf_term_wf_type : forall {Γ A} {a}, [ Γ ⊢ a @ A ] -> [ Γ ⊢ A ].
   intros.
   split;
   (* Todo : replace with tatic that split all /\ *)
   inversion H as [H0 H1]; inversion H1; subst; try assumption.
Qed.


Lemma wf_subs_wf_context : forall {Δ Γ : preContext} {y: preSubs}, [ Δ ⊢ y # Γ ] -> [ ⊢ Δ ] /\ [ ⊢ Γ ].
   intros.
   split;
   (* Todo : replace with tatic that split all /\ *)
   inversion H as [H0 H1]; inversion H1; subst; try assumption.
Qed.


(*** Equality for Types ***)
Inductive eq_type : relation preType :=
(** Enforce equivalence **)
| EqReflType : forall A, eq_type A A
| EqSymType : forall A1 A2,
   eq_type A1 A2 ->
   eq_type A2 A1
| EqTransType : forall A1 A2 A3,
   eq_type A1 A2 ->
   eq_type A2 A3 ->
   eq_type A1 A3
(** Enforce compatibility with substitution **)
| EqSubstIdType : forall A,
   eq_type (A [ Id ] : preType) (A)
| EqSubstCompType : forall A g1 g0,
   eq_type (A [ (g0 ∘ g1)] : preType) ( (A [g0] : preType) [ g1] : preType)
.

Definition TypeEqJG {ctx} : relation (@wfType ctx) := eq_type.
Lemma TypeEqJG_refl {ctx : wfCtx} (A : @wfType ctx) :
    TypeEqJG A A.
Proof.
   constructor.
Qed.
Lemma TypeEqJG_sym {ctx : wfCtx} (A1 A2 : @wfType ctx) :
   TypeEqJG A1 A2  ->
   TypeEqJG A2 A1.
Proof.
   constructor.
   exact H.
Qed.
Lemma TypeEqJG_trans {ctx : wfCtx} (A1 A2 A3 : @wfType ctx) :
   TypeEqJG A1 A2 ->
   TypeEqJG A2 A3 ->
   TypeEqJG A1 A3.
Proof.
   apply EqTransType.
Qed.

Add Parametric Relation (ctx :wfCtx) : (@wfType ctx) (@TypeEqJG ctx)
   reflexivity proved by (@TypeEqJG_refl ctx)
   symmetry proved by (@TypeEqJG_sym ctx)
   transitivity proved by (@TypeEqJG_trans ctx)
   as TypeEqJG_rel.

Notation "ctx ⊢ A1 '==' A2" := (@TypeEqJG ctx A1 A2) (at level 50) : ty_scope.

Definition wfTypeSubst
   {Δ : wfCtx}
   {Γ : wfCtx}
   (A : @wfType Δ)
   (y : @wfSub Δ Γ)
   : @wfType Γ.

   refine ({|
      t := ptyp_subs A y;
      t_asum := _;
      t_judg := _
      |}).
   apply Γ.
   simpl in *.
   exists Δ.
   split; [apply y | apply A ].
Defined.

Add Parametric Morphism (Δ Γ : wfCtx) : (wfTypeSubst )
   with signature (@TypeEqJG Γ  ==> eq ==> @TypeEqJG Δ)
   as TypeEqJG_mor.

(*** End Equality for Types ***)

Definition wfOneCtx : wfCtx.
   refine ({|
      ctx := 1;
      ctx_judg := _
   |}).
   constructor.
Defined.
Notation "1" := (wfOneCtx).

(*** Equality of substitutions ***)
Inductive eq_sub :  relation (preSubs) :=
(** Enforce equivalence **)
| EqReflSub : forall gamma, eq_sub gamma gamma
| EqSymSub : forall gamma1 gamma2,
   eq_sub gamma1 gamma2 ->
   eq_sub gamma2 gamma1
| EqTransSub : forall gamma1 gamma2 gamma3,
   eq_sub gamma1 gamma2 ->
   eq_sub gamma2 gamma3 ->
   eq_sub gamma1 gamma3
(** Enforce compatibility with composition **)
| EqLeftId : forall {Δ Γ} (gamma : @wfSub Δ Γ),
   eq_sub (Id ∘ gamma) (sub gamma)
| EqRightId : forall {Δ Γ} (gamma : @wfSub Δ Γ),
  eq_sub (gamma ∘ Id) (sub gamma)
| EqCompAssoc (ctx0 ctx1 ctx2 ctx3 : wfCtx) (gamma2 : @wfSub ctx3 ctx2) (gamma1 : @wfSub ctx2 ctx1) (gamma0 : @wfSub ctx1 ctx0):
   eq_sub
   (gamma0 ∘ (gamma1 ∘ gamma2))
   ( (gamma0 ∘ gamma1) ∘ gamma2)
| EqCompSub : forall (Γ Γ' Δ Δ' : preSubs),
   eq_sub Γ Γ' ->
   eq_sub Δ Δ' ->
   eq_sub (Δ ∘ Γ) (Δ' ∘ Γ')

| EqBang : forall {Γ} (y : @wfSub Γ 1),
   eq_sub (!) y
(** Substitution former **)
| EqSubstBeta : forall a y,
      eq_sub (p ∘ (y & a)) y
| EqSubstEta : forall y,
      eq_sub y ((p ∘ y) & (q [y]))
.



Definition SubsEqJG {delta : wfCtx} {ctx : wfCtx} : relation (@wfSub delta ctx) := eq_sub.

Lemma SubsEqJG_refl {delta : wfCtx} {ctx : wfCtx} (gamma : @wfSub delta ctx) :
    SubsEqJG gamma gamma.
Proof.
   constructor.
Qed.

Lemma SubsEqJG_sym {delta ctx : wfCtx} (gamma gamma' : @wfSub delta ctx) :
   SubsEqJG gamma gamma'  ->
   SubsEqJG gamma' gamma.
Proof.
   constructor.
   exact H.
Qed.
   (* intros H.
   unfold SubsEqJG in *.
   induction H; subst; constructor.
   all: assumption.
Qed. *)

Lemma SubsEqJG_trans {delta ctx : wfCtx} (gamma1 gamma2 gamma3 : @wfSub delta ctx) :
   SubsEqJG gamma1 gamma2 ->
   SubsEqJG gamma2 gamma3 ->
   SubsEqJG gamma1 gamma3.
Proof.
   apply EqTransSub.
Qed.

Add Parametric Relation (delta ctx :wfCtx) : (@wfSub delta ctx) (@SubsEqJG delta ctx)
   reflexivity proved by (@SubsEqJG_refl delta ctx)
   symmetry proved by (@SubsEqJG_sym delta ctx)
   transitivity proved by (@SubsEqJG_trans delta ctx)
   as SubsEqJG_rel.

Notation "[ Δ ⊢ g1 '==' g2 :s Γ ]" := (@SubsEqJG Δ Γ g1 g2) (at level 50).

Add Parametric Morphism (Δ mid Γ : wfCtx) : (@sub_compose Δ mid Γ)
   with signature (@SubsEqJG mid Γ  ==> @SubsEqJG Δ mid ==> @SubsEqJG Δ Γ)
   as SubsEqJG_mor.
Proof.
   unfold SubsEqJG in *.
   simpl.
   intros gamma1 gamma2 H12.
   intros gamma1' gamma2' H12'.
   apply EqCompSub; assumption.
Qed.


(*** End Equality of substitutions ***)



(*** Equality for Terms ***)
Inductive eq_term : relation preTerm :=
(** Enforce equivalence **)
| EqReflTerm : forall t, eq_term t t
| EqSymTerm : forall t1 t2,
   eq_term t1 t2 ->
   eq_term t2 t1
| EqTransTerm : forall t1 t2 t3,
   eq_term t1 t2 ->
   eq_term t2 t3 ->
   eq_term t1 t3
(** Enforce compatibility with substitution **)
| EqSubstIdTerm: forall {ctx : wfCtx} {A : @wfType ctx} (a : @wfTerm ctx A),
   eq_term (ESubst ctx A a ctx (Id ctx)) (a)
| EqSubstCompTerm : forall {Δ mid Γ : wfCtx}
   {A : @wfType Γ} (a : @wfTerm Γ A)
   (g1 : @wfSub Δ mid) (g0 : @wfSub mid Γ),
      eq_term (a [e g0 ∘ g1]) (a [e g0] [e g1])
(** Substitution former **)
| EqSubstBetaTerm : forall {Δ Γ : wfCtx}
   {A : @wfType Γ} (g : @wfSub Δ Γ)
   (a : @wfTerm Δ (A [t g])) ,
      eq_term (q [e g ,s a]) a
.
Definition TermEqJG {ctx : wfCtx} {A : @wfType ctx} : relation (@wfTerm ctx A) := eq_term.
Lemma TermEqJG_refl {ctx : wfCtx} {A : @wfType ctx} (t : @wfTerm ctx A) :
    TermEqJG t t.
Proof.
   constructor.
Qed.
Lemma TermEqJG_sym {ctx : wfCtx} {A : @wfType ctx} (t1 t2 : @wfTerm ctx A) :
   TermEqJG t1 t2  ->
   TermEqJG t2 t1.
Proof.
   constructor.
   exact H.
Qed.
Lemma TermEqJG_trans {ctx : wfCtx} {A : @wfType ctx} (t1 t2 t3 : @wfTerm ctx A) :
   TermEqJG t1 t2 ->
   TermEqJG t2 t3 ->
   TermEqJG t1 t3.
Proof.
   apply EqTransTerm.
Qed.

Add Parametric Relation (ctx :wfCtx) (A : @wfType ctx) : (@wfTerm ctx A) (@TermEqJG ctx A)
   reflexivity proved by (@TermEqJG_refl ctx A)
   symmetry proved by (@TermEqJG_sym ctx A)
   transitivity proved by (@TermEqJG_trans ctx A)
   as TermEqJG_rel.
Notation "[ ctx ⊢ t1 '==' t2 ; A ]" := (@TermEqJG ctx A t1 t2) (at level 50).

(*** End Equality for Terms ***)

(** End Equality Judgements **)




