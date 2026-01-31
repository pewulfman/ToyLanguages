From Stdlib Require Import Nat String.
From Corelib.Program Require Import Basics Tactics Wf.
From Stdlib.Logic Require Import JMeq.

Require Export Setoid.

Require Export Relation_Definitions.
(* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

(** Syntax **)

(** Pre-syntax definitions **)

(** Convention For syntax sorts.
   Contexts ctx: greek uppercase letters: Gamma, Delta, ...
   Types t : uppercase letters: A, B, ...
   Terms e : lowercase letters: a, b, ...
   Substitutions g :  indexed g : g0, g1, ...
**)

Inductive preContext : Set :=
  One : preContext
| CExt: preContext -> preType -> preContext
with preSub : Set :=
| Id : preContext -> preSub
| Weak : preContext -> preType -> preSub
| Comp : preSub -> preSub -> preSub
(** Terminal subst **)
| Bang : preContext -> preSub
(** Extension **)
| SExt : preContext
   -> preContext -> preSub
   -> preType -> preTerm
   -> preSub
with preType : Set :=
| Base : preContext -> preType
| Func : preContext -> preType -> preType -> preType
| Prod : preContext -> preType -> preType -> preType
| TSubst : preContext -> preType -> preSub -> preType
with preTerm : Set :=
| Qar : (preContext * preType) -> preTerm
| Const : preContext -> nat -> preTerm
| Pair :  preContext
   -> preType -> preTerm
   -> preType -> preTerm
   -> preTerm
| Fst : preContext
   -> preType * preType -> preTerm
   -> preTerm
| Snd : preContext
   -> preType * preType -> preTerm
   -> preTerm
| Lam : preContext
   -> preType
   -> preType -> preTerm
   -> preTerm
| App : preContext
   -> preType -> preTerm
   -> preType -> preTerm
   -> preTerm
| ESubst : preContext
   -> preType -> preTerm
   -> preContext -> preSub
   -> preTerm
.

Scheme preContext_Type_rec := Induction for preContext Sort Set
   with preType_Context_rec := Induction for preType Sort Set.

About preContext_Type_rec.

Scheme preSub_Context_rec := Induction for preSub Sort Set
   with preContext_Sub_rec := Induction for preTerm Sort Set.
About preSub_Context_rec.

Scheme preType_Context_Sub_rec := Induction for preType Sort Set
   with preContext_Sub_Type_rec := Induction for preContext Sort Set
   with preSub_Type_Context_rec := Induction for preSub Sort Set.
About preType_Context_Sub_rec.

Scheme preTerm_Context_Sub_Type_rec := Induction for preTerm Sort Set
   with preContext_Sub_Type_Term_rec := Induction for preContext Sort Set
   with preSub_Type_Term_Context_rec := Induction for preSub Sort Set
   with preType_Term_Context_Sub_rec := Induction for preType Sort Set.
About preTerm_Context_Sub_Type_rec.

Notation "ctx ,c A" := (CExt ctx A) (at level 50, left associativity).

Notation "A --> B" := (Func _ A B) (at level 55,  right associativity).
Notation "A ** B" := (Prod _ A B) (at level 60, right associativity).

Notation "A '[t' g ]" := (TSubst _ A g) (at level 50).
Notation "a '[e' g ]" := (ESubst _ a g) (at level 50).

(* Notation "g ,s a " := (SExt g a) (at level 50). *)

(** Syntax Jugements *)

Fixpoint ContextJG (ctx : preContext) {struct ctx} : Prop :=
  match ctx with
  | One => True
  | CExt Gamma A => ContextJG Gamma /\ TypeJG Gamma A
  end
  with
   SubsJG (Delta : preContext) (g : preSub) (Gamma : preContext) {struct g} : Prop :=
  (* Presupose *)
  match g with
   | Id ctx => Delta = ctx /\ ctx = Gamma /\ ContextJG ctx
   | Weak ctx A => Delta = ctx ,c A /\ ctx = Gamma /\ ContextJG ctx /\ TypeJG ctx A
   | Comp g0 g1 =>
       exists ctx1,
       (* Delta = ctx2, Gamma = ctx0 *)
       SubsJG Delta g1 ctx1 /\
       SubsJG ctx1 g0 Gamma
   | Bang ctx => Delta = ctx /\Gamma = One /\ ContextJG ctx
   | SExt ctx ctx' g A a =>
         ctx = Delta /\ ContextJG ctx /\
         Gamma = ctx',c A /\ ContextJG ctx' /\
         SubsJG Delta g ctx' /\
         TypeJG ctx' A /\
         TermJG ctx (TSubst ctx' A g) a
  end

  with TypeJG (ctx : preContext) (A : preType) {struct A} : Prop :=
   match A with
   | Base Gamma => Gamma = ctx /\ ContextJG Gamma
   | Func Gamma A1 A2 =>
      Gamma = ctx /\ ContextJG Gamma /\
       TypeJG ctx A1 /\ TypeJG ctx A2
   | Prod Gamma A1 A2 =>
      Gamma = ctx /\ ContextJG Gamma /\
       TypeJG ctx A1 /\ TypeJG ctx A2
   | TSubst Gamma A g =>
         Gamma = ctx /\ ContextJG Gamma /\
         TypeJG Gamma A /\
         SubsJG ctx g Gamma
   end

  with TermJG (ctx : preContext) (ty : preType) (e : preTerm) {struct e} : Prop :=
  match e with
   | Qar (Gamma, A) => ContextJG Gamma /\ TypeJG Gamma A /\
       ty = A /\ Gamma = ctx
   | Const Gamma n => Gamma = ctx /\ ty = Base Gamma /\ ContextJG Gamma
   | Pair Gamma A1 a A2 b =>
       Gamma = ctx /\ ContextJG Gamma /\
       TypeJG ctx A1 /\ TypeJG ctx A2 /\
       ty = Prod ctx A1 A2 /\
       TermJG ctx A1 a /\
       TermJG ctx A2 b
   | Fst Gamma (A,B) p =>
       Gamma = ctx /\ ContextJG Gamma /\
       ty = A /\ TypeJG ctx A /\ TypeJG ctx B /\
       TermJG ctx (Prod ctx A B) p
   | Snd Gamma (A,B) p =>
       Gamma = ctx /\ ContextJG Gamma /\
       ty = B /\ TypeJG ctx A /\ TypeJG ctx B /\
       TermJG ctx (Prod ctx A B) p
   | Lam Gamma A B b =>
       Gamma = ctx /\ ContextJG Gamma /\
         ty = Func ctx A B /\ TypeJG ctx A /\ TypeJG (ctx ,c A) B /\
         TermJG (ctx ,c A) B b
   | App Gamma A f B a =>
       Gamma = ctx /\ ContextJG Gamma /\
         ty = B /\ TypeJG ctx A /\ TypeJG (ctx ,c A) B /\
         TermJG ctx (Func ctx A B) f /\
         TermJG ctx A a
   | ESubst Gamma B a Delta g =>
       Gamma = ctx /\ ContextJG Gamma /\
         ty = TSubst ctx B g /\ TypeJG Delta B /\
         TermJG Delta B a /\
         SubsJG Gamma g Delta
   end
  .

Notation "[ ⊢ ctx ]" := (ContextJG ctx) (at level 50).
Notation "[ Delta ⊢ g :s Gamma ]" := (SubsJG Delta g Gamma) (at level 50).
Notation "[ ctx ⊢ A ]" := (TypeJG ctx A) (at level 50).
Notation "[ ctx ⊢ t ; A ]" := (TermJG ctx A t) (at level 50).

(** End Syntax Judgements **)

(* Example Judgements *)
Example ex1 :
   let B := Base One in
   [ One ⊢ Func One (Prod One B B) B ].
Proof.
  repeat split.
Qed.

(** Well-formed syntax types **)

Inductive wfCtx : Type := {
  ctx :> preContext;
  ctx_judg : ContextJG ctx
}.

Inductive wfType (ctx : wfCtx) : Type := {
  ty :> preType;
  ty_judg : TypeJG ctx ty
}.

Definition wfOne : wfCtx.
   refine ({|
      ctx := One;
      ctx_judg := _
   |}).
   constructor.
Defined.
Notation "1" := (wfOne).

Definition wf_Ext {ctx : wfCtx} (A : @wfType ctx) : wfCtx.
   refine ({|
      ctx := ctx ,c A;
      ctx_judg := _
      |}).
      destruct ctx as [ctx ctx_judg].
      destruct A as [A A_judg].
      simpl in *.
      split; assumption.
Defined.
Notation "ctx ,c A" := (@wf_Ext ctx A) (at level 50, left associativity).
Inductive wfSub {Delta Gamma : wfCtx}: Type := {
  sub :> preSub;
  sub_judg : SubsJG Delta sub Gamma
}.

Definition wf_Id {ctx : wfCtx} : @wfSub ctx ctx.
   refine ({|
      sub := Id ctx;
      sub_judg := _
   |}).
   destruct ctx as [ctx ctx_judg].
   simpl.
   tauto.
Defined.

Definition proj {ctx : wfCtx} {A : @wfType ctx} : @wfSub (ctx ,c A) ctx.
   refine ({|
      sub := Weak ctx A;
      sub_judg := _
   |}).
   destruct ctx as [ctx ctx_judg].
   destruct A as [A A_judg].
   simpl in *.
   repeat split;
   assumption.
Defined.

Inductive wfTerm (ctx : wfCtx) (A : wfType ctx) : Type := {
  term :> preTerm;
  term_judg : TermJG ctx A term
}.

(** End Well-formed syntax types **)

Definition sub_compose
   (Delta mid Gamma : wfCtx)
   (g0 : @wfSub mid Gamma)
   (g1 : @wfSub Delta mid) : @wfSub Delta Gamma.
Proof.
   refine ({|
      sub := Comp g0 g1;
      sub_judg := _
   |}).
   destruct g0 as [g0 H0].
   destruct g1 as [g1 H1].
   simpl.
   exists mid.
   split; assumption.
Defined.
Notation "gamma1 '∘' gamma2" := (sub_compose _ _ _ gamma1 gamma2) (at level 40, left associativity).


(** Equality Judgements   **)

(*** Equality of substitutions ***)
Inductive eq_sub :  relation (preSub) :=
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
| EqLeftId : forall {Delta Gamma} (gamma : @wfSub Delta Gamma),
   eq_sub (sub wf_Id ∘ gamma) (sub gamma)
| EqRightId : forall {Delta Gamma} (gamma : @wfSub Delta Gamma),
  eq_sub (sub gamma ∘ wf_Id) (sub gamma)
| EqCompAssoc (ctx0 ctx1 ctx2 ctx3 : wfCtx) (gamma2 : @wfSub ctx3 ctx2) (gamma1 : @wfSub ctx2 ctx1) (gamma0 : @wfSub ctx1 ctx0):
   eq_sub
   (sub_compose ctx3 ctx1 ctx0 gamma0 (sub_compose ctx3 ctx2 ctx1 gamma1 gamma2))
   (sub_compose ctx3 ctx2 ctx0 (sub_compose ctx2 ctx1 ctx0 gamma0 gamma1) gamma2)
| EqCompSub : forall (gamma1 gamma1' gamma2 gamma2' : preSub),
   eq_sub gamma1 gamma1' ->
   eq_sub gamma2 gamma2' ->
   eq_sub (Comp gamma1 gamma2) (Comp gamma1' gamma2')
| EqBang : forall {Gamma} (g : @wfSub Gamma 1),
   eq_sub (Bang Gamma) g
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

Notation "[ Delta ⊢ g1 '==' g2 :s Gamma ]" := (@SubsEqJG Delta Gamma g1 g2) (at level 50).

Add Parametric Morphism (Delta mid Gamma : wfCtx) : (@sub_compose Delta mid Gamma)
   with signature (@SubsEqJG mid Gamma  ==> @SubsEqJG Delta mid ==> @SubsEqJG Delta Gamma)
   as SubsEqJG_mor.
Proof.
   unfold SubsEqJG in *.
   simpl.
   intros gamma1 gamma2 H12.
   intros gamma1' gamma2' H12'.
   apply EqCompSub; assumption.
Qed.


(*** End Equality of substitutions ***)

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
| EqSubstIdType : forall {ctx : wfCtx} (A : @wfType ctx),
   eq_type (TSubst ctx A (Id ctx)) (A)
| EqSubstCompType : forall {Delta mid Gamma : wfCtx}
(A : @wfType Gamma) (g1 : @wfSub Delta mid) (g0 : @wfSub mid Gamma),
   eq_type (TSubst Delta A (g0 ∘ g1)) (TSubst mid (TSubst Gamma A g0) g1)
.

Definition TypeEqJG {ctx : wfCtx} : relation (@wfType ctx) := eq_type.
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

Notation "[ ctx ⊢ A1 '==' A2 ]" := (@TypeEqJG ctx A1 A2) (at level 50).

(*** End Equality for Types ***)


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
| EqSubstCompTerm : forall {Delta mid Gamma : wfCtx}
   {A : @wfType Gamma} (a : @wfTerm Gamma A)
   (g1 : @wfSub Delta mid) (g0 : @wfSub mid Gamma),
      eq_term (ESubst Delta A a Gamma (g0 ∘ g1)) (ESubst Delta (TSubst Gamma A g0) (ESubst mid A a Gamma g0) mid g1)
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


