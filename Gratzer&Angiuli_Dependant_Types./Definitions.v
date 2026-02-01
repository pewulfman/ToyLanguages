From Stdlib Require Import Nat String.
From Corelib.Program Require Import Basics Tactics Wf.
From Stdlib.Logic Require Import JMeq.

Require Export Setoid.

Require Export Relation_Definitions.
(* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

(** Syntax **)

(** Pre-syntax definitions **)

(** Convention For syntax sorts. On the left is fonction parameters, on the right construction to stay true to the textbook
   Contexts ctx: greek uppercase letters: 𝚪, Δ, ...
   Types t : uppercase letters: A, B, ...
   Terms e : lowercase letters: a, b, ...
   Substitutions g :  greak lowercase :γ, δ, μ ...
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
| TSubst : preContext
   -> preType
   -> preContext -> preSub
   -> preType
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


(** Syntax Jugements *)

Fixpoint ContextJG (ctx : preContext) {struct ctx} : Prop :=
  match ctx with
  | One => True
  | CExt Γ A => ContextJG Γ /\ TypeJG Γ A
  end

with TypeJG (ctx : preContext) (t : preType) {struct t} : Prop :=
   match t with
   | Base Γ =>
      Γ = ctx /\ ContextJG Γ
   | Func Γ A B =>
      Γ = ctx /\ ContextJG Γ /\
      TypeJG Γ A /\ TypeJG (CExt Γ A) B
   | Prod Γ A B =>
      Γ = ctx /\ ContextJG Γ /\
      TypeJG Γ A /\ TypeJG Γ B
   | TSubst Δ B Γ g =>
       Δ = ctx /\ ContextJG Γ /\ ContextJG Δ /\
       TypeJG Γ B /\
       SubsJG Δ g Γ
   end

   (* In the expression [ Δ ├ y : Γ ] Γ is viewed as the type of y *)
with SubsJG (ctx : preContext) (g : preSub) (t : preContext) {struct g} : Prop :=
  match g with
   | Id Γ => ctx = Γ /\ Γ = t /\ ContextJG Γ
   | Weak Γ A => ctx = CExt Γ A /\ Γ = t /\ ContextJG Γ /\ TypeJG Γ A
   | Comp y0 y1 =>
   exists mid : preContext,
      SubsJG ctx y1 mid /\
      SubsJG mid y0 t
   | Bang Γ => ctx = Γ /\ t = One /\ ContextJG Γ
   | SExt Δ Γ y A a =>
      Δ = ctx /\ ContextJG Δ /\
      CExt Γ A = t /\ ContextJG Γ /\
      TypeJG Γ A /\
      SubsJG Δ y Γ /\
      TermJG Δ (TSubst Δ A Γ y) a
   end

with TermJG (ctx : preContext) (t : preType) (e : preTerm) {struct e} : Prop :=
   match e with
   | Qar (Γ, A) =>
      let OutCtx := CExt Γ A in
      ContextJG Γ /\ TypeJG Γ A /\ ctx = OutCtx /\ t = TSubst OutCtx A Γ (Weak Γ A)
   | Const Γ n => Γ = ctx /\ t = Base Γ /\ ContextJG Γ
   | Pair Γ A a B b =>
      Γ = ctx /\ ContextJG Γ /\
      t = Prod ctx A B /\ TypeJG ctx A /\ TypeJG ctx B /\
      TermJG ctx A a /\
      TermJG ctx B b
   | Fst Γ (A,B) p =>
       Γ = ctx /\ ContextJG Γ /\
       t = A /\ TypeJG ctx A /\ TypeJG ctx B /\
       TermJG ctx (Prod ctx A B) p
   | Snd Γ (A,B) p =>
      Γ = ctx /\ ContextJG Γ /\
      t = B /\ TypeJG ctx A /\ TypeJG ctx B /\
      TermJG ctx (Prod ctx A B) p
   | Lam Γ A B b =>
       Γ = ctx /\ ContextJG Γ /\
         t = Func ctx A B /\ TypeJG ctx A /\ TypeJG (CExt ctx A) B /\
         TermJG (CExt ctx A) B b
   | App Γ A f B a =>
      Γ = ctx /\ ContextJG Γ /\
      t = B /\ TypeJG ctx A /\ TypeJG (CExt ctx A) B /\
      TermJG ctx (Func ctx A B) f /\
      TermJG ctx A a
   | ESubst Δ B a Γ g =>
      Δ = ctx /\ ContextJG Γ /\ ContextJG Δ /\
      t = TSubst Δ B Γ g /\ TypeJG Γ B /\
      TermJG Γ B a /\
      SubsJG Δ g Γ
   end.

Notation "[ ⊢ Γ ]" := (ContextJG Γ) (at level 50).
Notation "[ Δ ⊢ g :s Γ ]" := (SubsJG Δ g Γ) (at level 50).
Notation "[ ctx ⊢ A ]" := (TypeJG ctx A) (at level 50).
Notation "[ ctx ⊢ t :e A ]" := (TermJG ctx A t) (at level 50).


(** End Syntax Judgements **)

(* Example Judgements *)
Example ex0 :
   [ One ⊢ Base One ].
Proof.
   repeat split.
Qed.

Example ex1 :
   let B := Base One in
   [ One ⊢ Func One (Prod One B B) (Base (CExt One (Prod One B B))) ].
Proof.
   intros B.
   constructor. reflexivity.
   split. simpl. tauto.
   split. constructor. reflexivity.
   repeat split.
   constructor. reflexivity.
   repeat split.
Qed.

(** Well-formed syntax types **)
Inductive wfCtx : Type := {
  ctx :> preContext;
  ctx_judg : ContextJG ctx
}.

Inductive wfType {ctx : wfCtx}: Type := {
  t :> preType;
  t_judg : TypeJG ctx t
}.

Inductive wfSub {Δ Γ : wfCtx}: Type := {
  sub :> preSub;
  sub_judg : SubsJG Δ sub Γ
}.

Inductive wfTerm {ctx : wfCtx} (A : @wfType ctx) : Type := {
  term :> preTerm;
  term_judg : TermJG ctx A term
}.

(** End Well-formed syntax **)

(** Well-formed syntax constructors **)

Definition wfBase {ctx : wfCtx} : @wfType ctx.
   refine ({|
      t := Base ctx;
      t_judg := _
   |}).
   destruct ctx as [ctx ctx_judg].
   split; [reflexivity | assumption].
Defined.



Definition wfOneCtx : wfCtx.
   refine ({|
      ctx := One;
      ctx_judg := _
   |}).
   constructor.
Defined.
Notation "1" := (wfOneCtx).

Definition wf_Ext {ctx : wfCtx} (A : @wfType ctx) : @wfCtx.
   refine ({|
      ctx := CExt ctx A;
      ctx_judg := _
      |}).
      destruct ctx as [ctx ctx_judg].
      destruct A as [A A_judg].
      simpl in *.
      split; assumption.
Defined.

Notation "ctx ,c A" := (@wf_Ext ctx A) (at level 50, left associativity).

Definition wf_Id {ctx : wfCtx} : @wfSub ctx ctx.
   refine ({|
      sub := Id ctx;
      sub_judg := _
      |}).
     simpl.
     repeat split.
     apply ctx.
Defined.

Definition wf_Bang {ctx : wfCtx} : @wfSub ctx 1.
   refine ({|
      sub := Bang ctx;
      sub_judg := _
   |}).
   destruct ctx as [ctx ctx_judg].
   simpl in *.
   repeat split; try assumption.
Defined.
Notation "!" := (wf_Bang) (at level 50).

Definition proj {ctx : wfCtx} {A : @wfType ctx} : @wfSub (ctx ,c A) ctx.
   refine ({|
      sub := Weak ctx A;
      sub_judg := _
      |}).
      simpl in *.
      repeat split; try assumption.
      apply ctx. apply A.
Defined.

Definition wfTypeSubst
   {Δ : wfCtx}
   {Γ : wfCtx}
   (A : @wfType Γ)
   (g : @wfSub Δ Γ)
   : @wfType Δ.

   refine ({|
      t := TSubst Δ A Γ g;
      t_judg := _
      |}).
   simpl in *.
   repeat split; try assumption.
   apply Γ.
   apply Δ.
   apply A.
   apply g.
Defined.

Notation "A '[t' g ]" := (wfTypeSubst A g) (at level 50).

Definition wfTermSubst
   {Δ : wfCtx}
   {Γ : wfCtx}
   {A : @wfType Γ}
   (a : @wfTerm Γ A)
   (g : @wfSub Δ Γ)
   : @wfTerm Δ (A [t g]).
   refine ({|
      term := ESubst Δ A a Γ g;
      term_judg := _
   |}).
   simpl in *.
   repeat split; try assumption.
   apply Γ.
   apply Δ.
   apply A.
   apply a.
   apply g.
Defined.
Notation "a '[e' g ]" := (wfTermSubst a g) (at level 50).

Definition wfSub_Ext
   {Δ : wfCtx}
   {Γ : wfCtx}
   {A : @wfType Γ}
   (g : @wfSub Δ Γ)
   (a : @wfTerm Δ (A [t g]))
   : @wfSub (Δ) (Γ ,c A).
   refine ({|
      sub := SExt Δ Γ g A a;
      sub_judg := _
   |}).
   simpl in *.
   repeat split; try assumption.
   apply Δ.
   apply Γ.
   apply A.
   apply g.
   apply a.
Defined.

Notation "g ,s a " := (wfSub_Ext g a) (at level 50).

Definition q {ctx : wfCtx} {A : @wfType ctx} : @wfTerm (ctx ,c A) (A [t proj]).
   refine ({|
      term := Qar ( ctx: preContext ,  A : preType);
      term_judg := _
   |}).
   destruct ctx as [ctx Hctx].
   destruct A as [A HA].
   simpl in *.
   repeat split; try assumption.
Defined.


Definition sub_compose
   (Δ mid Γ : wfCtx)
   (g0 : @wfSub mid Γ)
   (g1 : @wfSub Δ mid) : @wfSub Δ Γ.
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
| EqSubstIdType : forall {Γ : wfCtx} (A : @wfType Γ),
   eq_type (A [t wf_Id ]) (A)
| EqSubstCompType : forall {Δ mid Γ : wfCtx}
(A : @wfType Γ) (g1 : @wfSub Δ mid) (g0 : @wfSub mid Γ),
   eq_type (A [t (g0 ∘ g1)]) ( A [t g0] [t g1])
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

Add Parametric Morphism (Δ Γ : wfCtx) : (wfTypeSubst )
   with signature (@TypeEqJG Γ  ==> eq ==> @TypeEqJG Δ)
   as TypeEqJG_mor.

(*** End Equality for Types ***)

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
| EqLeftId : forall {Δ Γ} (gamma : @wfSub Δ Γ),
   eq_sub (sub wf_Id ∘ gamma) (sub gamma)
| EqRightId : forall {Δ Γ} (gamma : @wfSub Δ Γ),
  eq_sub (sub gamma ∘ wf_Id) (sub gamma)
| EqCompAssoc (ctx0 ctx1 ctx2 ctx3 : wfCtx) (gamma2 : @wfSub ctx3 ctx2) (gamma1 : @wfSub ctx2 ctx1) (gamma0 : @wfSub ctx1 ctx0):
   eq_sub
   (sub_compose ctx3 ctx1 ctx0 gamma0 (sub_compose ctx3 ctx2 ctx1 gamma1 gamma2))
   (sub_compose ctx3 ctx2 ctx0 (sub_compose ctx2 ctx1 ctx0 gamma0 gamma1) gamma2)
| EqCompSub : forall (gamma1 gamma1' gamma2 gamma2' : preSub),
   eq_sub gamma1 gamma1' ->
   eq_sub gamma2 gamma2' ->
   eq_sub (Comp gamma1 gamma2) (Comp gamma1' gamma2')
| EqBang : forall {Γ} (g : @wfSub Γ 1),
   eq_sub (Bang Γ) g
(** Substitution former **)
| EqSubstBeta : forall {Δ Γ : wfCtx}
   {A : @wfType Γ} (g : @wfSub Δ Γ)
   (a : @wfTerm Δ (A [t g])),
      eq_sub (proj ∘ (g ,s a)) g
| EqSubstEta : forall {Δ Γ : wfCtx}
   {A : @wfType Γ}
   (g : @wfSub Δ (Γ ,c A)),
      eq_sub g ((proj ∘ g) ,s (q [e g]))
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


