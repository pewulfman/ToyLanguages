(* Monoid and binary composition classes *)

Set Implicit Arguments.

Class BinOp (A : Type) := {
  star : A -> A -> A
}.

Class Associative {A : Type} (b : BinOp A) := {
  assoc : forall x y z : A, star x (star y z) = star (star x y) z
}.

Class Neutral {A : Type} (b : BinOp A) := {
  e : A;
  left_id : forall x : A, star e x = x;
  right_id : forall x : A, star x e = x
}.

Class Monoid (A : Type) := {
  mon_binop : BinOp A;
  mon_assoc : Associative mon_binop;
  mon_neutral : Neutral mon_binop
}.

Infix "⋅" := star (at level 40, left associativity).

(* Convenience accessors *)
Arguments star {A} {_} _ _.
Arguments e {A} {_}.
