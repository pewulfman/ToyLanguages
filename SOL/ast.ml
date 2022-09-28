type tvar = string
type vvar = string
type tconst

type ty_expr =
  T_var of tvar
| T_const of tconst
| T_app of (ty_expr * ty_expr) (* sigma -> tau *)
| T_pair of ty_expr * ty_expr  (* sigma A tau *)
| T_union of ty_expr * ty_expr (* sigma V tau *)
| T_universal of tvar * ty_expr
| T_existential of tvar * ty_expr

type va_expr =
  V_var of vvar
  (* for type app*)
| V_lambda of vvar * va_expr (* lambda x : sigma . M *)
| V_app of va_expr * va_expr (* M N *)
| V_let    of vvar * va_expr * va_expr (* let x = N in M := (lambda x : TypeN . M) N *)
  (* for type pair *)
| V_pair   of va_expr * va_expr
| V_fst    of va_expr
| V_snd    of va_expr
  (* for type union *)
| V_left   of va_expr * ty_expr
| V_right  of va_expr * ty_expr
| V_case   of va_expr * (vvar * va_expr) * (vvar * va_expr)
  (* for type universal *)
| V_polymorphic of tvar * va_expr
| V_type_application of tvar * va_expr
  (* for type existential *)
| V_pack  of ty_expr * va_expr * (tvar * ty_expr) (* pack tau M as exist t.sigma *)
| V_abstype of tvar * (tvar * ty_expr) * va_expr * va_expr (* abstype t with x:sigma is N in M *)

