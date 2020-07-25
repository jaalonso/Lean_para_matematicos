import tactic

#check expr

-- Comentario: Colocar el cursor sonre expr y pulsando M-. se obtiene su
-- definición 
--    meta inductive expr (elaborated : bool := tt)
--    | var         : nat → expr
--    | sort        : level → expr
--    | const       : name → list level → expr
--    | mvar        (unique : name) (pretty : name) (type : expr) : expr
--    | local_const (unique : name) (pretty : name) (bi : binder_info) 
--                  (type : expr) : expr
--    | app         : expr → expr → expr
--    | lam         (var_name : name) (bi : binder_info) (var_type : expr) 
--                  (body : expr) : expr
--    | pi          (var_name : name) (bi : binder_info) (var_type : expr) 
--                  (body : expr) : expr
--    | elet        (var_name : name) (type : expr) (assignment : expr) 
--                  (body : expr) : expr
--    | macro       : macro_def → list expr → expr

open expr

meta def is_constant_of (l : list name) : expr → bool
| (const a a_1) := a ∈ l
| _             := ff

#eval is_constant_of [`nat, `int] `(ℕ)

-- Comentario: Al colocar el cursor sobre eval se obtiene tt

#eval is_constant_of [`nat, `int] `(bool)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff

meta def is_app_of (l : list name) (e: expr) : bool :=
let app_name := e.get_app_fn in
is_constant_of l app_name

#eval is_app_of [`has_le.le, `has_lt.lt] `(20 < 5)

-- Comentario: Al colocar el cursor sobre eval se obtiene tt

#eval is_app_of [`has_le.le, `has_lt.lt] `(20 ≤ 5)

-- Comentario: Al colocar el cursor sobre eval se obtiene tt

#eval is_app_of [`has_le.le, `has_lt.lt] `(20 = 5)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff

meta def mk_app (e1 e2 : expr) : expr :=
app e1 e2

#eval to_string $ mk_app `(nat.succ) `(nat.zero)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    "nat.succ nat.zero"

#eval to_string $ to_raw_fmt $ mk_app `(nat.succ) `(nat.zero)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    "(app (const nat.succ []) (const nat.zero []))"

meta def get_lhs_rhs : expr → option (expr × expr)
| `(%%a < %% b) := some (a, b)
| `(%%a ≤ %% b) := some (a, b)
| _             := none

#eval tactic.trace $ get_lhs_rhs `(2 < 3)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    (some (2, 3))

#eval tactic.trace $ get_lhs_rhs `(2 ≤ 3)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    (some (2, 3))

#eval tactic.trace $ get_lhs_rhs `(2 = 3)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    none

#eval to_string $ to_raw_fmt $ (`(λ x : ℕ, x) : expr)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    "(lam x default (const nat []) (var 0))"

meta def succ_fn : expr → option expr
| (lam var_name bi var_type body) := 
  let new_body := mk_app `(nat.succ) body in
  lam var_name bi var_type new_body
| _                               := none

#eval to_string $ succ_fn `(λ x : ℕ, x)

-- Comentario: Al colocar el cursor sobre eval se obtiene ff
--    "(some fun (x : nat), (nat.succ x))"

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Metaprogramming in Lean tutorial: video 3" de Rob
-- Lewis que se encuentra en https://youtu.be/Y7zjInL82-Q
