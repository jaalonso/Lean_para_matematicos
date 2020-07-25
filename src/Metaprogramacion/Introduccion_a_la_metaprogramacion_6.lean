import tactic

open tactic expr

meta def add_nonneg_proof_aux (n : expr) (h : option name) : tactic unit :=
do pf ← mk_app `nat.zero_le [n],
   nm ← get_unused_name,
   note (h.get_or_else nm) none pf,
   skip

example (n : ℕ) : true :=
begin
  add_nonneg_proof_aux `(55) none,
end

-- Comentario: Al colocar el cursor al final de la primera línea de la
-- demostración se obtiene
--    n : ℕ,
--    _x : 0 ≤ 55
--    ⊢ true

namespace tactic
namespace interactive

setup_tactic_parser

meta def add_nonneg_proof (n : parse parser.pexpr) (h : parse ident?) 
  : tactic unit :=
do n ← to_expr n,
   add_nonneg_proof_aux n h

meta def add_nonneg_proofs (l : parse pexpr_list) : tactic unit :=
do l ← l.mmap to_expr,
   l.mmap' (λ e, add_nonneg_proof_aux e none)

end interactive
end tactic

example (n : ℕ) : true :=
begin
  add_nonneg_proof 55 hx,
end

-- Comentario: Al colocar el cursor al final de la primera línea de la
-- demostración se obtiene
--    n : ℕ,
--    hx : 0 ≤ 55
--    ⊢ true

example (n : ℕ) : true :=
begin
  add_nonneg_proof 55 hx,
  add_nonneg_proofs [n+n+n, 2*n^2],
end

-- Comentario: Al colocar el cursor al final de la primera línea de la
-- demostración se obtiene
--    n : ℕ,
--    hx : 0 ≤ 55,
--    _x : 0 ≤ n + n + n,
--    _x_1 : 0 ≤ 2 * n ^ 2
--    ⊢ true

meta def mk_list : tactic (list ℕ) :=
return [1, 4, 6]

run_cmd  do
  l ← mk_list,
  match l with
  | (h::t) := trace h
  | _      := failed
  end

-- Comentario: Al colocar el cursor sobre run_cmd se obtiene 1.

run_cmd  do
  [a, b, c] ← mk_list,
  trace b

-- Comentario: Al colocar el cursor sobre run_cmd se obtiene 4.

example : true ∧ true :=
by do
  split,
  gs ← get_goals,
  gs.mmap' trace

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    2 goals
--    ⊢ true
--    
--    ⊢ true
--    
--    ?m_1
--    ?m_1

example : true ∧ false :=
by do
  split,
  gs ← get_goals,
  gs.mmap' (λ e, do tp ← infer_type e, trace tp)

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    2 goals
--    ⊢ true
--    
--    ⊢ false
--    
--    true
--    false

example : true ∧ false :=
by do
  split,
  gs ← get_goals,
  gs.mmap' (λ e, trace e.to_raw_fmt)

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    2 goals
--    ⊢ true
--    
--    ⊢ false
--    
--    (mvar _mlocal._fresh.176.839 _mlocal._fresh.176.839 (const 2 []))
--    (mvar _mlocal._fresh.176.840 _mlocal._fresh.176.840 (const 2 []))

example : ∃ x : ℕ, x = x :=
by do
  applyc `exists.intro,
  [e1, e2] ← get_goals,
  infer_type e1 >>= trace,
  infer_type e2 >>= trace

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    2 goals
--    ⊢ ?m_1 = ?m_1
--    
--    ⊢ ℕ
--    
--    ?m_1 = ?m_1
--    ℕ

example : ∃ x : ℕ, x = x :=
by do
  applyc `exists.intro,
  [e1, e2] ← get_goals,
  infer_type e1 >>= trace,
  trace e1.to_raw_fmt,
  infer_type e2 >>= trace,
  trace e2.to_raw_fmt

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    2 goals
--    ⊢ ?m_1 = ?m_1
--    
--    ⊢ ℕ
--    
--    ?m_1 = ?m_1
--    (mvar _mlocal._fresh.215.1681 _mlocal._fresh.215.1681 (const 2 []))
--    ℕ
--    (mvar _mlocal._fresh.215.1680 _mlocal._fresh.215.1680 (const 2 []))

example : ∃ x : ℕ, x = x :=
by do
  applyc `exists.intro,
  [e1, e2] ← get_goals,
  unify e2 `(7),
  trace e2

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    ⊢ 7 = 7
--    
--    7

set_option pp.instantiate_mvars false

example : ∃ x : ℕ, x = x :=
by do
  applyc `exists.intro,
  [e1, e2] ← get_goals,
  unify e2 `(7),
  trace e2,
  trace e2.to_raw_fmt

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    ⊢ ?m_1 = ?m_1
--    
--    ?m_1
--    (mvar _mlocal._fresh.16.1433 _mlocal._fresh.16.1433 (const 2 []))

example : ∃ x : ℕ, x = x :=
by do
  applyc `exists.intro,
  [e1, e2] ← get_goals,
  unify e2 `(7),
  trace e2,
  trace e2.to_raw_fmt,
  e2 ← instantiate_mvars e2,
  trace e2.to_raw_fmt

-- Comentario: Al colocar el cursor sobre do se obtiene 
--    tactic failed, there are unsolved goals
--    state:
--    ⊢ ?m_1 = ?m_1
--    
--    ?m_1
--    (mvar _mlocal._fresh.54.1667 _mlocal._fresh.54.1667 (const 2 []))
--    (app 
--     (app 
--      (app 
--       (app (const bit1 [0]) (const nat [])) 
--       (const nat.has_one [])) (const nat.has_add [])) 
--     (app 
--      (app 
--       (app 
--        (app (const bit1 [0]) (const nat [])) 
--        (const nat.has_one [])) 
--       (const nat.has_add [])) 
--      (app 
--       (app (const has_one.one [0]) (const nat [])) 
--       (const nat.has_one []))))

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Metaprogramming in Lean tutorial: video 6" de Rob
-- Lewis que se encuentra en https://youtu.be/ZbijjKFtvJI
