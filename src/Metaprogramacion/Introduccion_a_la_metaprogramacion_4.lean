import tactic

open tactic

meta def make_a_nat : tactic ℕ :=
return 14

meta def trace_a_nat : tactic unit :=
do n ← make_a_nat,
   trace n

run_cmd trace_a_nat

-- Comentario: Al colocar el cursor sobre run_cmd se obtiene 14.

example (a b c : ℤ) : false :=
begin 
  trace_a_nat,
  sorry,
end

-- Comentario: Al colocar el cursor sobre trace_a_nat se obtiene 14.

meta def inspect : tactic unit :=
do t ← target,
   trace t,
   a_expr ← get_local `a <|> fail "No hay ninguna a",
   trace (expr.to_raw_fmt a_expr),
   a_type ← infer_type a_expr,
   trace a_type,
   ctx <- local_context,
   trace ctx,
   let new_nat := 40,
   trace new_nat,
   ctx' ← ctx.mmap (λ e, infer_type e),
   trace ctx'

example (a b c : ℤ) (p q : ℕ) : c = b :=
by do inspect


-- Comentario: Al colocar el cursor sobre do se obtiene
--    c = b
--    (local_const 0._fresh.476.10 a (const 1 []))
--    ℤ
--    [a, b, c, p, q]
--    40
--    [ℤ, ℤ, ℤ, ℕ, ℕ]

meta def inspect2 : tactic unit :=
do t ← target,
   trace t,
   a_expr ← get_local `a <|> fail "No hay ninguna a",
   trace (expr.to_raw_fmt a_expr),
   a_type ← infer_type a_expr,
   trace a_type,
   ctx <- local_context,
   trace ctx,
   let new_nat := 40,
   trace new_nat,
   ctx' ← ctx.mmap (λ e, infer_type e),
   trace ctx',
   ctx.mmap' (λ e, do tp ← infer_type e, trace tp)

example (a b c : ℤ) (p q : ℕ) : c = b :=
by do inspect2

-- Comentario: Al colocar el cursor sobre do se obtiene
--    c = b
--    (local_const 0._fresh.619.1 a (const 1 []))
--    ℤ
--    [a, b, c, p, q]
--    40
--    [ℤ, ℤ, ℤ, ℕ, ℕ]
--    ℤ
--    ℤ
--    ℤ
--    ℕ
--    ℕ

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Metaprogramming in Lean tutorial: video 4" de Rob
-- Lewis que se encuentra en https://youtu.be/qsmnBNXgZgc
