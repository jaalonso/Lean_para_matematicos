import tactic

open tactic expr

------------------------------------------------------------------------
-- § Definición de la táctica assumption                              --
------------------------------------------------------------------------

-- 1ª versión
-- ==========

meta def test (hyp tgt : expr) : tactic bool :=
do hyp_tp ← infer_type hyp,
   return (hyp_tp = tgt)

meta def map_over_lc (tgt : expr) : list expr → tactic unit 
| []     := fail "nada del contexto coincide con el objetivo"
| (h::t) := do is_match ← test h tgt,
               if is_match then exact h
                           else map_over_lc t

meta def assump : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   map_over_lc tgt ctx

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  (hC : C)
  : C :=
by assump

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  : C :=
by assump

-- Comentario: Al colocar el cursor sobre assump se obtiene
--    nada del contexto coincide con el objetivo
--    state:
--    A B C : Prop,
--    hA : A,
--    hB : B
--    ⊢ C

-- 2ª versión
-- ==========

meta def test2 (hyp tgt : expr) : tactic unit :=
do hyp_tp ← infer_type hyp,
   guard (hyp_tp = tgt)

meta def map_over_lc2 (tgt : expr) : list expr → tactic unit 
| []     := fail "nada del contexto coincide con el objetivo"
| (h::t) := (do test2 h tgt, exact h) <|> map_over_lc2 t

meta def assump2 : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   map_over_lc2 tgt ctx

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  (hC : C)
  : C :=
by assump2

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  : C :=
by assump2

-- Comentario: Al colocar el cursor sobre assump se obtiene
--    nada del contexto coincide con el objetivo
--    state:
--    A B C : Prop,
--    hA : A,
--    hB : B
--    ⊢ C

-- 3ª versión
-- ==========

meta def test_and_exact (hyp tgt : expr) : tactic unit :=
do hyp_tp ← infer_type hyp,
   guard (hyp_tp = tgt),
   exact hyp

meta def map_over_lc3 (tgt : expr) : list expr → tactic unit 
| []     := fail "nada del contexto coincide con el objetivo"
| (h::t) := test_and_exact h tgt <|> map_over_lc3 t

meta def assump3 : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   map_over_lc3 tgt ctx

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  (hC : C)
  : C :=
by assump3

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  : C :=
by assump3

-- Comentario: Al colocar el cursor sobre assump se obtiene
--    nada del contexto coincide con el objetivo
--    state:
--    A B C : Prop,
--    hA : A,
--    hB : B
--    ⊢ C

-- 4ª versión
-- ==========

meta def assump4 : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   ctx.mfirst (λ e, test_and_exact e tgt)

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  (hC : C)
  : C :=
by assump4

example
  (A B C : Prop)
  (hA : A)
  (hB : B)
  : C :=
by assump4

-- Comentario: Al colocar el cursor sobre assump se obtiene
--    failed
--    state:
--    A B C : Prop,
--    hA : A,
--    hB : B
--    ⊢ C


example (n : ℕ) (hx : n + 0 = 5) : n = 5 :=
by assump4

-- Comentario: Al colocar el cursor sobre assump se obtiene
--    failed
--    state:
--    n : ℕ,
--    hx : n + 0 = 5
--    ⊢ n = 5

-- 5ª versión
-- ==========

meta def test_and_exact_def (hyp tgt : expr) : tactic unit :=
do hyp_tp ← infer_type hyp,
   is_def_eq hyp_tp tgt,
   exact hyp

meta def assump5 : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   ctx.mfirst (λ e, test_and_exact_def e tgt)

example (n : ℕ) (hx : n + 0 = 5) : n = 5 :=
by assump5

-- Comentario: Al colocar el cursor sobre assump se obtiene éxito

-- 6ª versión
-- ==========

meta def assump6 : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   ctx.mfirst (λ e, exact e)

example (n : ℕ) (hx : n + 0 = 6) : n = 6 :=
by assump6

-- Comentario: Al colocar el cursor sobre assump se obtiene éxito

-- 7ª versión
-- ==========

meta def assump7 : tactic unit :=
local_context >>= list.mfirst exact

example (n : ℕ) (hx : n + 0 = 7) : n = 7 :=
by assump7

-- Comentario: Al colocar el cursor sobre assump se obtiene éxito

----------------------------------------------------------------------
-- §§ Definición de la táctica add_refl                             --
----------------------------------------------------------------------

-- 1ª versión
-- ==========

meta def add_single_refl (e : expr) : tactic unit :=
do tp ← infer_type e,
   guard (tp = `(ℕ)),
   pf ← mk_app `eq.refl [e],
   nm ← get_unused_name,
   note nm none pf,
   skip

meta def add_refl : tactic unit :=
do ctx ← local_context,
   ctx.mmap' (λ e, add_single_refl e)

example (a b c : ℕ) (ha : a = b) : true :=
by do add_refl

-- Comentario: Al colocar el cursor sobre do se obtiene
--    failed
--    state:
--    a b c : ℕ,
--    ha : a = b,
--    _x : a = a,
--    _x_1 : b = b,
--    _x_2 : c = c
--    ⊢ true

-- 2ª versión
-- ==========

meta def add_refl2 : tactic unit :=
do ctx ← local_context,
   ctx.mmap' (λ e, try (add_single_refl e))

example (a b c : ℕ) (ha : a = b) : true :=
by do add_refl2

-- Comentario: Al colocar el cursor sobre do se obtiene
--    tactic failed, there are unsolved goals
--    state:
--    a b c : ℕ,
--    ha : a = b,
--    _x : a = a,
--    _x_1 : b = b,
--    _x_2 : c = c
--    ⊢ true

-- 3ª versión
-- ==========

meta def add_single_refl3 (e : expr) : tactic unit :=
do tp ← infer_type e,
   guard (tp = `(ℕ)),
   pf ← mk_app `eq.refl [e],
   nm ← get_unused_name e.local_pp_name,
   note nm none pf,
   skip

meta def add_refl3 : tactic unit :=
do ctx ← local_context,
   ctx.mmap' (λ e, try (add_single_refl3 e))

example (a b c : ℕ) (ha : a = b) : true :=
by do add_refl3

-- Comentario: Al colocar el cursor sobre do se obtiene
--    tactic failed, there are unsolved goals
--    state:
--    a b c : ℕ,
--    ha : a = b,
--    a_1 : a = a,
--    b_1 : b = b,
--    c_1 : c = c
--    ⊢ true

-- 4ª versión
-- ==========

meta def add_single_refl4 (e : expr) : tactic unit :=
do tp ← infer_type e,
   guard (tp = `(ℕ)),
   pf ← to_expr ``(not_lt_of_ge (nat.zero_le %%e)),
   nm ← get_unused_name e.local_pp_name,
   note nm none pf,
   skip

meta def add_refl4 : tactic unit :=
do ctx ← local_context,
   ctx.mmap' (λ e, try (add_single_refl4 e))

example (a b c : ℕ) (ha : a = b) : true :=
by do add_refl4

-- Comentario: Al colocar el cursor sobre do se obtiene
--    tactic failed, there are unsolved goals
--    state:
--    a b c : ℕ,
--    ha : a = b,
--    a_1 : ¬a < 0,
--    b_1 : ¬b < 0,
--    c_1 : ¬c < 0
--    ⊢ true

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Metaprogramming in Lean tutorial: video 5" de Rob
-- Lewis que se encuentra en https://youtu.be/-RQQxFVZnn4
