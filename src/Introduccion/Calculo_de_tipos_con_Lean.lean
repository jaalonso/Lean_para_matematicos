import analysis.calculus.specific_functions

-- ---------------------------------------------------------------------
-- Ejercicio 1. Calcular el tipo de las siguientes expresiones 
--    ℕ
--    real.exp
--    λ x, x*real.exp x
--    2 ∈ 3
--    2 ∩ 3
-- ----------------------------------------------------------------------

-- Nota: El resultado obtenido al colocar el cursor sobre check se
-- indica debajo de cada término.

#check ℕ
-- | ℕ : Type

#check real.exp
-- | real.exp : ℝ → ℝ

#check λ x, x*real.exp x
-- | λ (x : ℝ), x * real.exp x : ℝ → ℝ

#check 2 ∈ 3
-- | failed to synthesize type class instance for
-- | ⊢ has_mem ℕ ℕ

#check 2 ∩ 3
-- | failed to synthesize type class instance for
-- | ⊢ has_inter ℕ

-- ---------------------------------------------------------------------
-- Ejercicio 2. Comprobar el cálculo del tipo de  
--    ∀ N, ∃ p ≥ N, nat.prime p
-- ----------------------------------------------------------------------

#check ∀ N, ∃ p ≥ N, nat.prime p
-- | ∀ (N : ℕ), ∃ (p : ℕ) (H : p ≥ N), nat.prime p : Prop

set_option trace.elaborator_detail true
set_option trace.type_context.is_def_eq true
set_option trace.type_context.is_def_eq_detail true

#check ∀ N, ∃ p ≥ N, nat.prime p
/-
∀ (N : ℕ), ∃ (p : ℕ) (H : p ≥ N), ⁇

[elaborator_detail] [1] visiting
Π (N : _), Exists (λ (p : _), Exists (λ (H : ge p N), nat.prime p))
[elaborator_detail] [2] visiting
_
[type_context.is_def_eq_detail] process_assignment ?m_1 := Sort ?
[type_context.is_def_eq_detail] assign: ?m_1 := Sort ?
[type_context.is_def_eq] ?m_1 =?= Sort ? ... success  (approximate mode)
[elaborator_detail] [2] visiting
Exists (λ (p : _), Exists (λ (H : ge p N), nat.prime p))
[elaborator_detail] [3] visiting
λ (p : _), Exists (λ (H : ge p N), nat.prime p)
expected type:
?m_1 → Prop
[elaborator_detail] [4] visiting
_
[type_context.is_def_eq_detail] process_assignment ?m_1 := ?m_2
[type_context.is_def_eq_detail] process_assignment ?m_1 := Sort ?
[type_context.is_def_eq_detail] assign: ?m_1 := Sort ?
[type_context.is_def_eq_detail] assign: ?m_1 := ?m_2
[type_context.is_def_eq] ?m_1 =?= ?m_2 ... success  (approximate mode)
[elaborator_detail] [4] visiting
Exists (λ (H : ge p N), nat.prime p)
expected type:
Prop
[type_context.is_def_eq] Prop =?= Prop ... success  (approximate mode)
[elaborator_detail] [5] visiting
λ (H : ge p N), nat.prime p
expected type:
?m_1 → Prop
[elaborator_detail] [6] visiting
ge p N
[elaborator_detail] [7] visiting
p
expected type:
?m_1
[type_context.is_def_eq_detail] process_assignment ?m_1 := ?m_2
[type_context.is_def_eq_detail] assign: ?m_1 := ?m_2
[type_context.is_def_eq] ?m_1 =?= ?m_2 ... success  (approximate mode)
[type_context.is_def_eq] ?m_1 =?= ?m_2 ... success  (approximate mode)
[elaborator_detail] [7] visiting
N
expected type:
?m_1
[type_context.is_def_eq_detail] process_assignment ?m_1 := ?m_2
[type_context.is_def_eq_detail] assign: ?m_1 := ?m_2
[type_context.is_def_eq] ?m_1 =?= ?m_2 ... success  (approximate mode)
[type_context.is_def_eq] ?m_1 =?= ?m_2 ... success  (approximate mode)
[type_context.is_def_eq_detail] process_assignment ?m_1 := p ≥ N
[type_context.is_def_eq_detail] assign: ?m_1 := p ≥ N
[type_context.is_def_eq] p ≥ N =?= ?m_3 ... success  (approximate mode)
[elaborator_detail] [6] visiting
nat.prime p
expected type:
Prop
[type_context.is_def_eq] Prop =?= Prop ... success  (approximate mode)
[elaborator_detail] [7] visiting
p
expected type:
ℕ
[type_context.is_def_eq_detail] process_assignment ?m_1 := ℕ
[type_context.is_def_eq_detail] assign: ?m_1 := ℕ
[type_context.is_def_eq] ?m_1 =?= ℕ ... success  (approximate mode)
[type_context.is_def_eq] ?m_1 =?= ℕ ... success  (approximate mode)
[type_context.is_def_eq_detail] process_assignment ?m_1 := p
[type_context.is_def_eq_detail] assign: ?m_1 := p
[type_context.is_def_eq] ?m_1 =?= p ... success  (approximate mode)
[type_context.is_def_eq_detail] process_assignment ?m_1 := nat.has_le
[type_context.is_def_eq_detail] [1]: has_le ?m_1 =?= has_le ℕ
[type_context.is_def_eq_detail] [2]: has_le =?= has_le
[type_context.is_def_eq_detail] assign: ?m_1 := nat.has_le
[type_context.is_def_eq] ?m_1 =?= nat.has_le ... success  (approximate mode)
[type_context.is_def_eq] p ≥ N → Prop =?= ?m_1 → Prop ... success  (approximate mode)
[type_context.is_def_eq_detail] process_assignment ?m_1 := λ (H : p ≥ N), nat.prime p
[type_context.is_def_eq_detail] assign: ?m_1 := λ (H : p ≥ N), nat.prime p
[type_context.is_def_eq] ?m_1 =?= λ (H : p ≥ N), nat.prime p ... success  (approximate mode)
[type_context.is_def_eq] ℕ → Prop =?= ?m_1 → Prop ... success  (approximate mode)
[elaborator_detail] result before final checkpoint
∀ (N : ℕ), ∃ (p : ℕ) (H : p ≥ N), nat.prime p


∀ (N : ℕ), ∃ (p : ℕ) (H : p ≥ N), nat.prime p : Prop
-/

set_option trace.elaborator_detail false
set_option trace.type_context.is_def_eq false
set_option trace.type_context.is_def_eq_detail false

-- ---------------------------------------------------------------------
-- Ejercicio 3. Calcular el tipo de
--    ∀ x : ℝ, ∀ ε > 0, ∃ n : ℕ, x ≤ n * ε
-- ----------------------------------------------------------------------

example : ∀ x : ℝ, ∀ ε > 0, ∃ n : ℕ, x ≤ n * ε :=
sorry

-- El tipo es
--    ⊢ ∀ (x ε : ℝ), ε > 0 → (∃ (n : ℕ), x ≤ ↑n * ε)
-- Se observa cómo n se eleva del tipo ℕ a ℝ.

-- ---------------------------------------------------------------------
-- Ejercicio 4. Realizar las siguientes acciones:
-- 1. Declarar n y m como variables sobre los naturales.
-- 2. Calcular el tipo de (1 /(n + 1 : ℝ)). 
-- 2. Calcular el tipo de (1 /(n + m : ℝ)). 
-- ----------------------------------------------------------------------

variables (m n : ℕ)

#check 1 /(n + 1 : ℝ) 
-- | 1 / (↑n + 1) : ℝ

#check 1 /(n + m : ℝ) 
-- | 1 / (↑n + ↑m) : ℝ 


------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Mathematics in Lean introduction" de Patrick
-- Massot que se encuentra en https://youtu.be/lw8EfTmWzRU 

