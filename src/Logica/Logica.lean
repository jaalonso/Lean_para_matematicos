import data.real.basic

------------------------------------------------------------------------
-- § Introducción                                                     --
------------------------------------------------------------------------

-- Nota. Los *símbolos lógicos* en Lean son
/-
|---------+---------------+-----------------+---------------------------|
| Símbolo | Lean          | Lectura         | Nombre                    |
|---------+---------------+-----------------+---------------------------|
| →       | \to, \r       | si ... entonces | implicación               |
| ∀       | \all          | para todo       | cuantificador universal   |
| ∃       | \ex           | existe          | cuantificador existencial |
| ¬       | \not, \n      | no              | negación                  |
| ∧       | \and          | y               | conjunción                |
| ↔       | \iff, \lr     | si y solo si    | bicondicional             |
| ∨       | \or           | o               | disyunción                |
| false   | contradicción | falso           |                           |
| true    | trivial       | verdadero       |                           |
|---------+---------------+-----------------+---------------------------|
-/

-- Notas.
-- 1. Los *objetivos* en Lean son de la forma
--       1 goal
--       x y : ℕ,
--       h₁ : prime x,
--       h₂ : ¬even x,
--       h₃ : y > x
--       ⊢ y ≥ 4
-- 2. La parte antes de ⊢ se llama el *contexto* o el *contexto local*.
-- 3. Cada elemento del contexto se llama *hipótesis* o *hipótesis local*.
-- 4. La parte después de ⊢ se llama la *conclusión del objetivo* o el
--    *objetivo*.

-- Nota. Las *tácticas* de introducción o eliminación de conectivas son
/-
|---------+-----------------+-------------------+-----------------------------|
| Símbolo | Nombre          | Introducción      | Eliminación                 |
|---------+-----------------+-------------------+-----------------------------|
| →       | si ... entonces | `intro`, `intros` | `apply`, `have h₃ := h₁ h₂` |
| ∀       | para todo       | `intro`, `intros` | `apply`, `specialize`,      |
|         |                 |                   | `have h₂ := h₁ t`           |
| ∃       | existe          | `use`             | `cases`                     |
| ¬       | no              | `intro`, `intros` | `apply`, `contradiction`    |
| ∧       | y               | `split`           | `cases`, `h.1` / `h.2`,     |
|         |                 |                   | `h.left` / `h.right`        |
| ↔       | si y solo si    | `split`           | `cases`, `h.1` / `h.2`,     |
|         |                 |                   | `h.mp` / `h.mpr`, `rw`      |
| ∨       | o               | `left` / `right`  | `cases`                     |
| false   | contradicción   |                   | `contradiction`, `ex_falso` |
| true    | trivial         | `trivial`         |                             |
|---------+-----------------+-------------------+-----------------------------|
-/

-- Nota: En la demostraciones por contradicción,
-- + hay que usar `open_locale classical`
-- + se usa la táctica `by_contradiction`.

-- Nota: La estructura lógica puede estar oculta en las
-- definiciones. Por ejemplo,
-- + `x ∣ y` es existencial
-- + `s ⊆ t` es universal

------------------------------------------------------------------------
-- § Implicación y cuantificador universal                            --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Crear la sección primera
-- ----------------------------------------------------------------------

section primera

-- ---------------------------------------------------------------------
-- Ejercicio. Definir las siguientes variables:
-- + a, b, c y d como números reales.
-- + h₁ como a ≤ b
-- + h₂ como c ≤ d
-- ----------------------------------------------------------------------


variables a b c d : ℝ
variable  h₁ : a ≤ b
variables h₂ : c ≤ d

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de los siguientes términos
--    @add_le_add
--    @add_le_add _ _ a b
--    @add_le_add _ _ a b c d h₁
--    add_le_add h₁
-- ----------------------------------------------------------------------

-- Se calcula quitando el comentario y colocando el cursor sobre check
--    #check @add_le_add
--    #check @add_le_add _ _ a b
--    #check @add_le_add _ _ a b c d h₁
--    #check add_le_add h₁

-- Comentario: Al colocar el cursor sobre check se obtiene
-- + add_le_add : ∀ {α : Type u_1} [_inst_1 : ordered_add_comm_monoid α]
--                {a b c d : α}, a ≤ b → c ≤ d → a + c ≤ b + d
-- + add_le_add : ∀ {c d : ℝ}, a ≤ b → c ≤ d → a + c ≤ b + d
-- + add_le_add h₁ : c ≤ d → a + c ≤ b + d
-- + add_le_add h₁ : ?M_1 ≤ ?M_2 → a + ?M_1 ≤ b + ?M_2

-- ---------------------------------------------------------------------
-- Ejercicio. Incluir las hipótesis h₁ y h₂ hasta el final de la
-- sección.
-- ----------------------------------------------------------------------

include h₁ h₂

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de h₁
-- ----------------------------------------------------------------------

#check h₁

-- Comentario: Al colocar el cursor sobre chck se obtiene
--    h₁ : a ≤ b

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a + c ≤ b + d
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : a + c ≤ b + d :=
begin
  apply add_le_add,
  apply h₁,
  apply h₂,
end

-- Prueba
-- ======

/-
a b c d : ℝ,
h₁ : a ≤ b,
h₂ : c ≤ d
⊢ a + c ≤ b + d
  >> apply add_le_add,
| ⊢ a ≤ b
|   >> apply h₁,
⊢ c ≤ d
  >> apply h₂,
no goals
-/

-- Comentario. La táctica (apply h) equipara la conclusión de h con el
-- objetivo y sustituye el objetivo por hipótesis de h. Por ejemplo, si
-- h es (P → Q → R), el objetivo es S y existe una f tal que f(R) = S en
-- entonces los nuevos objetivos son f(P) y f(Q).

-- 2ª demostración
-- ===============

example : a + c ≤ b + d :=
begin
  apply add_le_add h₁,
  apply h₂,
end

-- Prueba
-- ======

/-
a b c d : ℝ,
h₁ : a ≤ b,
h₂ : c ≤ d
⊢ a + c ≤ b + d
  >> apply add_le_add h₁,
⊢ c ≤ d
  >> apply h₂,
no goals
-/


-- 3ª demostración
-- ===============

example : a + c ≤ b + d :=
begin
  have h₃ := add_le_add h₁,
  apply h₃,
  apply h₂,
end

-- Comentario. La táctica (have h := h2) añade la hipótesis h al contexto.

-- Prueba
-- ======

/-
a b c d : ℝ,
h₁ : a ≤ b,
h₂ : c ≤ d
⊢ a + c ≤ b + d
  >> have h₃ := add_le_add h₁,
h₃ : ?m_1 ≤ ?m_2 → a + ?m_1 ≤ b + ?m_2
⊢ a + c ≤ b + d
  >> apply h₃,
⊢ c ≤ d
  >> apply h₂,
no goals
-/

-- 3ª demostración
-- ===============

example : a + c ≤ b + d :=
begin
  have h₃ := add_le_add h₁ h₂,
  assumption,
end

-- Comentario: La táctica assumption unifica el obketivo con una de las
-- hipótesis.

-- Prueba
-- ======

/-
a b c d : ℝ,
h₁ : a ≤ b,
h₂ : c ≤ d
⊢ a + c ≤ b + d
  >> have h₃ := add_le_add h₁ h₂,
h₃ : a + c ≤ b + d
⊢ a + c ≤ b + d
  >> assumption,
no goals
-/

-- 5ª demostración
-- ===============

example : a + c ≤ b + d :=
begin
  apply add_le_add h₁ h₂,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar la sección primera
-- ----------------------------------------------------------------------

end primera

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de h₁
-- ----------------------------------------------------------------------

#check h₁

-- Comentario: Al colocar el cursor sobre check no se obtiene nada

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la sección segunda.
-- ----------------------------------------------------------------------

section segunda

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--     fn_ub (ℝ → ℝ) → ℝ → Prop
-- tal que (fn_ub f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop :=
∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que
-- + f y g son variables implícitas de funciones de ℝ en ℝ.
-- + a y b son variables implícitas de números reales.
-- ----------------------------------------------------------------------

variables {f g : ℝ → ℝ} {a b : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a es una cota superior de f y b es una
-- cota superior de g, entonces a + b es una cota superior de f + g.
-- ----------------------------------------------------------------------

theorem fn_ub_add
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  apply add_le_add,
  { specialize hfa x,
    assumption },
  { have h := hgb x,
    assumption },
end

-- Prueba
-- ======

/-
f g : ℝ → ℝ,
a b : ℝ,
hfa : fn_ub f a,
hgb : fn_ub g b
⊢ fn_ub (λ (x : ℝ), f x + g x) (a + b)
  >> intro x,
x : ℝ
⊢ (λ (x : ℝ), f x + g x) x ≤ a + b
  >> dsimp,
⊢ f x + g x ≤ a + b
  >> apply add_le_add,
| ⊢ f x ≤ a
|   >> { specialize hfa x,
| hfa : f x ≤ a
| ⊢ f x ≤ a
|   >>   assumption },
⊢ g x ≤ b
  >> { have h := hgb x,
h : g x ≤ b
⊢ g x ≤ b
  >>   assumption },
no goals
-/

-- Comentarios:
-- 1. La táctica (intro x) cuando el objetivo es universal aplica la
--    regla de introducción del cuantificador universal; es decir, si el
--    objetivo es (∀ y : α, P y) entonces añade la hipótesis (x : α) y
--    cambia el objetivo a (P x).
-- 2. Por la definición de fn_ub, el primer objetivo es universal.
-- 3. La táctica dsimp simplifica el objetivo usando definiciones.
-- 4. La táctica (specialize h x) cuando h es universal aplica la regla
--    de eliminación del cuantificador existencial; es decir si h es
--    (∀ y, P y) la sustituye por (P x).
-- 5. En lugar de (specialize h1 x) se puede usar (have h2 := h1 x).

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar la sección segunda.
-- ----------------------------------------------------------------------

end segunda

------------------------------------------------------------------------
-- § El cuantificador existencial                                     --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que existe un número real entre 2 y 3.
-- ----------------------------------------------------------------------

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num,
end

-- Prueba
-- ======

/-
⊢ ∃ (x : ℝ), 2 < x ∧ x < 3
  >> use 5 / 2,
⊢ 2 < 5 / 2 ∧ 5 / 2 < 3
  >> norm_num,
no goals
-/

-- Comentarios:
-- 1. La táctica (use e) cuando el objetivo es existencial aplica la
--    regla de introducción del cuantificador existencial; es decir, si
--    el objetivo es (∃ x, P x) lo sustituye por (P e).
-- 2. La tática norm_num aplica normalización numérica.

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la sección tercera.
-- ----------------------------------------------------------------------

section tercera

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    fn_has_ub (ℝ → ℝ) → Pro
-- tal que (fn_has_ub f) afirma que f tiene cota superior.
-- ----------------------------------------------------------------------

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que f y g son variables implícitas de funciones
-- de ℝ en ℝ.
-- ----------------------------------------------------------------------

variables {f g : ℝ → ℝ}

example
  (ubf : fn_has_ub f)
  (ubg : fn_has_ub g)
  : fn_has_ub (λ x, f x + g x) :=
begin
  cases ubf with a ha,
  cases ubg with b hb,
  use a + b,
  apply fn_ub_add ha hb,
end

-- Prueba
-- ======

/-
f g : ℝ → ℝ,
ubf : fn_has_ub f,
ubg : fn_has_ub g
⊢ fn_has_ub (λ (x : ℝ), f x + g x)
  >> cases ubf with a ha,
a : ℝ,
ha : fn_ub f a
⊢ fn_has_ub (λ (x : ℝ), f x + g x)
  >> cases ubg with b hb,
b : ℝ,
hb : fn_ub g b
⊢ fn_has_ub (λ (x : ℝ), f x + g x)
  >> use a + b,
⊢ fn_ub (λ (x : ℝ), f x + g x) (a + b)
  >> apply fn_ub_add ha hb,
no goals
-/

-- Comentario: La táctica (cases h with a ha) cuando h es existencial
-- aplica la regla de eliminación del cuantificador existencial; es
-- decir, si h es (∃ x : α, P x) añade las hipótesis (a : α) y (ha : P a).

end tercera

------------------------------------------------------------------------
-- § Negación                                                         --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la sección cuarta.
-- ----------------------------------------------------------------------

section cuarta

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que f es una variable implícita de funciones de ℝ
-- en ℝ.
-- ----------------------------------------------------------------------

variable {f : ℝ → ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--     ∀ a, ∃ x, f x > a
-- entonces f no tiene cota superior.
-- ----------------------------------------------------------------------

example
  (h : ∀ a, ∃ x, f x > a)
  : ¬ fn_has_ub f :=
begin
  intro ubf,
  cases ubf with b hb,
  specialize h b,
  cases h with y hy,
  specialize hb y,
  linarith,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ,
h : ∀ (a : ℝ), ∃ (x : ℝ), f x > a
⊢ ¬fn_has_ub f
  >> intro ubf,
ubf : fn_has_ub f
⊢ false
  >> cases ubf with b hb,
b : ℝ,
hb : fn_ub f b
⊢ false
  >> specialize h b,
h : ∃ (x : ℝ), f x > b
⊢ false
  >> cases h with y hy,
y : ℝ,
hy : f y > b
⊢ false
  >> specialize hb y,
hb : f y ≤ b
⊢ false
  >> linarith,
no goals
-/

-- Comentarios:
-- 1. La táctica (intro h) cuando el obketivo es una negación aplica la
--    regla de introducción de la negación; es decir, si el objetivo es ¬P
--    entonces añade la hipótesis (h : P) y cambia el objetivo a false.
-- 2. la táctica lnarith aplica simplificación con la aritmética lineal.

end cuarta

------------------------------------------------------------------------
-- § Conjunción                                                       --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la sección quinta
-- ----------------------------------------------------------------------

section quinta

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que x e y son variables implícitas de números
-- reales.
-- ----------------------------------------------------------------------

variables {x y : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--     x ≤ y
--     ¬ y ≤ x
-- entonces
--    x ≤ y ∧ x ≠ y
-- ----------------------------------------------------------------------

example
  (h₀ : x ≤ y)
  (h₁ : ¬ y ≤ x)
  : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  { intro h₂,
    apply h₁,
    rw h₂ },
end

-- Prueba
-- ======

/-
x y : ℝ,
h₀ : x ≤ y,
h₁ : ¬y ≤ x
⊢ x ≤ y ∧ x ≠ y
  >> split,
| ⊢ x ≤ y
|   >> { assumption },
⊢ x ≠ y
  >> { intro h₂,
h₂ : x = y
⊢ false
  >>   apply h₁,
h₂ : x = y
⊢ false
  >>   rw h₂ },
no goals
-/

-- Comentario. La táctica split si la conclusión es una conjunción
-- aplica la regla de introducción de la conjunción; es decir, si es
-- (P ∧ Q) diferencia dos casos en el que la conclusión del primero es P
-- y la del segundo es Q.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    x ≤ y ∧ x ≠ y
-- entonces
--    ¬ y ≤ x
-- ----------------------------------------------------------------------

example
  (h : x ≤ y ∧ x ≠ y)
  : ¬ y ≤ x :=
begin
  intro h1,
  apply h.2,
  apply le_antisymm h.1 h1,
end

-- Comentarios:
-- 1. Si h es una conjunción, entonces h.1 es su primera parte y h.2 la
--    segunda. Por ejemplo, si h es P ∧ Q, entonces h.1 es P y h.2 es Q.
-- 2. Se ha usado el lema
--    + le_antisymm : x ≤ y → y ≤ x → x = y

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar la sección quinta.
-- ----------------------------------------------------------------------

end quinta

------------------------------------------------------------------------
-- § Disyunción                                                       --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la sección sexta
-- ----------------------------------------------------------------------

section sexta

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que x e y son variables de números reales.
-- ----------------------------------------------------------------------

variables x y : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de los siguientes términos
--    le_or_gt 0 y
--    @abs_of_nonneg
--    @abs_of_neg
-- ----------------------------------------------------------------------

#check le_or_gt 0 y
#check @abs_of_nonneg
#check @abs_of_neg

-- Comentario: Al colocar el cursor sobre check se obtiene
-- + le_or_gt 0 y : 0 ≤ y ∨ 0 > y
-- + abs_of_nonneg :
--     ∀ {α : Type u_1} [_inst_1 : decidable_linear_ordered_add_comm_group α]
--       {a : α}, 0 ≤ a → abs a = a
-- + abs_of_neg :
--     ∀ {α : Type u_1} [_inst_1 : decidable_linear_ordered_add_comm_group α]
--       {a : α}, a < 0 → abs a = -a [3 times]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    x < abs y → x < y ∨ x < -y
-- ----------------------------------------------------------------------

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with ynonneg yneg,
  { rw abs_of_nonneg ynonneg,
    intro h1,
    left,
    apply h1 },
  { rw abs_of_neg yneg,
    intro h2,
    right,
    apply h2 },
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ x < abs y → x < y ∨ x < -y
  >> cases le_or_gt 0 y with ynonneg yneg,
| ynonneg : 0 ≤ y
| ⊢ x < abs y → x < y ∨ x < -y
|   >> { rw abs_of_nonneg ynonneg,
| ⊢ x < y → x < y ∨ x < -y
|   >>   intro h1,
| h1 : x < y
| ⊢ x < y ∨ x < -y
|   >>   left,
| ⊢ x < y
|   >>   apply h1 },
yneg : 0 > y
⊢ x < abs y → x < y ∨ x < -y
  >> { rw abs_of_neg yneg,
⊢ x < -y → x < y ∨ x < -y
  >>   intro h2,
h2 : x < -y
⊢ x < y ∨ x < -y
  >>   right,
⊢ x < -y
  >>   apply h2 },
no goals
-/

-- Comentarios
-- 1. La táctica (cases h with h1 h2) xuando h es una disyunción aplica
--    la regla de eliminación de la disyunción; es decir, si (h : P ∨ Q)
--    cambia el objetrivo por dos; en el primero le añade la hipótesis
--    (h1 : P) y en el segundo (h2 : Q).
-- 2. La táctica (rw h) reescribe el objetivo con el lema h.
-- 3. La táctica left cuando la conclusión es una disyunción aplica la
--    primera regla de introducción de la disyunción; es decir, si la
--    conclusión es (P ∨ Q) la cambia por P.
-- 4. La táctica right cuando la conclusión es una disyunción aplica la
--    segunda regla de introducción de la disyunción; es decir, si la
--    conclusión es (P ∨ Q) la cambia por Q.

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar la sección sexta.
-- ----------------------------------------------------------------------

end sexta

------------------------------------------------------------------------
-- § Otras conectivas y demostraciones                                --
------------------------------------------------------------------------

-- Comentarios:
-- 1. No se han vistos las reglas del bicondicional, de true y de false.
-- 2. Tampoco se ha visto las demostraciones con by_contradiction

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en la teoría logic.lean de Jeremy Avigad que se
-- encuentra en https://bit.ly/39c7pFO y se comenta en el vídeo
-- "Logic in Lean" que se encuentra en https://youtu.be/WGwKefZ8KFo
--
-- Sus referencias son
-- + "Mathematics in Lean" https://bit.ly/2OzX8ty
-- + "Theorem proving in Lean" http://bit.ly/37XcbVn
-- + "Lean Cheatsheet" https://bit.ly/3eGhBay
