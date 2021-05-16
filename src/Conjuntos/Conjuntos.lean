import data.set.basic
import data.set.lattice
import data.nat.parity
import tactic.linarith

-- ---------------------------------------------------------------------
-- Ejercicio 1. Habilitar las teorías set, nat y function.
-- ----------------------------------------------------------------------

open set nat function

-- ---------------------------------------------------------------------
-- Ejercicio 2. Activar la lógica clásica.
-- ----------------------------------------------------------------------

open_locale classical

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar los tipos α, β, γ e I.
-- ----------------------------------------------------------------------

variables {α : Type*} {β : Type*} {γ : Type*} {I : Type*}

-- ---------------------------------------------------------------------
-- Ejercicio 4. Empezar la sección set_variables.
-- ----------------------------------------------------------------------


section set_variables

-- ---------------------------------------------------------------------
-- Ejercicio 5. Declarar
-- 1. x como una variable sobre objetos de tipo α
-- 2. s, t y u como variables sobre conjuntos de elementos de tipo α.
-- ----------------------------------------------------------------------

variable  x : α
variables s t u : set α

-- ---------------------------------------------------------------------
-- Ejercicio 6. Calcular el tipo de las siguientes expresiones (el
-- símbolo se puede escribir como se indica a su lado).
--    s ⊆ t           -- \sub
--    x ∈ s           -- \in o \mem
--    x ∉ s           -- \notin
--    s ∩ t           -- \i o \cap
--    s ∪ t           -- \un o \cup
--    (∅ : set α)     -- \empty
--    (univ: set α)
-- ----------------------------------------------------------------------

#check s ⊆ t
#check x ∈ s
#check x ∉ s
#check s ∩ t
#check s ∪ t
#check (∅ : set α)
#check (univ: set α)

-- Comentario; Al colocar el cursor sobre check se obtiene
-- + s ⊆ t : Prop
-- + x ∈ s : Prop
-- + x ∉ s : Prop
-- + s ∩ t : set α
-- + s ∪ t : set α
-- + ∅ : set α
-- univ : set α

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que si
--    s ⊆ t
-- entonces
--    s ∩ u ⊆ t ∩ u :=
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw subset_def,
  rw inter_def,
  rw inter_def,
  dsimp,
  intros x h,
  cases h with xs xu,
  split,
  { rw subset_def at h,
    apply h,
    assumption },
  { assumption },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> rw subset_def,
⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  >> rw inter_def,
⊢ ∀ (x : α), x ∈ {a : α | a ∈ s ∧ a ∈ u} → x ∈ t ∩ u
  >> rw inter_def,
⊢ ∀ (x : α), x ∈ {a : α | a ∈ s ∧ a ∈ u} → x ∈ {a : α | a ∈ t ∧ a ∈ u}
  >> dsimp,
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> intros x h,
x : α,
h : x ∈ s ∧ x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> cases hx with xs xu,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> split,
| 2 goals
| α : Type u_1,
| s t u : set α,
| h : s ⊆ t,
| x : α,
| xs : x ∈ s,
| xu : x ∈ u
| ⊢ x ∈ t
|   >>  { rw subset_def at h,
| h : ∀ (x : α), x ∈ s → x ∈ t
| ⊢ x ∈ t
|   >>    apply h,
| ⊢ x ∈ s
|   >>    assumption },
α : Type u_1,
s t u : set α,
h : s ⊆ t,
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ u
  >>  { assumption },
no goals
-/

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  dsimp,
  rintros x ⟨xs, xu⟩,
  rw subset_def at h,
  exact ⟨h _ xs, xu⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> rw [subset_def, inter_def, inter_def],
⊢ ∀ (x : α), x ∈ {a : α | a ∈ s ∧ a ∈ u} → x ∈ {a : α | a ∈ t ∧ a ∈ u}
  >> dsimp,
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rintros x ⟨xs, xu⟩,
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> rw subset_def at h,
h : ∀ (x : α), x ∈ s → x ∈ t
⊢ x ∈ t ∧ x ∈ u
  >> exact ⟨h _ xs, xu⟩,
no goals
-/

-- Comentarios:
-- 1. La táctica (rintros x ⟨h1, h2⟩) cuando la conclusión es
--    de la forma (∀ x : α, P ∧ Q → S) añade las hipótesis (x : α),
--    (h1 : P), (h2 : Q) y cambia la conclusión a S.
-- 2. La táctica (exact ⟨h1, h2⟩) si la conclusión es de la
--    forma (P ∧ Q), h1 es una prueba de P y h2 es una prueba de, entonces
--    es una prueba de la conclusión.

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> simp only [subset_def, mem_inter_eq] at *,
h : ∀ (x : α), x ∈ s → x ∈ t
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rintros x ⟨xs, xu⟩,
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> exact ⟨h _ xs, xu⟩,
no goals
-/

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> intros x xsu,
x : α,
xsu : x ∈ s ∩ u
⊢ x ∈ t ∩ u
  >> exact ⟨h xsu.1, xsu.2⟩,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio 8. Demostrar que
--    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  clear hx,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  { right,
    show x ∈ s ∩ u,
    exact ⟨xs, xu⟩ },
end

-- 2ª demostración
-- ===============

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left,
    exact ⟨xs, xt⟩ },
  { right,
    exact ⟨xs, xu⟩ },
end

-- ---------------------------------------------------------------------
-- Ejercicio 9. Demostrar que
--    (s \ t) \ u ⊆ s \ (t ∪ u)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs },
  { dsimp,
    intro xtu,
    cases xtu with xt xu,
    { show false, from xnt xt },
    { show false, from xnu xu }},
end

-- 2ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

-- 3ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  simp at *,
  finish,
end

-- 4ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  finish,
end

-- ---------------------------------------------------------------------
-- Ejercicio 10. Demostrar que
--    (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u
-- ----------------------------------------------------------------------

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  { use xs,
    left,
    exact xt },
  { use xs,
    right,
    exact xu },
end

-- ---------------------------------------------------------------------
-- Ejercicio 11. Demostrar que
--    s \ (t ∪ u) ⊆ (s \ t) \ u
-- ----------------------------------------------------------------------

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { intro xt,
    exact xntu (or.inl xt) },
  { intro xu,
    exact xntu (or.inr xu) },
end

-- ---------------------------------------------------------------------
-- Ejercicio 12. Demostrar que
--    s ∩ t = t ∩ s
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩,
    exact ⟨xt, xs⟩ },
  { rintros ⟨xt, xs⟩,
    exact ⟨xs, xt⟩ },
end

-- Comentarios:
-- 1. La táctica ext si la conclusión es un igualdad de conjunto (A = B)
--    la sustituye por (x ∈ A ↔ x ∈ B).
-- 2. Se ha usado el lema
--    + mem_inter_eq x s t : x ∈ s ∩ t = (x ∈ s ∧ x ∈ t)

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

-- Comentario: Se ha usado el lema
-- + and.comm : a ∧ b ↔ b ∧ a

-- ---------------------------------------------------------------------
-- Ejercicio 13. Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { rintros ⟨xs, _⟩,
    exact xs },
  { intro xs,
    use xs,
    left,
    exact xs },
end

-- ---------------------------------------------------------------------
-- Ejercicio 14. Demostrar que
--    s ∪ (s ∩ t) = s
-- ----------------------------------------------------------------------

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  { rintros (xs | ⟨xs, xt⟩);
    exact xs },
  { intro xs,
    left,
    exact xs },
end

-- ---------------------------------------------------------------------
-- Ejercicio 15. Demostrar que
--    (s \ t) ∪ t = s ∪ t
-- ----------------------------------------------------------------------

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  { rintros (⟨xs, nxt⟩ | xt),
    { left,
      exact xs},
    { right,
      exact xt }},
  { by_cases h : x ∈ t,
    { intro _,
      right,
      exact h },
    { rintros (xs | xt),
      { left,
        use [xs, h] },
      { right,
        use xt }}},
end

-- ---------------------------------------------------------------------
-- Ejercicio 16. Demostrar que
--    (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
-- ----------------------------------------------------------------------


example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { split,
      { left,
        exact xs },
      { rintros ⟨_, xt⟩,
        contradiction }},
    { split ,
      { right,
        exact xt },
      { rintros ⟨xs, _⟩,
        contradiction }}},
  { rintros ⟨xs | xt, nxst⟩,
    { left,
      use xs,
      intro xt,
      apply nxst,
      split; assumption },
    { right,
      use xt,
      intro xs,
      apply nxst,
      split; assumption }},
end

-- ---------------------------------------------------------------------
-- Ejercicio 17. Definir evens como el conjunto de los pares y odds el de
-- los impares.
-- ----------------------------------------------------------------------

def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

-- ---------------------------------------------------------------------
-- Ejercicio 18. Demostrar que la unión de pares e impares es el
-- universal; es decir,
--    evens ∪ odds = univ
-- ----------------------------------------------------------------------

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em,
end

-- ---------------------------------------------------------------------
-- Ejercicio 19. Demostrar que
-- + s ∩ t = {x | x ∈ s ∧ x ∈ t}
-- + s ∪ t = {x | x ∈ s ∨ x ∈ t}
-- + (∅ : set α) = {x | false}
-- + (univ : set α) = {x | true}
-- ----------------------------------------------------------------------

example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := rfl
example : (∅ : set α) = {x | false} := rfl
example : (univ : set α) = {x | true} := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 20. Demostrar que el vacío no tiene elementos.
-- ----------------------------------------------------------------------

example
  (x : ℕ)
  (h : x ∈ (∅ : set ℕ))
  : false :=
h

-- ---------------------------------------------------------------------
-- Ejercicio 21. Demostrar que todos los elementos pertenecen al
-- universal.
-- ----------------------------------------------------------------------

example
  (x : ℕ)
  : x ∈ (univ : set ℕ) :=
trivial

-- ---------------------------------------------------------------------
-- Ejercicio 22. Demostrar que
--    {n | prime n} ∩ {n | n > 2} ⊆ {n | ¬ even n}
-- ----------------------------------------------------------------------

example : {n | prime n} ∩ {n | n > 2} ⊆ { n | ¬ even n} :=
begin
  intro n,
  simp,
  intro nprime,
  cases prime.eq_two_or_odd nprime with h h,
  { rw h,
    intro,
    linarith },
  { rw [even_iff, h],
    norm_num },
end

-- Comentario: Se han usado los siguientes lemas
-- + prime.eq_two_or_odd : prime p → p = 2 ∨ p % 2 = 1
-- + even_iff : n.even ↔ n % 2 = 0

-- ---------------------------------------------------------------------
-- Ejercicio 23. Crear una sección.
-- ----------------------------------------------------------------------

section

-- ---------------------------------------------------------------------
-- Ejercicio 24. Declarar A y B como familias de conjuntos de elementos
-- de tipo α indexadas por ℕ.
-- ----------------------------------------------------------------------

variables A B : ℕ → set α

-- ---------------------------------------------------------------------
-- Ejercicio 25. Demostrar que
--    s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
-- ----------------------------------------------------------------------

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  { rintros ⟨i, xAi, xs⟩,
    exact ⟨xs, ⟨i, xAi⟩⟩ },
end

-- Comentario: Se han usado los lemas
-- + mem_inter_eq x s t : x ∈ s ∩ t = (x ∈ s ∧ x ∈ t)
-- + mem_Union : x ∈ Union A ↔ ∃ (i : ℕ), x ∈ A i

-- ---------------------------------------------------------------------
-- Ejercicio 26. Demostrar que
--    (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
-- ----------------------------------------------------------------------

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    { intro i,
      exact (h i).2 }},
  { rintros ⟨h1, h2⟩ i,
    split,
    { exact h1 i },
    { exact h2 i }},
end

-- ---------------------------------------------------------------------
-- Ejercicio 27. Cerrar la sección
-- ----------------------------------------------------------------------

end

-- ---------------------------------------------------------------------
-- Ejercicio 28. Abrir una sección
-- ----------------------------------------------------------------------

section

-- ---------------------------------------------------------------------
-- Ejercicio 29. Declarar A y B como familia de conjuntos de elementos de
-- tipo α indexadas por ℕ.
-- ----------------------------------------------------------------------

variables A B : ℕ → set α

-- ---------------------------------------------------------------------
-- Ejercicio 30. Demostrar que
--    s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)
-- ----------------------------------------------------------------------

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { rintros (xs | xI),
    { intro i,
      right,
      exact xs },
    { intro i,
      left,
      exact xI i }},
  { intro h,
    by_cases xs : x ∈ s,
    { left,
      exact xs },
    { right,
      intro i,
      cases h i,
      { assumption },
      { contradiction }}},
end

-- Comentario. Se han usado los lemas
-- + mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t
-- + mem_Inter : x ∈ Inter A ↔ ∀ (i : ℕ), x ∈ A i

-- ---------------------------------------------------------------------
-- Ejercicio 31. Cerrar la sección.
-- ----------------------------------------------------------------------

end

-- Comentario: Mathlib también tiene, como se explica en *Mathematics in
-- Lean*,
-- + uniones acotadas: ⋃ x ∈ s, f x
-- + intersecciones acotadas: ⋂ x ∈ s, f x
-- + uniones de conjuntos: ⋃₀ s
-- + intersecciones de conjuntos: ⋂₀ s

-- ---------------------------------------------------------------------
-- Ejercicio 32. Cerrar la sección set_variables.
-- ---------------------------------------------------------------------

end set_variables

-- ---------------------------------------------------------------------
-- Ejercicio 33. Iniciar la sección function_variables.
-- ----------------------------------------------------------------------

section function_variables

-- ---------------------------------------------------------------------
-- Ejercicio 34. Declarar las siguientes variables:
-- + f como variable de funciones de α en β
-- + s y t como variable sobre conjunto de elementos de tipo α.
-- + u y v como variable sobre conjunto de elementos de tipo β.
-- + A como variable de familas de conjunto de α con índice en I.
-- + B como variable de familas de conjunto de β con índice en I.
-- ----------------------------------------------------------------------

variable  f : α → β
variables s t : set α
variables u v : set β
variable  A : I → set α
variable  B : I → set β

-- ---------------------------------------------------------------------
-- Ejercicio 35. Calcular los tipos de
-- 1. La imagen de s por f.
-- 2. La imagen inversa de u por f,
-- ----------------------------------------------------------------------

#check f '' s
#check image f s
#check f ⁻¹' u       -- se escribe con \inv
#check preimage f u

-- ---------------------------------------------------------------------
-- Ejercicio 36. Demostrar que
--    f '' s = {y | ∃ x, x ∈ s ∧ f x = y}
-- ----------------------------------------------------------------------

example : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 37. Demostrar que
--    f ⁻¹' u = {x | f x ∈ u }
-- ----------------------------------------------------------------------

example : f ⁻¹' u = {x | f x ∈ u } := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 38. Demostrar que
--    f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v
-- ----------------------------------------------------------------------

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

-- ---------------------------------------------------------------------
-- Ejercicio 39. Demostrar que
--    f '' (s ∪ t) = f '' s ∪ f '' t
-- ----------------------------------------------------------------------

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left,
       use [x, xs] },
    { right,
      use [x, xt] }},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { use [x, or.inl xs] },
    { use [x, or.inr xt] }},
end

-- ---------------------------------------------------------------------
-- Ejercicio 40. Demostrar que
--    s ⊆ f ⁻¹' (f '' s)
-- ----------------------------------------------------------------------

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs],
end

-- ---------------------------------------------------------------------
-- Ejercicio 41. Demostrar que
--    f '' s ⊆ u ↔ s ⊆ f ⁻¹' u
-- ----------------------------------------------------------------------

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
begin
  split,
  { intros h x xs,
    have : f x ∈ f '' s,
      from mem_image_of_mem _ xs,
      exact h this },
  { intros h y ymem,
    rcases ymem with ⟨x, xs, fxeq⟩,
    rw ← fxeq,
    apply h xs },
end

-- Comentario: Se ha usado el lema
-- + mem_image_of_mem f : x ∈ s → f x ∈ f '' s

-- ---------------------------------------------------------------------
-- Ejercicio 42. Demostrar que si f es inyectiva, entonces
--    f ⁻¹' (f '' s) ⊆ s
-- ----------------------------------------------------------------------

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, fxeq⟩,
  rw ← h fxeq,
  exact ys,
end

-- ---------------------------------------------------------------------
-- Ejercicio 43. Demostrar que
--    f '' (f⁻¹' u) ⊆ u
-- ----------------------------------------------------------------------

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, xmem, rfl⟩,
  exact xmem,
end

-- ---------------------------------------------------------------------
-- Ejercicio 44. Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u) :=
-- ----------------------------------------------------------------------

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  rcases h y with ⟨x, fxeq⟩,
  use x,
  split,
  { show f x ∈ u,
    rw fxeq,
    exact yu },
  { exact fxeq },
end

-- ---------------------------------------------------------------------
-- Ejercicio 45. Demostrar que si s ⊂ t, entonces
--    f '' s ⊆ f '' t
-- ----------------------------------------------------------------------

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxeq⟩,
  use [x, h xs, fxeq],
end

-- ---------------------------------------------------------------------
-- Ejercicio 46. Demostrar que si u ⊆ v, entonces
--    f ⁻¹' u ⊆ f ⁻¹' v
-- ----------------------------------------------------------------------

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

-- ---------------------------------------------------------------------
-- Ejercicio 47. Demostrar que
--    f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v
-- ----------------------------------------------------------------------

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext x; refl

-- ---------------------------------------------------------------------
-- Ejercicio 48. Demostrar que
--    f '' (s ∩ t) ⊆ f '' s ∩ f '' t
-- ----------------------------------------------------------------------

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, fxeq⟩ ,
  split,
  { use [x, xs, fxeq] },
  { use [x, xt, fxeq] },
end

-- ---------------------------------------------------------------------
-- Ejercicio 49. Demostrar que si f es inyectiva, entonces
--    f '' s ∩ f '' t ⊆ f '' (s ∩ t)
-- ----------------------------------------------------------------------

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x, xs, fxeq⟩, ⟨z, zt, fzeq⟩⟩,
  use x,
  split,
  { split,
    { assumption },
    { have hxz : x = z :=
        (injective.eq_iff' h fzeq).mp fxeq,
      rw hxz,
      assumption }},
  { assumption },
end

-- ---------------------------------------------------------------------
-- Ejercicio 50. Demostrar que
--    f '' s \ f '' t ⊆ f '' (s \ t)
-- ----------------------------------------------------------------------

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxeq⟩, ynet⟩,
  use x,
  split,
  { split,
    { assumption },
    { intro xt,
      apply ynet,
      use [x, xt, fxeq] }},
  { assumption },
end

-- ---------------------------------------------------------------------
-- Ejercicio 51. Demostrar que
--    f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
-- ----------------------------------------------------------------------

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  rintros x ⟨h1, h2⟩,
  show f x ∈ u \ v,
  split,
  { apply h1 },
  { apply h2 },
end

-- ---------------------------------------------------------------------
-- Ejercicio 52. Demostrar que
--    (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v)
-- ----------------------------------------------------------------------

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { rintros ⟨⟨x, xs, fxeq⟩, yv⟩,
    use x,
    split,
    { split,
      { assumption },
      { show f x ∈ v,
        rw fxeq,
        assumption }},
    { assumption }},
  { rintros ⟨x, ⟨xs, xv⟩, fxeq⟩,
    use x,
    { exact ⟨xs, fxeq⟩ },
    { rw ← fxeq,
      apply xv }},
end

-- ---------------------------------------------------------------------
-- Ejercicio 53. Demostrar que
--    f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u
-- ----------------------------------------------------------------------

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
begin
  rintros y ⟨x, ⟨xs, xu⟩, fxy⟩,
  use x,
  split,
  { assumption },
  { assumption },
end

-- ---------------------------------------------------------------------
-- Ejercicio 54. Demostrar que
--    s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u)
-- ----------------------------------------------------------------------

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, xu⟩,
  show f x ∈ f '' s ∩ u,
  split,
  { use [x, xs, rfl] },
  { apply xu },
end

-- ---------------------------------------------------------------------
-- Ejercicio 55. Demostrar que
--    s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u)
-- ----------------------------------------------------------------------


example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | xu),
  { show f x ∈ f '' s ∪ u,
    use [x, xs, rfl] },
  { show f x ∈ f '' s ∪ u,
    apply mem_union_right,
    apply xu },
end

-- Comentario: Se ha usado el lema
-- + mem_union_right : x ∈ t → x ∈ s ∪ t

-- ---------------------------------------------------------------------
-- Ejercicio 56. Demostrar que
--    f '' (⋃ i, A i) = ⋃ i, f '' A i
-- ----------------------------------------------------------------------

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  { rintros ⟨i, x, xAi, fxeq⟩,
    exact ⟨x, ⟨i, xAi⟩, fxeq⟩ },
end

-- ---------------------------------------------------------------------
-- Ejercicio 57. Demostrar que
--    f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i
-- ----------------------------------------------------------------------


example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y,
  simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example
  (i : I)
  (injf : injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y,
  simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x,
  split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  { exact fxeq },
end

-- ---------------------------------------------------------------------
-- Ejercicio 58. Demostrar que
--    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

-- ---------------------------------------------------------------------
-- Ejercicio 59. Demostrar que
--    f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

-- ---------------------------------------------------------------------
-- Ejercicio 60. Demostrar el teorema de Cantor:
--    ∀ f : α → set α, ¬ surjective f
-- ----------------------------------------------------------------------

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with j,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  { have h₂ : j ∈ S,
      from h₁,
    have h₃ : j ∉ S,
      by rwa h at h₁,
    contradiction},
end

-- ---------------------------------------------------------------------
-- Ejercicio 61. Cerrar la sesión function_variables
-- ----------------------------------------------------------------------

end function_variables

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en la teoría sets.lean de Jeremy Avigad que se
-- encuentra en https://bit.ly/2ZW0ldf y se comenta en el vídeo
-- "Sets in Lean" que se encuentra en https://youtu.be/qlJrCtYiEkI
