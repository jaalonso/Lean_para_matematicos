import data.set.basic
import data.set.lattice
import data.nat.parity
import tactic.linarith
import tactic

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
--    s ∩ u ⊆ t ∩ u
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

-- 5ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
by rw diff_diff

-- ---------------------------------------------------------------------
-- Ejercicio 10. Demostrar que
--    (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
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

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left,
    exact ⟨xs, xt⟩ },
  { right,
    exact ⟨xs, xu⟩ },
end

-- 3ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  by finish
end

-- 4ª demostración
-- ===============

example :
  s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
by rw inter_union_distrib_left

-- ---------------------------------------------------------------------
-- Ejercicio 11. Demostrar que
--    s \ (t ∪ u) ⊆ (s \ t) \ u
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  intros x hx,
  split,
  { split,
    { exact hx.1, },
    { dsimp,
      intro xt,
      apply hx.2,
      left,
      exact xt, }},
  { dsimp,
    intro xu,
    apply hx.2,
    right,
    exact xu, },
end

-- 2ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  split,
  { split,
    { exact xs, },
    { intro xt,
      exact xntu (or.inl xt), }},
  { intro xu,
    exact xntu (or.inr xu), },
end

-- 3ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { intro xt,
    exact xntu (or.inl xt) },
  { intro xu,
    exact xntu (or.inr xu) },
end

-- 4ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩;
  finish,
end

-- 5ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by intro ; finish

-- 6ª demostración
-- ===============

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
by rw diff_diff

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
  { intro h,
    split,
    { exact h.2, },
    { exact h.1, }},
  { intro h,
    split,
    { exact h.2, },
    { exact h.1, }},
end

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext,
  simp only [mem_inter_eq],
  exact ⟨λ h, ⟨h.2, h.1⟩,
         λ h, ⟨h.2, h.1⟩⟩,
end

-- 3ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext,
  exact ⟨λ h, ⟨h.2, h.1⟩,
         λ h, ⟨h.2, h.1⟩⟩,
end

-- 4ª demostración
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

-- 5ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  exact and.comm,
end

-- Comentario: Se ha usado el lema
-- + and.comm : a ∧ b ↔ b ∧ a

-- 6ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
ext (λ x, and.comm)

-- 7ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

-- 8ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
inter_comm s t

-- Comentario: Se ha usado el lema
-- + inter_comm: a ∩ b = b ∩ a

-- 9ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 13. Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    dsimp at h,
    exact h.1, },
  { intro xs,
    dsimp,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    exact h.1, },
  { intro xs,
    split,
    { exact xs, },
    { left,
      exact xs, }},
end

-- 3ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext x,
  split,
  { intros h,
    exact h.1, },
  { intro xs,
    split,
    { exact xs, },
    { exact (or.inl xs), }},
end

-- 4ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨λ h, h.1,
         λ xs, ⟨xs, or.inl xs⟩⟩,
end

-- 5ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  exact ⟨and.left,
         λ xs, ⟨xs, or.inl xs⟩⟩,
end

-- 6ª demostración
-- ===============

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

-- 7ª demostración
-- ===============

example : s ∩ (s ∪ t) = s :=
inf_sup_self

-- ---------------------------------------------------------------------
-- Ejercicio 14. Demostrar que
--    s ∪ (s ∩ t) = s
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  { intro hx,
    cases hx with xs xst,
    { exact xs, },
    { exact xst.1, }},
  { intro xs,
    left,
    exact xs, },
end

-- 2ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  exact ⟨λ hx, or.dcases_on hx id and.left,
         λ xs, or.inl xs⟩,
end

-- 3ª demostración
-- ===============

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

-- 4ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
sup_inf_self

-- ---------------------------------------------------------------------
-- Ejercicio 15. Demostrar que
--    (s \ t) ∪ t = s ∪ t
-- ----------------------------------------------------------------------

-- 1ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  { intro hx,
    cases hx with xst xt,
    { left,
      exact xst.1, },
    { right,
      exact xt }},
  { by_cases h : x ∈ t,
    { intro _,
      right,
      exact h },
    { intro hx,
      cases hx with xs xt,
      { left,
        split,
        { exact xs, },
        { dsimp,
          exact h, }},
      { right,
        exact xt, }}},
end

-- 2ª definición
-- =============

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

-- 3ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext,
  simp,
  tauto,
end

-- 4ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
begin
  rw ext_iff,
  intro,
  rw iff_def,
  finish,
end

-- 5ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
by finish [ext_iff, iff_def]

-- 6ª definición
-- =============

example : (s \ t) ∪ t = s ∪ t :=
diff_union_self

-- ---------------------------------------------------------------------
-- Ejercicio 16. Demostrar que
--    (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

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

-- 2ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { finish, },
    { finish, }},
  { rintros ⟨xs | xt, nxst⟩,
    { finish, },
    { finish, }},
end

-- 3ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩) ; finish, },
  { rintros ⟨xs | xt, nxst⟩ ; finish, },
end

-- 4ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext,
  split,
  { finish, },
  { finish, },
end

-- 5ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  rw ext_iff,
  intro,
  rw iff_def,
  finish,
end

-- 6ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by finish [ext_iff, iff_def]

-- ---------------------------------------------------------------------
-- Ejercicio 17. Definir
-- + naturales como el conjunto de los números naturales,
-- + pares como el conjunto de los números naturales pares y
-- + impares como el conjunto de los números naturales impares.
-- ----------------------------------------------------------------------

def naturales : set ℕ := {n | true}
def pares     : set ℕ := {n | even n}
def impares   : set ℕ := {n | ¬ even n}

-- ---------------------------------------------------------------------
-- Ejercicio 18. Demostrar que la unión de pares e impares es el
-- conjunto de los números naturales.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : pares ∪ impares = naturales :=
begin
  unfold pares impares naturales,
  ext n,
  simp,
  apply classical.em,
end

-- 2ª demostración
-- ===============

example : pares ∪ impares = naturales :=
begin
  unfold pares impares naturales,
  ext n,
  finish,
end

-- 3ª demostración
-- ===============

example : pares ∪ impares = naturales :=
by finish [pares, impares, naturales, ext_iff]

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
-- Ejercicio 22. Los números primos y los mayores que 2 se definen por
--    def primos      : set ℕ := {n | prime n}
--    def mayoresQue2 : set ℕ := {n | n > 2}
--
-- Demostrar que
--    primos ∩ mayoresQue2 ⊆ impares
-- ----------------------------------------------------------------------

def primos      : set ℕ := {n | prime n}
def mayoresQue2 : set ℕ := {n | n > 2}

example : primos ∩ mayoresQue2 ⊆ impares :=
begin
  unfold primos mayoresQue2 impares,
  intro n,
  simp,
  intro hn,
  cases prime.eq_two_or_odd hn with h h,
  { rw h,
    intro,
    linarith, },
  { rw even_iff,
    rw h,
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

-- 1ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  split,
  { intro h,
    rw mem_Union,
    cases h with xs xUAi,
    rw mem_Union at xUAi,
    cases xUAi with i xAi,
    use i,
    split,
    { exact xAi, },
    { exact xs, }},
  { intro h,
    rw mem_Union at h,
    cases h with i hi,
    cases hi with xAi xs,
    split,
    { exact xs, },
    { rw mem_Union,
      use i,
      exact xAi, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩, },
  { rintros ⟨i, xAi, xs⟩,
    exact ⟨xs, ⟨i, xAi⟩⟩ },
end

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  finish [mem_inter_eq, mem_Union],
end

-- 4ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by finish [mem_inter_eq, mem_Union, ext_iff]

-- Comentario: Se han usado los lemas
-- + mem_inter_eq x s t : x ∈ s ∩ t = (x ∈ s ∧ x ∈ t)
-- + mem_Union : x ∈ Union A ↔ ∃ (i : ℕ), x ∈ A i

-- ---------------------------------------------------------------------
-- Ejercicio 26. Demostrar que
--    (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

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
  { intros h i,
    cases h with h1 h2,
    split,
    { exact h1 i },
    { exact h2 i }},
end

-- 2ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  exact ⟨λ h, ⟨λ i, (h i).1, λ i, (h i).2⟩,
         λ ⟨h1, h2⟩ i, ⟨h1 i, h2 i⟩⟩,
end

-- 3ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext,
  simp only [mem_inter_eq, mem_Inter],
  finish,
end

-- 4ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext,
  finish [mem_inter_eq, mem_Inter],
end

-- 5ª demostración
-- ===============

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
by finish [mem_inter_eq, mem_Inter, ext_iff]

-- ---------------------------------------------------------------------
-- Ejercicio 27. Cerrar la sección
-- ----------------------------------------------------------------------

end

-- ---------------------------------------------------------------------
-- Ejercicio 28. Abrir una sección
-- ----------------------------------------------------------------------

section

-- ---------------------------------------------------------------------
-- Ejercicio 29. Declarar A y B como familias de conjuntos de elementos
-- de tipo α indexadas por ℕ.
-- ----------------------------------------------------------------------

variables A B : ℕ → set α

-- ---------------------------------------------------------------------
-- Ejercicio 30. Demostrar que
--    s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { intros h i,
    cases h with xs xAi,
    { right,
      exact xs },
    { left,
      exact xAi i, }},
  { intro h,
    by_cases xs : x ∈ s,
    { left,
      exact xs },
    { right,
      intro i,
      cases h i with xAi xs,
      { exact xAi, },
      { contradiction, }}},
end

-- 2ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { rintros (xs | xI) i,
    { right,
      exact xs },
    { left,
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

-- 3ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { finish, },
  { finish, },
end

-- 4ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext,
  simp only [mem_union, mem_Inter],
  split ; finish,
end

-- 5ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext,
  simp only [mem_union, mem_Inter],
  finish [iff_def],
end

-- 6ª demostración
-- ===============

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
by finish [ext_iff, mem_union, mem_Inter, iff_def]

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
-- + s y t como variables sobre conjuntos de elementos de tipo α.
-- + u y v como variables sobre conjuntos de elementos de tipo β.
-- + A como variable de familias de conjuntos de α con índice en I.
-- + B como variable de familias de conjuntos de β con índice en I.
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
--    f ⁻¹' u = {x | f x ∈ u}
-- ----------------------------------------------------------------------

example : f ⁻¹' u = {x | f x ∈ u} := rfl

-- ---------------------------------------------------------------------
-- Ejercicio 38. Demostrar que
--    f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext x,
  split,
  { intro h,
    split,
    { apply mem_preimage.mpr,
      rw mem_preimage at h,
      exact mem_of_mem_inter_left h, },
    { apply mem_preimage.mpr,
      rw mem_preimage at h,
      exact mem_of_mem_inter_right h, }},
  { intro h,
    apply mem_preimage.mpr,
    split,
    { apply mem_preimage.mp,
      exact mem_of_mem_inter_left h,},
    { apply mem_preimage.mp,
      exact mem_of_mem_inter_right h, }},
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext x,
  exact ⟨λ h, ⟨mem_preimage.mpr (mem_of_mem_inter_left h),
               mem_preimage.mpr (mem_of_mem_inter_right h)⟩,
         λ h, ⟨mem_preimage.mp (mem_of_mem_inter_left h),
               mem_preimage.mp (mem_of_mem_inter_right h)⟩⟩,
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
begin
  ext,
  refl,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by {ext, refl}

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
rfl

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
preimage_inter

-- ---------------------------------------------------------------------
-- Ejercicio 39. Demostrar que
--    f '' (s ∪ t) = f '' s ∪ f '' t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { intro h1,
    cases h1 with x hx,
    cases hx with xst fxy,
    rw ← fxy,
    cases xst with xs xt,
    { left,
      apply mem_image_of_mem,
      exact xs, },
    { right,
      apply mem_image_of_mem,
      exact xt, }},
  { intro h2,
    cases h2 with yfs yft,
    { cases yfs with x hx,
      cases hx with xs fxy,
      rw ← fxy,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { cases yft with x hx,
      cases hx with xt fxy,
      rw ← fxy,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 2ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, fxy⟩,
    rw ← fxy,
    cases xst with xs xt,
    { left,
      exact mem_image_of_mem f xs, },
    { right,
      exact mem_image_of_mem f xt, }},
  { rintros (yfs | yft),
    { rcases yfs with ⟨x, xs, fxy⟩,
      rw ← fxy,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { rcases yft with ⟨x, xt, fxy⟩,
      rw ← fxy,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 3ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, rfl⟩,
    cases xst with xs xt,
    { left,
      exact mem_image_of_mem f xs, },
    { right,
      exact mem_image_of_mem f xt, }},
  { rintros (yfs | yft),
    { rcases yfs with ⟨x, xs, rfl⟩,
      apply mem_image_of_mem,
      left,
      exact xs, },
    { rcases yft with ⟨x, xt, rfl⟩,
      apply mem_image_of_mem,
      right,
      exact xt, }},
end

-- 4ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintro ⟨x, xst, rfl⟩,
    cases xst with xs xt,
    { left,
      use [x, xs], },
    { right,
      use [x, xt], }},
  { rintros (yfs | yft),
    { rcases yfs with ⟨x, xs, rfl⟩,
      use [x, or.inl xs], },
    { rcases yft with ⟨x, xt, rfl⟩,
      use [x, or.inr xt], }},
end

-- 5ª demostración
-- ===============

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

-- 6ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { finish, },
    { finish, }},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { finish, },
    { finish, }},
end

-- 7ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { rintros ⟨x, xs | xt, rfl⟩ ; finish, },
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩) ; finish, },
end

-- 8ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  split,
  { finish, },
  { finish, },
end

-- 9ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y,
  rw iff_def,
  finish,
end

-- 10ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
by finish [ext_iff, iff_def, mem_image_eq]

-- 11ª demostración
-- ===============

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
image_union f s t

-- ---------------------------------------------------------------------
-- Ejercicio 40. Demostrar que
--    s ⊆ f ⁻¹' (f '' s)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  apply mem_preimage.mpr,
  apply mem_image_of_mem,
  exact xs,
end

-- 2ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  apply mem_image_of_mem,
  exact xs,
end

-- 3ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
λ x, mem_image_of_mem f

-- 4ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs],
end

-- 5ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  use [x, xs],
end

-- 6ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
subset_preimage_image f s

-- ---------------------------------------------------------------------
-- Ejercicio 41. Demostrar que
--    f '' s ⊆ u ↔ s ⊆ f ⁻¹' u
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
begin
  split,
  { intros h x xs,
    apply mem_preimage.mpr,
    apply h,
    apply mem_image_of_mem,
    exact xs, },
  { intros h y hy,
    rcases hy with ⟨x, xs, fxy⟩,
    rw ← fxy,
    exact h xs, },
end

-- 2ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
begin
  split,
  { intros h x xs,
    apply h,
    apply mem_image_of_mem,
    exact xs, },
  { rintros h y ⟨x, xs, rfl⟩,
    exact h xs, },
end

-- 3ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
image_subset_iff

-- 4ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by simp

-- Comentario: Se ha usado el lema
-- + mem_image_of_mem f : x ∈ s → f x ∈ f '' s

-- ---------------------------------------------------------------------
-- Ejercicio 42. Demostrar que si f es inyectiva, entonces
--    f ⁻¹' (f '' s) ⊆ s
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rw mem_preimage at hx,
  rw mem_image_eq at hx,
  cases hx with y hy,
  cases hy with ys fyx,
  unfold injective at h,
  have h1 : y = x := h fyx,
  rw ← h1,
  exact ys,
end

-- 2ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rw mem_preimage at hx,
  rcases hx with ⟨y, ys, fyx⟩,
  rw ← h fyx,
  exact ys,
end

-- 3ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, hy⟩,
  rw ← h hy,
  exact ys,
end

-- ---------------------------------------------------------------------
-- Ejercicio 43. Demostrar que
--    f '' (f⁻¹' u) ⊆ u
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y h,
  cases h with x h2,
  cases h2 with hx fxy,
  rw ← fxy,
  exact hx,
end

-- 2ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y h,
  rcases h with ⟨x, hx, fxy⟩,
  rw ← fxy,
  exact hx,
end

-- 3ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hx, fxy⟩,
  rw ← fxy,
  exact hx,
end

-- 4ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hx, rfl⟩,
  exact hx,
end

-- 5ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
image_preimage_subset f u

-- 6ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 44. Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  use x,
  split,
  { apply mem_preimage.mpr,
    rw fxy,
    exact yu },
  { exact fxy },
end

-- 2ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  use x,
  split,
  { show f x ∈ u,
    rw fxy,
    exact yu },
  { exact fxy },
end

-- 3ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  by finish,
end

-- ---------------------------------------------------------------------
-- Ejercicio 45. Demostrar que si s ⊆ t, entonces
--    f '' s ⊆ f '' t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rw mem_image at hy,
  cases hy with x hx,
  cases hx with xs fxy,
  use x,
  split,
  { exact h xs, },
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, xs, fxy⟩,
  use x,
  exact ⟨h xs, fxy⟩,
end

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxy ⟩,
  use [x, h xs, fxy],
end

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
by finish [subset_def, mem_image_eq]

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : f '' s ⊆ f '' t :=
image_subset f h

-- ---------------------------------------------------------------------
-- Ejercicio 46. Demostrar que si u ⊆ v, entonces
--    f ⁻¹' u ⊆ f ⁻¹' v
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  apply mem_preimage.mpr,
  apply h,
  apply mem_preimage.mp,
  exact hx,
end

-- 2ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  apply h,
  exact hx,
end

-- 3ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  exact h hx,
end

-- 4ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
λ x hx, h hx

-- 5ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

-- 6ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
preimage_mono h

-- 7ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by tauto

-- ---------------------------------------------------------------------
-- Ejercicio 47. Demostrar que
--    f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { intros h,
    rw mem_preimage at h,
    cases h with fxu fxv,
    { left,
      apply mem_preimage.mpr,
      exact fxu, },
    { right,
      apply mem_preimage.mpr,
      exact fxv, }},
  { intro h,
    rw mem_preimage,
    cases h with xfu xfv,
    { rw mem_preimage at xfu,
      left,
      exact xfu, },
    { rw mem_preimage at xfv,
      right,
      exact xfv, }},
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { intros h,
    cases h with fxu fxv,
    { left,
      exact fxu, },
    { right,
      exact fxv, }},
  { intro h,
    cases h with xfu xfv,
    { left,
      exact xfu, },
    { right,
      exact xfv, }},
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { rintro (fxu | fxv),
    { exact or.inl fxu, },
    { exact or.inr fxv, }},
  { rintro (xfu | xfv),
    { exact or.inl xfu, },
    { exact or.inr xfv, }},
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  split,
  { finish, },
  { finish, } ,
end

-- 5ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
begin
  ext x,
  finish,
end

-- 6ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext; finish

-- 7ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext; refl

-- 8ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
rfl

-- 9ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
preimage_union

-- 10ª demostración
-- ===============

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 48. Demostrar que
--    f '' (s ∩ t) ⊆ f '' s ∩ f '' t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with xst fxy,
  split,
  { use x,
    split,
    { exact xst.1, },
    { exact fxy, }},
  { use x,
    split,
    { exact xst.2, },
    { exact fxy, }},
end

-- 2ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, ⟨xs, xt⟩, fxy⟩,
  split,
  { use x,
    exact ⟨xs, fxy⟩, },
  { use x,
    exact ⟨xt, fxy⟩, },
end

-- 3ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, fxy⟩,
  split,
  { use [x, xs, fxy], },
  { use [x, xt, fxy], },
end

-- 4ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
image_inter_subset f s t

-- 5ª demostración
-- ===============

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by intro ; finish

-- ---------------------------------------------------------------------
-- Ejercicio 49. Demostrar que si f es inyectiva, entonces
--    f '' s ∩ f '' t ⊆ f '' (s ∩ t)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  intros y hy,
  cases hy  with hy1 hy2,
  cases hy1 with x1 hx1,
  cases hx1 with x1s fx1y,
  cases hy2 with x2 hx2,
  cases hx2 with x2t fx2y,
  use x1,
  split,
  { split,
    { exact x1s, },
    { convert x2t,
      apply h,
      rw ← fx2y at fx1y,
      exact fx1y, }},
  { exact fx1y, },
end

-- 2ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩,
  use x1,
  split,
  { split,
    { exact x1s, },
    { convert x2t,
      apply h,
      rw ← fx2y at fx1y,
      exact fx1y, }},
  { exact fx1y, },
end

-- 3ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x1, x1s, fx1y⟩, ⟨x2, x2t, fx2y⟩⟩,
  unfold injective at h,
  finish,
end

-- 4ª demostración
-- ===============

example
  (h : injective f)
  : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
by intro ; unfold injective at *  ; finish

-- ---------------------------------------------------------------------
-- Ejercicio 50. Demostrar que
--    f '' s \ f '' t ⊆ f '' (s \ t)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  intros y hy,
  cases hy with yfs ynft,
  cases yfs with x hx,
  cases hx with xs fxy,
  use x,
  split,
  { split,
    { exact xs, },
    { dsimp,
      intro xt,
      apply ynft,
      rw ← fxy,
      apply mem_image_of_mem,
      exact xt, }},
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxy⟩, ynft⟩,
  use x,
  split,
  { split,
    { exact xs, },
    { intro xt,
      apply ynft,
      use [x, xt, fxy], }},
  { exact fxy, },
end

-- 3ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x, xs, fxy⟩, ynft⟩,
  use x,
  finish,
end

-- 4ª demostración
-- ===============

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
subset_image_diff f s t

-- ---------------------------------------------------------------------
-- Ejercicio 51. Demostrar que
--    f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  rw mem_preimage,
  split,
  { rw ← mem_preimage,
    exact hx.1, },
  { dsimp,
    rw ← mem_preimage,
    exact hx.2, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  split,
  { exact hx.1, },
  { exact hx.2, },
end

-- 3ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  exact ⟨hx.1, hx.2⟩,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  rintros x ⟨h1, h2⟩,
  exact ⟨h1, h2⟩,
end

-- 5ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
subset.rfl

-- 6ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 52. Demostrar que
--    (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { intro hy,
    cases hy with hyfs yv,
    cases hyfs with x hx,
    cases hx with xs fxy,
    use x,
    split,
    { split,
      { exact xs, },
      { rw mem_preimage,
        rw fxy,
        exact yv, }},
    { exact fxy, }},
  { intro hy,
    cases hy with x hx,
    split,
    { use x,
      split,
      { exact hx.1.1, },
      { exact hx.2, }},
    { cases hx with hx1 fxy,
      rw ← fxy,
      rw ← mem_preimage,
      exact hx1.2, }},
end

-- 2ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { rintros ⟨⟨x, xs, fxy⟩, yv⟩,
    use x,
    split,
    { split,
      { exact xs, },
      { rw mem_preimage,
        rw fxy,
        exact yv, }},
    { exact fxy, }},
  { rintros ⟨x, ⟨xs, xv⟩, fxy⟩,
    split,
    { use [x, xs, fxy], },
    { rw ← fxy,
      rw ← mem_preimage,
      exact xv, }},
end

-- 3ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { rintros ⟨⟨x, xs, fxy⟩, yv⟩,
    finish, },
  { rintros ⟨x, ⟨xs, xv⟩, fxy⟩,
    finish, },
end

-- 4ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by ext ; split ; finish

-- 5ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by finish [ext_iff, iff_def]

-- 6ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
(set.push_pull f s v).symm

-- ---------------------------------------------------------------------
-- Ejercicio 53. Demostrar que
--    f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with hx1 fxy,
  cases hx1 with xs xv,
  { left,
    use x,
    split,
    { exact xs, },
    { exact fxy, }},
  { right,
    rw ← fxy,
    exact xv, },
end

-- 2ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  rintros y ⟨x, xs | xv, fxy⟩,
  { left,
    use [x, xs, fxy], },
  { right,
    rw ← fxy,
    exact xv, },
end

-- 3ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  rintros y ⟨x, xs | xv, fxy⟩;
  finish,
end

-- ---------------------------------------------------------------------
-- Ejercicio 54. Demostrar que
--    s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  intros x hx,
  rw mem_preimage,
  split,
  { apply mem_image_of_mem,
    exact hx.1, },
  { rw ← mem_preimage,
    exact hx.2, },
end

-- 2ª demostración
-- ===============

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, xu⟩,
  split,
  { exact mem_image_of_mem f xs, },
  { exact xu, },
end

-- 3ª demostración
-- ===============

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, xu⟩,
  exact ⟨mem_image_of_mem f xs, xu⟩,
end

-- 4ª demostración
-- ===============

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, xu⟩,
  show f x ∈ f '' s ∩ u,
  split,
  { use [x, xs, rfl] },
  { exact xu },
end

-- 5ª demostración
-- ===============

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
inter_preimage_subset s u f

-- ---------------------------------------------------------------------
-- Ejercicio 55. Demostrar que
--    s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  intros x hx,
  rw mem_preimage,
  cases hx with xs xu,
  { apply mem_union_left,
    apply mem_image_of_mem,
    exact xs, },
  { apply mem_union_right,
    rw ← mem_preimage,
    exact xu, },
end

-- 2ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  intros x hx,
  cases hx with xs xu,
  { apply mem_union_left,
    apply mem_image_of_mem,
    exact xs, },
  { apply mem_union_right,
    exact xu, },
end

-- 3ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | xu),
  { left,
    exact mem_image_of_mem f xs, },
  { right,
    exact xu, },
end

-- 4ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | xu),
  { exact or.inl (mem_image_of_mem f xs), },
  { exact or.inr xu, },
end

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  intros x h,
  exact or.elim h (λ xs, or.inl (mem_image_of_mem f xs)) or.inr,
end

-- 6ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
λ x h, or.elim h (λ xs, or.inl (mem_image_of_mem f xs)) or.inr

-- 7ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | xu),
  { show f x ∈ f '' s ∪ u,
    use [x, xs, rfl] },
  { show f x ∈ f '' s ∪ u,
    right,
    apply xu },
end

-- 8ª demostración
-- ===============

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
union_preimage_subset s u f

-- Comentario: Se ha usado el lema
-- + mem_union_right : x ∈ t → x ∈ s ∪ t

-- ---------------------------------------------------------------------
-- Ejercicio 56. Demostrar que
--    f '' (⋃ i, A i) = ⋃ i, f '' A i
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  split,
  { intro hy,
    rw mem_image at hy,
    cases hy with x hx,
    cases hx with xUA fxy,
    rw mem_Union at xUA,
    cases xUA with i xAi,
    rw mem_Union,
    use i,
    rw ← fxy,
    apply mem_image_of_mem,
    exact xAi, },
  { intro hy,
    rw mem_Union at hy,
    cases hy with i yAi,
    cases yAi with x hx,
    cases hx with xAi fxy,
    rw ← fxy,
    apply mem_image_of_mem,
    rw mem_Union,
    use i,
    exact xAi, },
end

-- 2ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxy⟩,
    use [i, x, xAi, fxy] },
  { rintros ⟨i, x, xAi, fxy⟩,
    exact ⟨x, ⟨i, xAi⟩, fxy⟩ },
end

-- 3ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by tidy

-- 4ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
image_Union

-- ---------------------------------------------------------------------
-- Ejercicio 57. Demostrar que
--    f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intros y h,
  apply mem_Inter_of_mem,
  intro i,
  cases h with x hx,
  cases hx with xIA fxy,
  rw ← fxy,
  apply mem_image_of_mem,
  exact mem_Inter.mp xIA i,
end

-- 2ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intros y h,
  apply mem_Inter_of_mem,
  intro i,
  rcases h with ⟨x, xIA, rfl⟩,
  exact mem_image_of_mem f (mem_Inter.mp xIA i),
end

-- 3ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y,
  simp,
  intros x xIA fxy i,
  use [x, xIA i, fxy],
end

-- 4ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by tidy

-- ---------------------------------------------------------------------
-- Ejercicio 58. Demostrar que si f es inyectiva, entonces
--    (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (i : I)
  (injf : injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intros y hy,
  rw mem_Inter at hy,
  rcases hy i with ⟨x, xAi, fxy⟩,
  use x,
  split,
  { apply mem_Inter_of_mem,
    intro j,
    rcases hy j with ⟨z, zAj, fzy⟩,
    convert zAj,
    apply injf,
    rw fxy,
    rw ← fzy, },
  { exact fxy, },
end

-- 2ª demostración
-- ===============

example
  (i : I)
  (injf : injective f)
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y,
  simp,
  intro h,
  rcases h i with ⟨x, xAi, fxy⟩,
  use x,
  split,
  { intro j,
    rcases h j with ⟨z, zAi, fzy⟩,
    have : f x = f z, by rw [fxy, fzy],
    have : x = z, from injf this,
    rw this,
    exact zAi },
  { exact fxy },
end

-- ---------------------------------------------------------------------
-- Ejercicio 59. Demostrar que
--    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
begin
  ext x,
  split,
  { intro hx,
    rw mem_preimage at hx,
    rw mem_Union at hx,
    cases hx with i fxBi,
    rw mem_Union,
    use i,
    apply mem_preimage.mpr,
    exact fxBi, },
  { intro hx,
    rw mem_preimage,
    rw mem_Union,
    rw mem_Union at hx,
    cases hx with i xBi,
    use i,
    rw mem_preimage at xBi,
    exact xBi, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
preimage_Union

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 60. Demostrar que
--    f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  split,
  { intro hx,
    apply mem_Inter_of_mem,
    intro i,
    rw mem_preimage,
    rw mem_preimage at hx,
    rw mem_Inter at hx,
    exact hx i, },
  { intro hx,
    rw mem_preimage,
    rw mem_Inter,
    intro i,
    rw ← mem_preimage,
    rw mem_Inter at hx,
    exact hx i, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  calc  (x ∈ f ⁻¹' ⋂ (i : I), B i)
      ↔ f x ∈ ⋂ (i : I), B i       : mem_preimage
  ... ↔ (∀ i : I, f x ∈ B i)       : mem_Inter
  ... ↔ (∀ i : I, x ∈ f ⁻¹' B i)   : iff_of_eq rfl
  ... ↔ x ∈ ⋂ (i : I), f ⁻¹' B i   : mem_Inter.symm,
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  simp,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext, simp }

-- ---------------------------------------------------------------------
-- Ejercicio 61. Demostrar el teorema de Cantor:
--    ∀ f : α → set α, ¬ surjective f
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  unfold surjective at surjf,
  cases surjf S with j fjS,
  by_cases j ∈ S,
  { apply absurd _ h,
    rw fjS,
    exact h, },
  { apply h,
    rw ← fjS at h,
    exact h, },
end

-- 2ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  cases surjf S with j fjS,
  by_cases j ∈ S,
  { apply absurd _ h,
    rwa fjS, },
  { apply h,
    rwa ← fjS at h, },
end

-- 3ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
cantor_surjective

-- ---------------------------------------------------------------------
-- Ejercicio 62. Cerrar la sesión function_variables
-- ----------------------------------------------------------------------

end function_variables

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en la teoría sets.lean de Jeremy Avigad que se
-- encuentra en https://bit.ly/2ZW0ldf y se comenta en el vídeo
-- "Sets in Lean" que se encuentra en https://youtu.be/qlJrCtYiEkI
