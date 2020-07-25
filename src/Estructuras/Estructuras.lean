import data.rat.basic
import data.nat.parity
import tactic.basic

------------------------------------------------------------------------
-- § Introducción                                                     --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la teoría de los naturales. 
-- ----------------------------------------------------------------------

open nat

-- ---------------------------------------------------------------------
-- Ejercicio. Permitir en esta teoría definiciones no computables. 
-- ----------------------------------------------------------------------

noncomputable theory 

-- ---------------------------------------------------------------------
-- Ejercicio. Permitir el uso de la lógica clásica. 
-- ----------------------------------------------------------------------

open_locale classical 

------------------------------------------------------------------------
-- § Estructuras y clases                                             --
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §§ Declaración de estructuras                                      --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructura even_natural_number con dos campos
-- + n que es un número natural
-- + even_n que es una demostración de que n es par. 
-- ----------------------------------------------------------------------

structure even_natural_number : Type :=
  (n : ℕ)
  (even_n : even n)

-- ---------------------------------------------------------------------
-- Ejercicio. Ver la información de even_natural_number 
-- ----------------------------------------------------------------------

#print even_natural_number

-- Comentario: Al colocar el curso sobre print se obtiene
--    structure even_natural_number : Type
--    fields:
--    even_natural_number.n : even_natural_number → ℕ
--    even_natural_number.even_n : ∀ (c : even_natural_number), c.n.even

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructuras (is_even_cube_above_100 n) cuyos
-- campos son
-- + even con una demostración de que n es par
-- + is_cube con una demostración de que n es un cubo y
-- + gt_100 con una demostración de que n es mayor que 100. 
-- ----------------------------------------------------------------------

structure is_even_cube_above_100 (n : ℕ) : Prop :=
  (even : evens n)
  (is_cube : ∃ k, n = k^3)
  (gt_100 : n > 100)

-- ---------------------------------------------------------------------
-- Ejercicio. Ver la información de (is_even_cube_above_100).
-- ----------------------------------------------------------------------

#print is_even_cube_above_100

-- Comentario: Al colocar el cursor sobre print se obtiene
--    structure is_even_cube_above_100 : ℕ → Prop
--    fields:
--    is_even_cube_above_100.even : 
---     ∀ {n : ℕ}, is_even_cube_above_100 n → n.even
--    is_even_cube_above_100.is_cube : 
--      ∀ {n : ℕ}, is_even_cube_above_100 n → (∃ (k : ℕ), n = k ^ 3)
--    is_even_cube_above_100.gt_100 : 
--      ∀ {n : ℕ}, is_even_cube_above_100 n → n > 100

-- ---------------------------------------------------------------------
-- Ejercicio. Definir las estructuras (bound f) cuyo argumento es una
-- función de ℕ en ℕ y sus camposson
-- + bound que es un número natural
-- + le_bound que es una prueba de que bound es una cota superior de f. 
-- ----------------------------------------------------------------------

structure bounds (f : ℕ → ℕ) :=
  (bound : ℕ)
  (le_bound : ∀ (n : ℕ), f n ≤ bound)

-- ---------------------------------------------------------------------
-- Ejercicio. Ver la información de bounds
-- ----------------------------------------------------------------------

#print bounds

-- Comentario: Al colocar el cursor sobre print se obtiene
--    structure bounds : (ℕ → ℕ) → Type
--    fields:
--    bounds.bound : Π {f : ℕ → ℕ}, bounds f → ℕ
--    bounds.le_bound : ∀ {f : ℕ → ℕ} (c : bounds f) (n : ℕ), f n ≤ c.bound

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructura eventually_constant_sequence cuyos
-- campos son
-- + seq que es una sucesión entera
-- + eventually_constant que afirma que seq es eventualmente constante.
-- ----------------------------------------------------------------------

structure eventually_constant_sequence : Type :=
(seq : ℕ → ℕ)
(eventually_constant : ∃ k v, ∀ n ≥ k, seq n = v)


-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructura bipointed_type de los tipos don dos
-- elementos distintos.   
-- ----------------------------------------------------------------------

structure bipointed_type :=
(A : Type)
(x y : A)
(x_ne_y : x ≠ y)
-- omit

------------------------------------------------------------------------
-- § Proyecciones de una estructura                                   --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    is_even_cube_above_100 n
-- entonces n es mayor que 100.
-- ----------------------------------------------------------------------

-- 1ª demostración 
-- ===============

example 
  (n : ℕ) 
  (hn : is_even_cube_above_100 n) 
  : n > 100 :=
is_even_cube_above_100.gt_100 hn

-- 1ª demostración 
-- ===============

section

open is_even_cube_above_100

example 
  (n : ℕ) 
  (hn : is_even_cube_above_100 n) 
  : n > 100 :=
gt_100 hn

end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    is_even_cube_above_100 n
-- entonces n es par.
-- ----------------------------------------------------------------------

example 
  (n : ℕ) 
  (hn : is_even_cube_above_100 n) 
  : even n :=
hn.even

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    is_even_cube_above_100 n
-- entonces n es par y cubo.
-- ----------------------------------------------------------------------

example 
  (n : ℕ) 
  (hn : is_even_cube_above_100 n) 
  : even n ∧ ∃ k, n = k^3 :=
⟨ hn.even, hn.is_cube ⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    is_even_cube_above_100 n
-- entonces n es par, mayor que 100 y cubo.
-- ----------------------------------------------------------------------

example 
  (n : ℕ) 
  (hn : is_even_cube_above_100 n) 
  : even n ∧ n > 100 ∧ (∃ k, n = k^3) :=
⟨ hn.1, hn.3, hn.2 ⟩


-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    is_even_cube_above_100' : ℕ → Prop
-- tal que 8is_even_cube_above_100') afirma que n es par, cubo y mayor
-- que 100. 
-- ----------------------------------------------------------------------

def is_even_cube_above_100' (n : ℕ) : Prop :=
even n ∧ (∃ k, n = k^3) ∧ n > 100

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el subtipo even_natural_number' de los números
-- naturales pares.
-- ----------------------------------------------------------------------

def even_natural_number' : Type :=
{ n : ℕ // even n }

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto set_of_even_natural_numbers de los
-- números naturales pares. 
-- ----------------------------------------------------------------------

def set_of_even_natural_numbers : set ℕ :=
{ n : ℕ | even n }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    even_natural_number → even_natural_number'
-- ----------------------------------------------------------------------

example : even_natural_number → even_natural_number' :=
λ n, ⟨n.1, n.2⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que, parado todo natural n,
--    is_even_cube_above_100 n → is_even_cube_above_100' n
-- ----------------------------------------------------------------------

example (n : ℕ) : is_even_cube_above_100 n → is_even_cube_above_100' n :=
λ hn, ⟨hn.even, hn.is_cube, hn.gt_100⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    even_natural_number' → even_natural_number
-- ----------------------------------------------------------------------

-- 1ª demostración
example : even_natural_number' → even_natural_number :=
λ n,
{ even_natural_number .
  n      := n.1,
  even_n := n.2 }

-- 2ª demostración
example : even_natural_number' → even_natural_number :=
λ n,
{ n      := n.1,
  even_n := n.2 }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que, para todo número natural n,
--    is_even_cube_above_100' n → is_even_cube_above_100 n
-- ----------------------------------------------------------------------

example 
  (n : ℕ) 
  : is_even_cube_above_100' n → is_even_cube_above_100 n :=
λ ⟨h1n, h2n, h3n⟩,
{ even    := h1n,
  is_cube := h2n,
  gt_100  := h3n }

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    bounds' : (ℕ → ℕ) → Type
-- tal que (bound' f) es el subtipo de las cotas superiores de f.
-- ----------------------------------------------------------------------

def bounds' (f : ℕ → ℕ) : Type :=
{ n : ℕ // ∀ (m : ℕ), f m ≤ n }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que para toda f,
--    bounds f → bounds' f
-- ----------------------------------------------------------------------

example 
  (f : ℕ → ℕ) 
  : bounds f → bounds' f :=
λ ⟨n, hn⟩, ⟨n, hn⟩ 

-- ----------------------------------------------------------------------
-- Ejercicio. Demostrar que para toda f,
--    bounds' f → bounds f
-- ----------------------------------------------------------------------

example 
  (f : ℕ → ℕ) 
  : bounds' f → bounds f :=
λ n, { bound := n.1, le_bound := n.2 }

------------------------------------------------------------------------
-- § Clases                                                           --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase
--    is_square : ℕ → Prop
-- tal que (is_square n) si n es un cuadrado.
-- ----------------------------------------------------------------------

@[class] def is_square (n : ℕ) : Prop := ∃k : ℕ, k^2 = n

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar el espacio de nombres is_square. 
-- ----------------------------------------------------------------------

namespace is_square

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función 
--    sqrt : ℕ → ℕ 
-- yal que, si n es un número cuadrado, entonces (sqrt n) es su raíz
-- cuadrada. 
-- ----------------------------------------------------------------------

def sqrt (n : ℕ) [hn : is_square n] : ℕ := classical.some hn

-- Comentario: Se ha usado el lema
-- + classical.some : (∃ (x : ℕ), p x) → ℕ [2 times]

-- ---------------------------------------------------------------------
-- Ejercicio. Definir √ como notación para la raíz cuadrada.  
-- ----------------------------------------------------------------------

prefix `√`:(max+1) := sqrt 

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si n es un cuadrado, entonces
--    (√n) ^ 2 = n
-- y declararlo como regla de simplificación
-- ----------------------------------------------------------------------

@[simp] lemma square_sqrt 
  (n : ℕ) 
  [hn : is_square n] 
  : (√n) ^ 2 = n :=
classical.some_spec hn

-- Comentario: Se ha usado el lema
-- + classical.some_spec : ∀ (h : ∃ (x : ℕ), p x), p (classical.some h) 

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si n es un número cuadrado, entonces
--    √n = k ↔ n = k^2
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (n k : ℕ) 
  [is_square n] 
  : √n = k ↔ n = k^2 :=
begin
  split, 
  { intro h,
    rw ← h,
    exact (square_sqrt n).symm },
  { intro h,
    apply pow_left_inj (nat.zero_le _) (nat.zero_le k) two_pos,
    simp [h] },
end

-- Comentario: Se usan los lemas
-- + pow_left_inj : 0 ≤ x → 0 ≤ y → 0 < n → x ^ n = y ^ n → x = y 
-- + zero_le : ∀ (n : ℕ), 0 ≤ n 
-- + two_pos : 0 < 2

-- 2ª demostración
-- ===============

@[simp] lemma sqrt_eq_iff 
  (n k : ℕ) 
  [is_square n] 
  : √n = k ↔ n = k^2 :=
begin
  split; 
  intro h,
  { simp [← h] },
  { exact pow_left_inj (nat.zero_le _) (nat.zero_le k) two_pos (by simp [h]) }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que n^2 es un cuadrado y declararlo como
-- instancia (para aplicarlo directamente en las inferencias de clases).
-- ----------------------------------------------------------------------

instance square_square 
  (n : ℕ) 
  : is_square (n^2) :=
⟨n, rfl⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    √(n ^ 2) 0 n
-- ----------------------------------------------------------------------

lemma sqrt_square 
  (n : ℕ) 
  : √(n ^ 2) = n :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el producto de dos cuadrados es un cuadrado
-- (y declarlo como instancia)
-- ----------------------------------------------------------------------

example
  (n m : ℕ) 
  [is_square n] 
  [is_square m] 
  : is_square (n*m) :=
begin
  use (√n * √m),
  rw nat.mul_pow,
  rw square_sqrt,
  rw square_sqrt,
end

-- Prueba
-- ======

/-
n m : ℕ,
_inst_1 : is_square n,
_inst_2 : is_square m
⊢ is_square (n * m)
  >> use (√n * √m),
⊢ (√n * √m) ^ 2 = n * m
  >> rw nat.mul_pow,
⊢ √n ^ 2 * √m ^ 2 = n * m
  >> rw square_sqrt,
⊢ n * √m ^ 2 = n * m
  >> rw square_sqrt,
no goals
-/

-- 2ª demostración
-- ===============

instance square_mul 
  (n m : ℕ) 
  [is_square n] 
  [is_square m] 
  : is_square (n*m) :=
⟨√n * √m, by simp [nat.mul_pow]⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si n y m son cuadrados, entonces
--    √(n * m) = √n * √m
-- ----------------------------------------------------------------------

lemma sqrt_mul 
  (n m : ℕ) 
  [is_square n] 
  [is_square m] 
  : √(n * m) = √n * √m :=
by simp [nat.mul_pow]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si n es un cuadrado, entonces
--    √(n * m ^ 2) = √n * m
-- ----------------------------------------------------------------------

example 
  (n m : ℕ) 
  [is_square n] 
  : √(n * m ^ 2) = √n * m :=
by simp [sqrt_mul, sqrt_square]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si n es un cuadrado, entonces
--    √n ≤ n
-- ----------------------------------------------------------------------

lemma sqrt_le 
  (n : ℕ) 
  [is_square n] 
  : √n ≤ n :=
begin
  conv_rhs { rw [← square_sqrt n, nat.pow_two] }, 
             apply nat.le_mul_self
end

-- Comentario: Se han usado los lemas
-- + nat.le_mul_self : n ≤ n * n
-- + nat.pow_two : n ^ 2 = n * n 

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar el espacio de nombres is_square. 
-- ----------------------------------------------------------------------

end is_square

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar la sección bijections. 
-- ----------------------------------------------------------------------

section bijections

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la teoría function. 
-- ----------------------------------------------------------------------

open function

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar α y β como variables de tipo. 
-- ----------------------------------------------------------------------

variables {α β : Type*}

-- ---------------------------------------------------------------------
-- Ejercicio. Obtener la información de la estructura equiv. 
-- ----------------------------------------------------------------------

#print equiv

-- Comentario: Al colocar el cursor sobre print se obtiene
--    structure equiv : 
--      Sort u_1 → Sort u_2 → Sort (max 1 (imax u_1 u_2) (imax u_2 u_1))
--    fields:
--    equiv.to_fun : Π {α : Sort u_1} {β : Sort u_2}, α ≃ β → α → β
--    equiv.inv_fun : Π {α : Sort u_1} {β : Sort u_2}, α ≃ β → β → α
--    equiv.left_inv : ∀ {α : Sort u_1} {β : Sort u_2} (c : α ≃ β), 
--                     left_inverse c.inv_fun c.to_fun
--    equiv.right_inv : ∀ {α : Sort u_1} {β : Sort u_2} (c : α ≃ β), 
--                      right_inverse c.inv_fun c.to_fun
--
-- Su definición es
--    structure equiv (α β : Type*) :=
--    (to_fun    : α → β)
--    (inv_fun   : β → α)
--    (left_inv  : left_inverse inv_fun to_fun)
--    (right_inv : right_inverse inv_fun to_fun)
-- Es decir, da una equivalencia (biyección) entre dos tipos.

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructura biyection que afirma la existencia
-- de una aplicación inyectiva y suprayectiva entre los tipos.
-- ----------------------------------------------------------------------

structure bijection (α β : Type*) :=
  (to_fun : α → β)
  (injective : injective to_fun)
  (surjective : surjective to_fun)

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar bijection como una instancia de has_coe_to_fun
-- para tratar las biyecciones como funciones.
-- ----------------------------------------------------------------------

instance : has_coe_to_fun (bijection α β) :=
⟨_, λ f, f.to_fun⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Ampliar la táctica de extensionalidad a las biyecciones. 
-- ----------------------------------------------------------------------

@[ext] 
def bijection.ext 
  {f g : bijection α β} 
  (hfg : ∀ x, f x = g x) 
  : f = g :=
by { cases f, cases g, congr, ext, exact hfg x }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el lema coe_mk para reducir la aplicación de una
-- biyección a un argumento. 
-- ----------------------------------------------------------------------

@[simp] 
lemma coe_mk 
  {f : α → β} 
  {h1f : injective f} 
  {h2f : surjective f} 
  {x : α} 
  : { bijection . to_fun := f, 
      injective := h1f, 
      surjective := h2f } x = f x :=
 rfl

-- ---------------------------------------------------------------------
-- Ejercicio. Definir equiv_of_bijection tal que, si f es una biyección
-- de α en β entonces (equiv_of_bijection f) es una equivalencia entre α
-- y β.
-- ----------------------------------------------------------------------

def equiv_of_bijection (f : bijection α β) : α ≃ β :=
begin
  exact equiv.of_bijective f ⟨f.injective, f.surjective⟩
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir bijection_of_equiv tal que si f es una
-- equivalencia entre α y β, entonces (bijection_of_equiv f) es una
-- biyección de α en β. 
-- ----------------------------------------------------------------------

def bijection_of_equiv (f : α ≃ β) : bijection α β :=
{ to_fun := f,
  injective := f.injective,
  surjective := f.surjective }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las biyecciones son equivalentes a las
-- equivalencias. 
-- ----------------------------------------------------------------------

def bijection_equiv_equiv : bijection α β ≃ (α ≃ β) :=
{ to_fun := equiv_of_bijection,
  inv_fun := bijection_of_equiv,
  left_inv := 
    by { intro f, ext, simp [bijection_of_equiv, equiv_of_bijection] },
  right_inv := 
    by { intro f, ext, simp [bijection_of_equiv, equiv_of_bijection] } }

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar la sección bijections
-- ----------------------------------------------------------------------

end bijections



/-! ### Exercise: Bundled groups -/

/-! Below is a possible definition of a group in Lean.
  It's not the definition we use use in mathlib. The actual definition uses classes,
  and will be explained in detail in the next session. -/

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructura Group que tiene 
--    + universo: G, 
--    + operación interna: op (representada por *) 
--    + elemento neutro por la izquierda: id (representado por 1)
--    + inverso por la izquierda inv (representado por ⁻¹)
-- y verifica los axiomas
--    + asociativa: ∀ (x y z : G), (x * y) * z = x * (y * z)
--    + neutro: ∀ (x : G), 1 * x = x)
--    + inverso: ∀ (x : G), x⁻¹ * x = 1
-- ----------------------------------------------------------------------

structure Group :=
  (G : Type*)
  (op : G → G → G) (infix *    := op)
  (id : G)         (notation 1 := id) 
  (inv : G → G)    (postfix ⁻¹ := inv) 
  (op_assoc' : ∀ (x y z : G), (x * y) * z = x * (y * z))
  (id_op' : ∀ (x : G), 1 * x = x)
  (op_left_inv' : ∀ (x : G), x⁻¹ * x = 1)

-- ---------------------------------------------------------------------
-- Ejercicio. Extender la estructura Group a CommGroup de los grupos
-- conmutativos.  
-- ----------------------------------------------------------------------

structure CommGroup extends Group :=
  (infix * := op)
  (op_comm : ∀ (x y : G), x * y = y * x)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el grupo aditivo de los racionales. 
-- ----------------------------------------------------------------------

def rat_Group : Group :=
{ G := ℚ,
  op := (+), 
  id := 0,
  inv := λ x, -x,
  op_assoc' := add_assoc,
  id_op' := zero_add,
  op_left_inv' := neg_add_self }

-- ---------------------------------------------------------------------
-- Ejercicio. Extender el grupo aditivo de los racionales a grupo
-- conmutativo.  
-- ----------------------------------------------------------------------

def rat_CommGroup : CommGroup :=
{ G := ℚ, 
  op_comm := add_comm, 
  ..rat_Group }

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar el espacio de nombres Group 
-- ----------------------------------------------------------------------

namespace Group

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar G como una variable sobre grupos. 
-- ----------------------------------------------------------------------

variables {G : Group}

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar los grupos como instancias de tipos. 
-- ----------------------------------------------------------------------

instance : has_coe_to_sort Group := ⟨_, Group.G⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar que G tiene
--    + multiplicación: op (o *)
--    + neutro: id (o 1)
--    + inverso: inv (o ⁻¹) 
-- ----------------------------------------------------------------------

instance : has_mul G := ⟨G.op⟩
instance : has_one G := ⟨G.id⟩
instance : has_inv G := ⟨G.inv⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que G cumple los axiomas de grupo.
-- ----------------------------------------------------------------------

lemma op_assoc 
  (x y z : G) 
  : (x * y) * z = x * (y * z) := 
G.op_assoc' x y z

lemma id_op 
  (x : G) 
  : 1 * x = x := 
G.id_op' x

lemma op_left_inv 
  (x : G) 
  : x⁻¹ * x = 1 := 
  G.op_left_inv' x

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si G es un grupo y x es un elemento de G,
-- entonces 
--    x * x = x → x = 1
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {G : Group} 
  {x : G} 
  : x * x = x → x = 1 :=
begin
  intro hx, 
  rw ← id_op x,
  rw ← op_left_inv x,
  rw op_assoc,
  rw hx,
end

-- Prueba
-- ======

/-
G : Group,
x : ↥G
⊢ x * x = x → x = 1
  >> intro hx, 
hx : x * x = x
⊢ x = 1
  >> rw ← id_op x,
⊢ 1 * x = 1
  >> rw ← op_left_inv x,
⊢ (x⁻¹ * x) * x = x⁻¹ * x
  >> rw op_assoc,
⊢ x⁻¹ * (x * x) = x⁻¹ * x
  >> rw hx,
no goals
-/

-- 2ª demostración
-- ===============

lemma eq_id_of_op_eq_self 
  {G : Group} 
  {x : G} 
  : x * x = x → x = 1 :=
begin
  intro hx, 
  rw [← id_op x, ← op_left_inv x, op_assoc, hx]
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que x⁻¹ es el inverso de x por la derecha.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {G : Group} 
  (x : G) 
  : x * x⁻¹ = 1 :=
begin
  apply eq_id_of_op_eq_self,
  rw op_assoc x x⁻¹ (x * x⁻¹),
  rw ← op_assoc x⁻¹ x x⁻¹,
  rw op_left_inv,
  rw id_op,
end

-- Prueba
-- ======

/-
G : Group,
x : ↥G
⊢ x * x⁻¹ = 1
  >> apply eq_id_of_op_eq_self,
⊢ (x * x⁻¹) * (x * x⁻¹) = x * x⁻¹
  >> rw op_assoc x x⁻¹ (x * x⁻¹),
⊢ x * (x⁻¹ * (x * x⁻¹)) = x * x⁻¹
  >> rw ← op_assoc x⁻¹ x x⁻¹,
⊢ x * ((x⁻¹ * x) * x⁻¹) = x * x⁻¹
  >> rw op_left_inv,
⊢ x * (1 * x⁻¹) = x * x⁻¹
  >> rw id_op,
no goals
-/

-- 2ª demostración
-- ===============

lemma op_right_inv 
  {G : Group} 
  (x : G) 
  : x * x⁻¹ = 1 :=
begin
  apply eq_id_of_op_eq_self,
  rw [op_assoc x x⁻¹ (x * x⁻¹), ← op_assoc x⁻¹ x x⁻¹, op_left_inv, id_op]
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 1 es neutro por la derecha.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {G : Group} 
  (x : G) 
  : x * 1 = x :=
begin
  rw ← op_left_inv x, 
  rw ← op_assoc, 
  rw op_right_inv, 
  rw id_op,
end

-- Prueba
-- ======

/-
G : Group,
x : ↥G
⊢ x * 1 = x
  >> rw ← op_left_inv x, 
⊢ x * (x⁻¹ * x) = x
  >> rw ← op_assoc,
⊢ (x * x⁻¹) * x = x 
  >> rw op_right_inv, 
⊢ 1 * x = x
  >> rw id_op,
no goals
-/

-- 2ª demostración
-- ===============

lemma op_id 
  {G : Group} 
  (x : G) 
  : x * 1 = x :=
by rw [← op_left_inv x, ← op_assoc, op_right_inv, id_op]

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el producto cartesiano de dos grupos. 
-- ----------------------------------------------------------------------

def prod_Group (G₁ G₂ : Group) : Group :=
{ G := G₁ × G₂,
  op := λ x y, (x.1 * y.1, x.2 * y.2),
  op_assoc' := by { intros, ext; simp; rw [op_assoc] },
  id := (1, 1),
  id_op' := by { intros, ext; simp; rw [id_op] },
  inv := λ x, (x.1⁻¹, x.2⁻¹),
  op_left_inv' := by { intros, ext; simp; rw [op_left_inv] } }

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar el espacio de nombres Group 
-- ----------------------------------------------------------------------

end Group

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la estructura pointed_type cuyos campos son
-- + type que es un tipo y
-- + point que es un elemento de type.
-- ----------------------------------------------------------------------

structure pointed_type :=
(type : Type*)
(point : type)

-- ---------------------------------------------------------------------
-- Ejercicio. Empezar el espacio de nombre pointed_type. 
-- ----------------------------------------------------------------------

namespace pointed_type

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar A y B como variables sobre pointed_type 
-- ----------------------------------------------------------------------

variables {A B : pointed_type}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si A es un pointed_type entonces es un tipo.
-- ----------------------------------------------------------------------

instance : has_coe_to_sort pointed_type := ⟨_, pointed_type.type⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el poructo de pointed_type. 
-- ----------------------------------------------------------------------

@[simps point]
def prod (A B : pointed_type) : pointed_type :=
{ type := A × B,
  point := (A.point, B.point) }

-- Comentario: El atributo @[simps point] indica que se puede despelgar
-- la definición. 

-- ---------------------------------------------------------------------
-- Ejercicio. Terminar el espacio de nombres de pointed_type. 
-- ----------------------------------------------------------------------

end pointed_type

structure pointed_map (A B : pointed_type) :=
(to_fun : A → B)
(to_fun_point : to_fun A.point = B.point)

namespace pointed_map

infix ` →. `:25 := pointed_map

variables {A B C D : pointed_type}
variables {h : C →. D} {g : B →. C} {f f₁ f₂ : A →. B}

instance : has_coe_to_fun (A →. B) := ⟨λ _, A → B, pointed_map.to_fun⟩

@[simp] lemma coe_mk {f : A → B} {hf : f A.point = B.point} {x : A} :
  { pointed_map . to_fun := f, to_fun_point := hf } x = f x := rfl
@[simp] lemma coe_point : f A.point = B.point := f.to_fun_point

@[ext] protected lemma ext (hf₁₂ : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
begin
  cases f₁ with f₁ hf₁, cases f₂ with f₂ hf₂, congr, ext x, exact hf₁₂ x
end

/-! Below we show that pointed types form a category. -/

def comp (g : B →. C) (f : A →. B) : A →. C :=
{ to_fun := g ∘ f,
  to_fun_point := by simp }

def id : A →. A :=
{ to_fun := id,
  to_fun_point := by simp }

/-! You can use projection notation for any declaration declared in the same namespace as the
  structure. For example, `g.comp f` means `pointed_map.comp g f` -/
lemma comp_assoc : h.comp (g.comp f) = (h.comp g).comp f :=
by { ext x, refl }

lemma id_comp : f.comp id = f :=
by { ext x, refl }

lemma comp_id : id.comp f = f :=
by { ext x, refl }

/-! Below we show that `A.prod B` (that is, `pointed_type.prod A B`) is a product in the category of
  pointed types. -/

def fst : A.prod B →. A :=
{ to_fun := prod.fst,
  to_fun_point := rfl }

def snd : A.prod B →. B :=
{ to_fun := prod.snd,
  to_fun_point := rfl }

def pair (f : C →. A) (g : C →. B) : C →. A.prod B :=
{ to_fun := λ c, (f c, g c),
  to_fun_point := by simp }

lemma fst_pair (f : C →. A) (g : C →. B) : fst.comp (f.pair g) = f :=
by { ext, simp [pair, fst, comp] }

lemma snd_pair (f : C →. A) (g : C →. B) : snd.comp (f.pair g) = g :=
by { ext, simp [pair, snd, comp] }

lemma pair_unique (f : C →. A) (g : C →. B) (u : C →. A.prod B) (h1u : fst.comp u = f)
  (h2u : snd.comp u = g) : u = f.pair g :=
begin
  ext,
  { have : fst (u x) = f x, { rw [←h1u], simp [comp] }, simpa using this },
  { have : snd (u x) = g x, { rw [←h2u], simp [comp] }, simpa using this }
end


end pointed_map

/-! As an advanced exercise, you can show that the category of pointed type has coproducts.
  For this we need quotients, the basic interface is given with the declarations
  `quot r`: the quotient of the equivalence relation generated by relation `r` on `A`
  `quot.mk r : A → quot r`,
  `quot.sound`
  `quot.lift` (see below)
  -/

#print quot
#print quot.mk
#print quot.sound
#print quot.lift

open sum

/-! We want to define the coproduct of pointed types `A` and `B` as the coproduct `A ⊕ B` of the
  underlying type, identifying the two basepoints.

  First define a relation that *only* relates `inl A.point ~ inr B.point`.
-/
def coprod_rel (A B : pointed_type) : (A ⊕ B) → (A ⊕ B) → Prop :=
λ x y, x = inl A.point ∧ y = inr B.point

namespace pointed_type

-- @[simps point]
-- omit
@[simps point]
-- omit
def coprod (A B : pointed_type) : pointed_type :=
{ type := quot (coprod_rel A B),
  point := quot.mk _ (inl A.point) }
end pointed_type

namespace pointed_map

variables {A B C D : pointed_type}

def inl : A →. A.coprod B :=
{ to_fun := quot.mk _ ∘ sum.inl,
  to_fun_point := rfl }

def inr : B →. A.coprod B :=
{ to_fun := quot.mk _ ∘ sum.inr,
  to_fun_point := by { refine (quot.sound _).symm, exact ⟨rfl, rfl⟩ } }

def elim (f : A →. C) (g : B →. C) : A.coprod B →. C :=
{ to_fun := quot.lift (sum.elim f g) (by { rintro _ _ ⟨rfl, rfl⟩, simp }),
  to_fun_point := by simp }

lemma elim_comp_inl (f : A →. C) (g : B →. C) : (f.elim g).comp inl = f :=
by { ext, simp [elim, inl, comp] }

lemma elim_comp_inr (f : A →. C) (g : B →. C) : (f.elim g).comp inr = g :=
by { ext, simp [elim, inr, comp] }

lemma elim_unique (f : A →. C) (g : B →. C) (u : A.coprod B →. C) (h1u : u.comp inl = f)
  (h2u : u.comp inr = g) : u = f.elim g :=
begin
  ext (x|y),
  { have : u (inl x) = f x, { rw [←h1u], simp [comp] }, simpa [elim, inl] using this },
  { have : u (inr y) = g y, { rw [←h2u], simp [comp] }, simpa [elim, inl] using this }
end

end pointed_map

-- Comprobación de la corrección sintáctica
#lint

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en la teoría structures.lean de Floris van Doorn que se
-- encuentra en https://bit.ly/39s7AwF y se comenta en los vídeos
-- "Structures and Classes" que se encuentra en
-- https://youtu.be/xYenPIeX6MY 
