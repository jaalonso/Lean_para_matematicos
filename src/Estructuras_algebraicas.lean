-- Estructuras algebraicas
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Importar las librerías
-- + data.rat.basic (que contiene los números racionales) y
-- + tactic (que contiene las tácticas)
-- ----------------------------------------------------------------------

import data.rat.basic
import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar el espacio de nombres lftcm (para evitar
-- conflictos de nombres) de forma que cuando se defina `group` su
-- nombre será `lftcm.group`.
-- ----------------------------------------------------------------------

namespace lftcm

-- Comentario sobre notación de clases de tipos:
-- + Para definir un término de tipo `has_mul G` hay que definir una
--   función `has_mul.mul : G → G → G`.
-- + La notación `g * h` representa `has_mul.mul g h`.
-- + `has_mul` es una clase.
-- + Al escribir `[has_mul G]` se dispone de una multiplicación llamada
--   `*` que verifica los axiomas de grupo.
-- + Al escribir `[has_one G]` se dispone de un elemento neutro
--   `has_one.one : G` que se representa por `1`.
-- + Al escribir `[has_inv G]` se dispone de una operación
--   `has_inv.inv : G → G` de forma que `inv g` es el inverso de `g` y
--    se representa por `g⁻¹`

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los grupos
-- ----------------------------------------------------------------------

class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar el espacio de nombres group.
-- ----------------------------------------------------------------------

namespace group

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar G como una variable sobre grupos
-- ----------------------------------------------------------------------

variables {G : Type} [group G]

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar a, b y c elementos de G.
-- ----------------------------------------------------------------------

variables  (a b c : G)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    a * b = a * c
-- entonces
--    b = c
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

lemma mul_left_cancel
  (Habac : a * b = a * c)
  : b = c :=
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- 2ª demostración
-- ===============

lemma mul_left_cancel2
  (Habac : a * b = a * c)
  : b = c :=
begin
  rw ←one_mul b,
  rw ←mul_left_inv a,
  rw mul_assoc,
  rw Habac,
  rw ←mul_assoc,
  rw mul_left_inv,
  rw one_mul,
end

-- Prueba
-- ======

/-
G : Type,
_inst_1 : group G,
a b c : G,
Habac : a * b = a * c
⊢ b = c
  >> rw ←one_mul b,
⊢ 1 * b = c
  >> rw ←mul_left_inv a,
⊢ (a⁻¹ * a) * b = c
  >> rw mul_assoc,
⊢ a⁻¹ * (a * b) = c
  >> rw Habac,
⊢ a⁻¹ * (a * c) = c
  >> rw ←mul_assoc,
⊢ (a⁻¹ * a) * c = c
  >> rw mul_left_inv,
⊢ 1 * c = c
  >> rw one_mul,
no goals
-/

-- 3ª demostración
-- ===============

lemma mul_left_cancel3
  (Habac : a * b = a * c)
  : b = c :=
begin
  rw [←one_mul b, ←mul_left_inv a, mul_assoc, Habac, ←mul_assoc,
      mul_left_inv, one_mul],
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    x = a⁻¹ * y
-- entonces
--    a * x = y
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

lemma mul_eq_of_eq_inv_mul
  {a x y : G}
  (h : x = a⁻¹ * y)
  : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rw ←mul_assoc,
  rw mul_left_inv,
  rw one_mul,
  exact h,
end

-- Prueba
-- ======

/-
G : Type,
_inst_1 : group G,
a x y : G,
h : x = a⁻¹ * y
⊢ a * x = y
  >> apply mul_left_cancel a⁻¹,
⊢ a⁻¹ * (a * x) = a⁻¹ * y
  >> rw ←mul_assoc,
⊢ (a⁻¹ * a) * x = a⁻¹ * y
  >> rw mul_left_inv,
⊢ 1 * x = a⁻¹ * y
  >> rw one_mul,
⊢ x = a⁻¹ * y
  >> exact h,
no goals
-/

-- 2ª demostración
-- ===============

lemma mul_eq_of_eq_inv_mul2
  {a x y : G}
  (h : x = a⁻¹ * y)
  : a * x = y :=
mul_left_cancel a⁻¹ _ _ $ by rwa [←mul_assoc, mul_left_inv, one_mul]

-- Comentario: La táctica `rwa hs` rescribe la conclusión con las reglas
-- de hs y al final aplica assumption.

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar los axiomas y one_mul mul_left_inv como reglas de
-- simplificación.
-- ----------------------------------------------------------------------

attribute [simp] one_mul mul_left_inv

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar, y declarar como regla de simplificación, que el
-- 1 es elemento neutro por la derecha.
-- ----------------------------------------------------------------------

-- 2ª demostración
-- ===============

example
  (a : G)
  : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  apply eq.symm,
  exact mul_left_inv a,
end

-- Prueba
-- ======

/-
G : Type,
_inst_1 : group G,
a : G
⊢ a * 1 = a
  >> apply mul_eq_of_eq_inv_mul,
⊢ 1 = a⁻¹ * a
  >> apply eq.symm,
⊢ a⁻¹ * a = 1
  >> exact mul_left_inv a,
no goals
-/

-- 2ª demostración
-- ===============

example
  (a : G)
  : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  simp,
end

-- Prueba
-- ======

/-
G : Type,
_inst_1 : group G,
a : G
⊢ a * 1 = a
  >> apply mul_eq_of_eq_inv_mul
⊢ 1 = a⁻¹ * a
  >> simp,
no goals
-/

-- Comentario: El simplificador demuestra que `1 = a⁻¹ * a` porque se ha
-- declarado mul_left_inv como regla de simplificación

-- 3ª demostración
-- ===============

@[simp]
theorem mul_one
  (a : G)
  : a * 1 = a :=
mul_eq_of_eq_inv_mul $ by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar, y declarar como regla de simplificación, que
--    a * a⁻¹ = 1
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (a : G)
  : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

-- Prueba
-- ======

/-
G : Type,
_inst_1 : group G,
a : G
⊢ a * a⁻¹ = 1
  >> apply mul_eq_of_eq_inv_mul,
⊢ a⁻¹ = a⁻¹ * 1
  >> rw mul_one,
no goals
-/

-- 2ª demostración
-- ===============

@[simp]
theorem mul_right_inv
  (a : G)
  : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  simp
end

-- 3ª demostración
-- ===============

example
  (a : G)
  : a * a⁻¹ = 1 :=
mul_eq_of_eq_inv_mul $ by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el inverso de 1 es 1.
-- ----------------------------------------------------------------------

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a⁻¹⁻¹ = a
-- ----------------------------------------------------------------------

@[simp] lemma inv_inv (a : G) : a⁻¹⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar la propiedad asociativa como regla de
-- simplificación.
-- ----------------------------------------------------------------------

attribute [simp] mul_assoc

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a⁻¹ * (a * b) = b
-- ----------------------------------------------------------------------

@[simp] lemma inv_mul_cancel_left
  (a b : G)
  : a⁻¹ * (a * b) = b :=
begin
  rw ←mul_assoc,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * (a⁻¹ * b) = b
-- ----------------------------------------------------------------------

@[simp] lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
begin
  rw ←mul_assoc,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ----------------------------------------------------------------------

@[simp] lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  simp,
end

-- Prueba
-- ======

/-
G : Type,
_inst_1 : group G,
a b : G
⊢ (a * b)⁻¹ = b⁻¹ * a⁻¹
  apply mul_left_cancel (a * b),
⊢ (a * b) * (a * b)⁻¹ = (a * b) * (b⁻¹ * a⁻¹)
  rw mul_right_inv,
⊢ 1 = a * b * (b⁻¹ * a⁻¹)
  simp,
no goals
-/

-- Comentario: Con las reglas de simplificación de grupo que se han
-- añadido se tiene un sistema de reescritura normalizador confluente;
-- es decir, el simplificador transforma cualquier expresión de grupo en
-- su forma canónica.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b⁻¹ * b * b * 1 * 1⁻¹)⁻¹
--    = (c⁻¹⁻¹ * d * d⁻¹ * 1⁻¹⁻¹ * c⁻¹⁻¹⁻¹)⁻¹⁻¹
-- ----------------------------------------------------------------------

example
  (a b c d : G)
  : ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b⁻¹ * b * b * 1 * 1⁻¹)⁻¹
    = (c⁻¹⁻¹ * d * d⁻¹ * 1⁻¹⁻¹ * c⁻¹⁻¹⁻¹)⁻¹⁻¹ :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el producto de dos grupos.
-- ----------------------------------------------------------------------

instance (G : Type) [group G] (H : Type) [group H] : group (G × H) :=
{ mul := λ k l, (k.1*l.1, k.2*l.2),
  one := (1,1),
  inv := λ k, (k.1⁻¹, k.2⁻¹),
  mul_assoc :=
  begin
    rintros ⟨a1,a2⟩ ⟨b1,b2⟩ ⟨c1,c2⟩,
    ext;
    simp,
  end,
  one_mul :=
  begin
    rintros ⟨a1,a2⟩,
    ext;
    simp,
  end,
  mul_left_inv :=
  begin
    rintros ⟨a1,a2⟩,
    ext;
    simp
  end }

-- Prueba de mul_assoc
-- ===================

/-
G : Type,
_inst_2 : group G,
H : Type,
_inst_3 : group H
⊢ ∀ (a b c : G × H), a * b * c = a * (b * c)
    >> rintros ⟨a1,a2⟩ ⟨b1,b2⟩ ⟨c1,c2⟩,
a1 : G,
a2 : H,
b1 : G,
b2 : H,
c1 : G,
c2 : H
⊢ (a1, a2) * (b1, b2) * (c1, c2) = (a1, a2) * ((b1, b2) * (c1, c2))
    >> ext;
⊢ ((a1, a2) * (b1, b2) * (c1, c2)).fst = ((a1, a2) * ((b1, b2) * (c1,c2))).fst
⊢ ((a1, a2) * (b1, b2) * (c1, c2)).snd = ((a1, a2) * ((b1, b2) * (c1, c2))).snd
    >> simp,
no goals
-/

-- Prueba de one_mul
-- =================

/-
G : Type,
_inst_2 : group G,
H : Type,
_inst_3 : group H
⊢ ∀ (a : G × H), 1 * a = a
  >> rintros ⟨a1,a2⟩,
a1 : G,
a2 : H
⊢ 1 * (a1, a2) = (a1, a2)
  >> ext;
⊢ (1 * (a1, a2)).fst = (a1, a2).fst
⊢ (1 * (a1, a2)).snd = (a1, a2).snd
  >> simp,
no goals
-/

-- Prueba de mul_left_inv
-- ======================

/-
G : Type,
_inst_2 : group G,
H : Type,
_inst_3 : group H
⊢ ∀ (a : G × H), a⁻¹ * a = 1
  >> rintros ⟨a1,a2⟩,
a1 : G,
a2 : H
⊢ (a1, a2)⁻¹ * (a1, a2) = 1
  >> ext;
⊢ ((a1, a2)⁻¹ * (a1, a2)).fst = 1.fst
⊢ ((a1, a2)⁻¹ * (a1, a2)).snd = 1.snd
  >> simp
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si G, H y K son grupos, entonces G × H × K
-- también lo es.
-- ----------------------------------------------------------------------

example (G H K : Type) [group G] [group H] [group K] : group (G × H × K) :=
by apply_instance

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar el espacio de nombres group.
-- ----------------------------------------------------------------------

end group

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el tipo mu2 con dos elementos p1 y m1 (que
-- representarán a +1 y -1).
-- ----------------------------------------------------------------------

inductive mu2
| p1 : mu2
| m1 : mu2

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el espacio de nombres mu2.
-- ----------------------------------------------------------------------

namespace mu2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la igualdad en mu2 es decidible.
-- ----------------------------------------------------------------------

attribute [derive decidable_eq] mu2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que mu2 es un tipo finito.
-- ----------------------------------------------------------------------

instance : fintype mu2 :=
⟨⟨[mu2.p1, mu2.m1], by simp⟩,
 λ x, by cases x; simp⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    mul : mu2 → mu2 → mu2
-- tal que (mul x y) es el producto de x por y.
-- ----------------------------------------------------------------------

def mul : mu2 → mu2 → mu2
| p1 p1 := p1
| p1 m1 := m1
| m1 p1 := m1
| m1 m1 := p1

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar mu2 una instancia de has_mul con la operación mul.
-- ----------------------------------------------------------------------

instance : has_mul mu2 := ⟨mul⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Definir one como p1.
-- ----------------------------------------------------------------------

def one : mu2 := p1

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar mu2 una instancia de has_one con elemento neutro
-- one.
-- ----------------------------------------------------------------------

instance : has_one mu2 := ⟨one⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    inv : mu2 → mu2
-- como la identidad.
-- ----------------------------------------------------------------------

def inv : mu2 → mu2 := id

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar mu2 una instancia de has_inv con inv.
-- ----------------------------------------------------------------------

instance : has_inv mu2 := ⟨inv⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    p1 * m1 * m1 = p1⁻¹ * p1
-- ----------------------------------------------------------------------

example : p1 * m1 * m1 = p1⁻¹ * p1 := rfl

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar mu2 una instancia de group.
-- ----------------------------------------------------------------------

instance : group mu2 :=
begin
  refine_struct { mul := mul, one := one, inv := inv },
  all_goals {exact dec_trivial}
end

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar el espacio de nombre mu2.
-- ----------------------------------------------------------------------

end mu2

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los monoides (ver
-- https://bit.ly/30NfvAZ )
-- ----------------------------------------------------------------------

class monoid (M : Type) extends has_mul M, has_one M :=
(mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c))
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los grupos conmutativos con sumas.
-- ----------------------------------------------------------------------

class add_comm_group (A : Type) extends has_add A, has_zero A, has_neg A :=
(add_assoc : ∀ (a b c : A), a + b + c = a + (b + c))
(zero_add : ∀ (a : A), 0 + a = a)
(add_left_neg : ∀ (a : A), -a + a = 0)
(add_comm : ∀ a b : A, a + b = b + a)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la resta en los grupos conmutativos con sumas.
-- ----------------------------------------------------------------------

instance (A : Type) [add_comm_group A] : has_sub A :=
⟨λ a b, a + -b⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los anillos.
-- ----------------------------------------------------------------------

class ring (R : Type) extends monoid R, add_comm_group R :=
(mul_add : ∀ (a b c : R), a * (b + c) = a * b + a * c)
(add_mul : ∀ (a b c : R), (a + b) * c = a * c + b * c)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los anillos conmutativos.
-- ----------------------------------------------------------------------

class comm_ring (R : Type) extends ring R :=
(mul_comm : ∀ a b : R, a * b = b * a)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los tipos con una multiplicación por
-- un escalar.
-- ----------------------------------------------------------------------

class has_scalar (R : Type) (M : Type) :=
(smul : R → M → M)

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar • como la multiplicación por un escalar.
-- ----------------------------------------------------------------------

infixr ` • `:73 := has_scalar.smul

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los módulos (ver
-- https://bit.ly/3hBPZW7 )
-- ----------------------------------------------------------------------

class module (R : Type) [ring R] (M : Type) [add_comm_group M]
extends has_scalar R M :=
(smul_add : ∀(r : R) (x y : M), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x)
(one_smul : ∀ x : M, (1 : R) • x = x)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los cuerpos.
-- ----------------------------------------------------------------------

class field (K : Type) extends comm_ring K, has_inv K :=
(zero_ne_one : (0 : K) ≠ 1)
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los espacios vectoriales.
-- ----------------------------------------------------------------------

def vector_space (K : Type) [field K] (V : Type) [add_comm_group V] :=
module K V

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los racionales son un cuerpo.
-- ----------------------------------------------------------------------

instance : field ℚ :=
{ mul := (*),
  one := 1,
  mul_assoc := rat.mul_assoc,
  one_mul := rat.one_mul,
  mul_one := rat.mul_one,
  add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_assoc := rat.add_assoc,
  zero_add := rat.zero_add,
  add_left_neg := rat.add_left_neg,
  add_comm := rat.add_comm,
  mul_add := rat.mul_add,
  add_mul := rat.add_mul,
  mul_comm := rat.mul_comm,
  inv := has_inv.inv,
  zero_ne_one := rat.zero_ne_one,
  mul_inv_cancel := rat.mul_inv_cancel,
  inv_zero := inv_zero
  }

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar A como un grupo conmutativo con suma.
-- ----------------------------------------------------------------------

variables {A : Type} [add_comm_group A]

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar a, b y c como variables sobre elementos de A.
-- ----------------------------------------------------------------------

variables (a b c : A)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    a + b = a + c
-- entonces
--    b = c
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (Habac : a + b = a + c)
  : b = c :=
calc b = 0 + b        : (add_comm_group.zero_add b).symm
   ... = (-a + a) + b : congr_arg (+ b) (add_comm_group.add_left_neg a).symm
   ... = -a + (a + b) : add_comm_group.add_assoc (-a) a b
   ... = -a + (a + c) : congr_arg ((+) (-a)) Habac
   ... = (-a + a) + c : (add_comm_group.add_assoc (-a) a c).symm
   ... = 0 + c        : congr_arg (+ c) (add_comm_group.add_left_neg a)
   ... = c            : add_comm_group.zero_add c

-- 2ª demostración
-- ===============

lemma add_comm_group.add_left_cancel
  (Habac : a + b = a + c)
  : b = c :=
begin
  rw ←add_comm_group.zero_add b,
  rw ←add_comm_group.add_left_neg a,
  rw add_comm_group.add_assoc,
  rw Habac,
  rw ←add_comm_group.add_assoc,
  rw add_comm_group.add_left_neg,
  rw add_comm_group.zero_add,
end

-- Prueba
-- ======

/-
A : Type,
_inst_1 : add_comm_group A,
a b c : A,
Habac : a + b = a + c
⊢ b = c
  >> rw ←add_comm_group.zero_add b,
⊢ 0 + b = c
  >> rw ←add_comm_group.add_left_neg a,
⊢ (-a + a) + b = c
  >> rw add_comm_group.add_assoc,
⊢ -a + (a + b) = c
  >> rw Habac,
⊢ -a + (a + c) = c
  >> rw ←add_comm_group.add_assoc,
⊢ (-a + a) + c = c
  >> rw add_comm_group.add_left_neg,
⊢ 0 + c = c
  >> rw add_comm_group.zero_add,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a + -a = 0
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example :
  a + -a = 0 :=
calc a + -a
     = -a + a : add_comm_group.add_comm a (-a)
 ... = 0      : add_comm_group.add_left_neg a

-- 2ª demostración
-- ===============

example :
  a + -a = 0 :=
calc a + -a
     = -a + a : by rw add_comm_group.add_comm
 ... = 0      : by rw add_comm_group.add_left_neg

-- 3ª demostración
-- ===============

lemma add_comm_group.add_right_neg :
  a + -a = 0 :=
begin
  rw add_comm_group.add_comm,
  rw add_comm_group.add_left_neg,
end

-- Prueba
-- ======

/-
A : Type,
_inst_1 : add_comm_group A,
a : A
⊢ a + -a = 0
  >> rw add_comm_group.add_comm,
⊢ -a + a = 0
  >> rw add_comm_group.add_left_neg,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a - b = a + -b
-- ----------------------------------------------------------------------

lemma add_comm_group.sub_eq_add_neg :
  a - b = a + -b :=
rfl

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a - a = 0
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example :
  a - a = 0 :=
calc a - a
     = a + (-a) : add_comm_group.sub_eq_add_neg a a
 ... = -a + a   : add_comm_group.add_comm a (-a)
 ... = 0        : add_comm_group.add_left_neg a

-- 2ª demostración
-- ===============

example :
  a - a = 0 :=
calc a - a
     = a + (-a) : by rw add_comm_group.sub_eq_add_neg
 ... = -a + a   : by rw add_comm_group.add_comm
 ... = 0        : by rw add_comm_group.add_left_neg

-- 3ª demostración
-- ===============

example :
  a - a = 0 :=
by rw [add_comm_group.sub_eq_add_neg,
       add_comm_group.add_comm,
       add_comm_group.add_left_neg]

-- 4ª demostración
-- ===============

lemma add_comm_group.sub_self :
  a - a = 0 :=
begin
  rw add_comm_group.sub_eq_add_neg,
  rw add_comm_group.add_comm,
  rw add_comm_group.add_left_neg,
end

-- Prueba
-- ======

/-
A : Type,
_inst_1 : add_comm_group A,
a : A
⊢ a - a = 0
  >> rw add_comm_group.sub_eq_add_neg,
⊢ a + -a = 0
  >> rw add_comm_group.add_comm,
⊢ -a + a = 0
  >> rw add_comm_group.add_left_neg,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    a + b = 0
-- entonces
--    -a = b
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc -a
     = 0 + (-a)       : (add_comm_group.zero_add (-a)).symm
 ... = (a + b) + (-a) : congr_arg (+ (-a)) h.symm
 ... = (b + a) + (-a) : congr_arg (+ (-a)) (add_comm_group.add_comm a b)
 ... = b + (a + (-a)) : add_comm_group.add_assoc b a (-a)
 ... = b + 0          : congr_arg ((+) b) (add_comm_group.add_right_neg a)
 ... = 0 + b          : add_comm_group.add_comm b 0
 ... = b              : add_comm_group.zero_add b

-- 2ª demostración
-- ===============

example
  (h : a + b = 0)
  : -a = b :=
calc -a
     = 0 + (-a)       : by rw add_comm_group.zero_add
 ... = (a + b) + (-a) : by rw h.symm
 ... = (b + a) + (-a) : congr_arg (+ (-a)) (add_comm_group.add_comm a b)
 ... = b + (a + (-a)) : by rw add_comm_group.add_assoc
 ... = b + 0          : congr_arg ((+) b) (add_comm_group.add_right_neg a)
 ... = 0 + b          : by rw add_comm_group.add_comm
 ... = b              : by rw add_comm_group.zero_add

-- 3ª demostración
-- ===============

lemma add_comm_group.neg_eq_of_add_eq_zero
  (h : a + b = 0)
  : -a = b :=
begin
  apply add_comm_group.add_left_cancel a,
  rw h,
  rw add_comm_group.add_right_neg,
end

-- Prueba
-- ======

/-
A : Type,
_inst_1 : add_comm_group A,
a b : A,
h : a + b = 0
⊢ -a = b
  >> apply add_comm_group.add_left_cancel a,
⊢ a + -a = a + b
  >> rw h,
⊢ a + -a = 0
  >> rw add_comm_group.add_right_neg,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a + 0 = a
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : a + 0 = a :=
calc a + 0
     = 0 + a : add_comm_group.add_comm a 0
 ... = a     : add_comm_group.zero_add a

-- 2ª demostración
-- ===============

example : a + 0 = a :=
calc a + 0
     = 0 + a : by rw add_comm_group.add_comm
 ... = a     : by rw add_comm_group.zero_add

-- 3ª demostración
-- ===============

example : a + 0 = a :=
begin
  rw add_comm_group.add_comm,
  rw add_comm_group.zero_add,
end

-- 3ª demostración
-- ===============

lemma add_comm_group.add_zero : a + 0 = a :=
by rw [add_comm_group.add_comm,
       add_comm_group.zero_add]

-- Prueba
-- ======

/-
A : Type,
_inst_1 : add_comm_group A,
a : A
⊢ a + 0 = a
  >> rw add_comm_group.add_comm,
⊢ 0 + a = a
  >> rw add_comm_group.zero_add,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar R como una variable implícita sobre los anillos.
-- ----------------------------------------------------------------------

variables {R : Type} [ring R]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que, para todo r de R,
--    r * 0 = 0
-- ----------------------------------------------------------------------

lemma ring.mul_zero
  (r : R)
  : r * 0 = 0 :=
begin
  apply add_comm_group.add_left_cancel (r * 0),
  rw ←ring.mul_add,
  rw add_comm_group.add_zero,
  rw add_comm_group.add_zero,
end

-- Prueba
-- ======

/-
R : Type,
_inst_2 : ring R,
r : R
⊢ r * 0 = 0
  >> apply add_comm_group.add_left_cancel (r * 0),
⊢ r * 0 + r * 0 = r * 0 + 0
  >> rw ←ring.mul_add,
⊢ r * (0 + 0) = r * 0 + 0
  >> rw add_comm_group.add_zero,
⊢ r * 0 = r * 0 + 0
  >> rw add_comm_group.add_zero,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que, para todo a y b de R,
--    a * -b = -(a * b)
-- ----------------------------------------------------------------------

lemma ring.mul_neg
  (a b : R) :
  a * -b = -(a * b) :=
begin
  symmetry,
  apply add_comm_group.neg_eq_of_add_eq_zero,
  rw ←ring.mul_add,
  rw add_comm_group.add_right_neg,
  rw ring.mul_zero,
end

-- Prueba
-- ======

/-
R : Type,
_inst_2 : ring R,
a b : R
⊢ a * -b = -(a * b)
  >> symmetry,
⊢ -(a * b) = a * -b
  >> apply add_comm_group.neg_eq_of_add_eq_zero,
⊢ a * b + a * -b = 0
  >> rw ←ring.mul_add,
⊢ a * (b + -b) = 0
  >> rw add_comm_group.add_right_neg,
⊢ a * 0 = 0
  >> rw ring.mul_zero,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Sea R un anillo conmutativo. Demostrar que, para todo r, a
-- y b de R,
--    r * (a - b) = r * a - r * b
-- ----------------------------------------------------------------------

lemma ring.mul_sub
  (R : Type)
  [comm_ring R]
  (r a b : R) :
  r * (a - b) = r * a - r * b :=
begin
  rw add_comm_group.sub_eq_add_neg,
  rw ring.mul_add,
  rw ring.mul_neg,
  refl,
end

-- Prueba
-- ======

/-
R : Type,
_inst_3 : comm_ring R,
r a b : R
⊢ r * (a - b) = r * a - r * b
  >> rw add_comm_group.sub_eq_add_neg,
⊢ r * (a + -b) = r * a - r * b
  >> rw ring.mul_add,
⊢ r * a + r * -b = r * a - r * b
  >> rw ring.mul_neg,
⊢ r * a + -(r * b) = r * a - r * b
  >> refl,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Sea R un anillo conmutativo. Demostrar que, para todo r, a
-- y b de R,
--    (a - b) * r = a * r - b * r
-- ----------------------------------------------------------------------

lemma comm_ring.sub_mul
  (R : Type)
  [comm_ring R]
  (r a b : R)
  : (a - b) * r = a * r - b * r :=
begin
  rw comm_ring.mul_comm (a - b),
  rw comm_ring.mul_comm a,
  rw comm_ring.mul_comm b,
  apply ring.mul_sub,
end

-- Prueba
-- ======

/-
R : Type,
_inst_3 : comm_ring R,
r a b : R
⊢ (a - b) * r = a * r - b * r
  >> rw comm_ring.mul_comm (a - b),
⊢ r * (a - b) = a * r - b * r
  >> rw comm_ring.mul_comm a,
⊢ r * (a - b) = r * a - b * r
  >> rw comm_ring.mul_comm b,
⊢ r * (a - b) = r * a - r * b
  >> apply ring.mul_sub,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar el espacio de nombres lftcm.
-- ----------------------------------------------------------------------

end lftcm

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en la teoría algebraic_hierarchy.lean de Kevin Buzzard que se
-- encuentra en https://bit.ly/32S8vFr y se comenta en el vídeo
-- "Building an algebraic hierarchy" que se encuentra en
-- https://youtu.be/ATlAQPAtiTY
