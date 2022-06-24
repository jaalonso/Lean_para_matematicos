-- Reconstrucción de espacios topológicos en Lean
-- =====================================================================

-- =====================================================================
-- § Introducción                                                     --
-- =====================================================================

-- Mathlib tiene una gran biblioteca de resultados sobre espacios
-- topológicos, incluyendo varias construcciones, axiomas de separación,
-- el teorema de Tychonoff, gavillas, la compactificación de Stone-Čech,
-- Heine-Cantor, por nombrar sólo algunos.
--
-- Véase https://leanprover-community.github.io/theories/topology.html
-- que para un (subconjunto) de lo que hay en la biblioteca.
--
-- Pero hoy ignoraremos todo eso y construiremos nuestra propia versión
-- de los espacios topológicos desde cero.
--
-- Primero un poco de preparación, vamos a hacer definiciones que
-- involucran a los números reales, cuya teoría no es computable, y
-- usaremos conjuntos

-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar las librerías de tácricas, conjuntos finitos y la
-- de los números reales.
-- ---------------------------------------------------------------------

import tactic
import data.set.finite
import data.real.basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar la teoría como no computable.
-- ---------------------------------------------------------------------

noncomputable theory

-- ---------------------------------------------------------------------
-- Ejercicio 3. Abrir el espacio de nombre de los conjuntos (`set`).
-- ---------------------------------------------------------------------

open set

-- =====================================================================
-- § ¿Qué es un espacio topológico?                                   --
-- =====================================================================

-- Un espacio topológico, según la Wikipedia, es un par ordenado (X, τ),
-- donde X es un conjunto y τ es una colección de subconjuntos de X, que
-- satisface los siguientes axiomas:
-- + A1. El conjunto vacío pertenece a τ.
-- + A2. El propio X pertenece a τ.
-- + A3. Cualquier unión arbitraria (finita o infinita) de miembros de τ
--   sigue perteneciendo a τ.
-- + A4, La intersección de cualquier número finito de miembros de τ sigue
--   perteneciendo a τ.

-- ---------------------------------------------------------------------
-- Ejercicio 4. Definir la clase de los espacios topológios
-- correspondiente a la definición de la Wikipedia.
-- ---------------------------------------------------------------------

class topological_space_wiki :=
  (X : Type)                                    -- El tipo baśico
  (τ : set (set X))                             -- Los abiertos
  (empty_mem : ∅ ∈ τ)                           -- A1
  (univ_mem : univ ∈ τ)                         -- A2
  (union : ∀ B ⊆ τ, ⋃₀ B ∈ τ)                   -- A3
  (inter : ∀ (B ⊆ τ) (h : finite B), ⋂₀ B ∈ τ)  -- A4

-- ---------------------------------------------------------------------
-- Ejercicio 5. Definir la clase de los espacios topológicos usando el
-- predicado `is_open : set X → Prop` en lugar del conjunto de los
-- abiertos y usando sólo la intersección binaria de abiertos.
-- ---------------------------------------------------------------------

@[ext]
class topological_space (X : Type) :=
  (is_open : set X → Prop)
  -- (empty_mem : is_open ∅) -- Se demostrará en el ejercicio 8
  (univ_mem : is_open univ)
  (union : ∀ (B : set (set X)) (h : ∀ b ∈ B, is_open b), is_open (⋃₀ B))
  (inter : ∀ (A B : set X) (hA : is_open A) (hB : is_open B), is_open (A ∩ B))

-- --------
-------------------------------------------------------------
-- Ejercicio 6. Abrir el espacio de nombre de los espacios topológicos
-- (`topological_space`).
-- ---------------------------------------------------------------------

namespace topological_space

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que la intersección de tres abiertos es un
-- conjunto abierto.
-- ---------------------------------------------------------------------

example
  (X : Type)
  [topological_space X]
  (U V W : set X)
  (hU : is_open U)
  (hV : is_open V)
  (hW : is_open W)
  : is_open (U ∩ V ∩ W) :=
begin
  apply inter _ _ _ hW,
  exact inter _ _ hU hV,
end

-- ---------------------------------------------------------------------
-- Ejercicio 8. Uno de los axiomas de un espacio topológico que tenemos es
-- no necesario, se deduce de los otros. Si lo eliminamos tendremos
-- menos trabajo que hacer cada vez que queramos crear un nuevo espacio
-- topológico así que:
--
-- 1. Identifica y elimina el axioma innecesario, asegúrate de
--    eliminarlo en todo el archivo.
-- 2. Volver a añadir el axioma como un lema con el mismo nombre y
--    demostrarlo en base a los otros, para que la interfaz sea la
--    misma.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (X : Type)
  [topological_space X]
  : is_open (∅ : set X) :=
begin
  have h1: (∅ : set X) = ⋃₀(∅ : set (set X)) := sUnion_empty.symm,
  rw h1,
  apply union,
  simp,
end

-- 2ª demostración
lemma empty_mem
  (X : Type)
  [topological_space X]
  : is_open (∅ : set X) :=
begin
  convert union (∅ : set (set X)) _ ;
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio 9. Definir la topología discreta en la que todos los
-- subconjuntos son abiertos.
-- ---------------------------------------------------------------------

def discrete (X : Type) : topological_space X :=
{ is_open  := λ U, true,
  univ_mem := trivial,
  union    := begin intros B h, trivial, end,
  inter    := begin intros A hA B hB, trivial, end }

-- ---------------------------------------------------------------------
-- Ejercicio 10. Los conjuntos costructibles de un espacio topológico
-- son los obtenidos mediante las siguientes reglas:
-- + La intersección de un conjunto abierto y otro cerrado es
--   construible.
-- + La unión de cualquier par de conjuntos construibles es
--   construible.
-- ---------------------------------------------------------------------

inductive is_constructible {X : Type} (T : topological_space X) : set X → Prop
| locally_closed :
    ∀ (A B : set X), is_open A → is_open B → is_constructible (A ∩ Bᶜ)
| union :
    ∀ A B, is_constructible A → is_constructible B → is_constructible (A ∪ B)

-- ---------------------------------------------------------------------
-- Ejercicio 11. Demostrar que el vacío es construible.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  {X : Type}
  (T : topological_space X)
  : is_constructible T ∅ :=
begin
  have h1 : univ ∩ univᶜ = (∅ : set X),
    { calc univ ∩ univᶜ
           = univ ∩ ∅   : congr_arg ((∩) univ) compl_univ
       ... = ∅          : inter_empty univ, },
  rw ←h1,
  apply is_constructible.locally_closed,
  exact univ_mem,
  exact univ_mem,
end

-- 2ª demostración
example
  {X : Type}
  (T : topological_space X)
  : is_constructible T ∅ :=
begin
  have h1 : univ ∩ univᶜ = (∅ : set X),
    { simp, },
  rw ←h1,
  exact is_constructible.locally_closed univ univ univ_mem univ_mem,
end

-- 3ª demostración
example
  {X : Type}
  (T : topological_space X)
  : is_constructible T ∅ :=
begin
  have := is_constructible.locally_closed univ univ univ_mem univ_mem,
  simpa,
end

-- 4ª demostración
example
  {X : Type}
  (T : topological_space X)
  : is_constructible T ∅ :=
begin
  convert is_constructible.locally_closed univ univ univ_mem univ_mem,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio 12. Para cada conjunto de conjuntos de X, definir los
-- abiertos generados por X mediante las siguientes reglas:
-- + Los elementos de g son abiertos.
-- + El universal es abierto.
-- + La intersección de dos abiertos es abierto.
-- + La unión de un conjunto de abiertos es abierto.
-- ---------------------------------------------------------------------

inductive generated_open (X : Type) (g : set (set X)) : set X → Prop
| basic  : ∀ s ∈ g, generated_open s
| univ   : generated_open univ
| inter  : ∀s t, generated_open s → generated_open t → generated_open (s ∩ t)
| sUnion : ∀k, (∀ s ∈  k, generated_open s) → generated_open (⋃₀ k)

-- ---------------------------------------------------------------------
-- Ejercicio 13. Sea g un conjunto de conjuntos de X. Demostrar que el
-- vacío es un abierto generado por g.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (X : Type)
  (g : set (set X))
  : generated_open X g ∅ :=
begin
  have h1 : ⋃₀(∅ : set (set X)) = ∅ := sUnion_empty,
  rw ←h1,
  apply generated_open.sUnion,
  simp,
end

-- 2ª demostración
lemma generated_open.empty
  (X : Type)
  (g : set (set X))
  : generated_open X g ∅ :=
begin
  have := generated_open.sUnion (∅ : set (set X)),
  simpa,
end

-- ---------------------------------------------------------------------
-- Ejercicio 14. Para cada conjunto de conjuntos de X, definir el
-- espacio topológico generado por g.
-- ---------------------------------------------------------------------

def generate_from (X : Type) (g : set (set X)) : topological_space X :=
{ is_open   := generated_open X g,
  univ_mem  := generated_open.univ,
  inter     := generated_open.inter,
  union     := generated_open.sUnion }

-- ---------------------------------------------------------------------
-- Ejercicio 15. Definir la topología indiscreta sobre X; es decir, la
-- topología cuyos únicos abiertos son el vacío y el universal.
-- ---------------------------------------------------------------------

def indiscrete (X : Type) : topological_space X :=
  generate_from X ∅

-- ---------------------------------------------------------------------
-- Ejercicio 16. Definir el producto de dos espacios topológicos.
-- ---------------------------------------------------------------------

instance prod.topological_space
  (X Y : Type)
  [topological_space X]
  [topological_space Y]
  : topological_space (X × Y) :=
topological_space.generate_from
  (X × Y)
  {U | ∃ (Ux : set X) (Uy : set Y) (hx : is_open Ux) (hy : is_open Uy),
       U = set.prod Ux Uy}

-- ---------------------------------------------------------------------
-- Ejercicio 17. Sean X e Y dos espacios topológicos y S ⊆ X × Y.
-- Demostrar que S es un abiertos del producto de X e Y si, y sólo si,
-- para todo (a,b) ∈ S, existen abiertos U y V tales que a ∈ U, b ∈ V
-- y U × V ⊆ S.
-- ---------------------------------------------------------------------

lemma is_open_prod_iff
  (X Y : Type)
  [topological_space X]
  [topological_space Y]
  {s : set (X × Y)}
  : is_open s ↔ (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧
                                          is_open v ∧
                                          a ∈ u ∧
                                          b ∈ v ∧
                                          set.prod u v ⊆ s) :=
sorry

-- =====================================================================
-- § Espacios métricos                                                --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir localmente la teoría de los grandes operadores.
-- ---------------------------------------------------------------------

open_locale big_operators

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los espacios métricos.
-- ---------------------------------------------------------------------

class metric_space_basic (X : Type) :=
  (dist : X → X → ℝ)
  (dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y)
  (dist_symm : ∀ x y, dist x y = dist y x)
  (triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

-- ---------------------------------------------------------------------
-- Ejercicio. Crear el espacio de nombre metric_space_basic
-- ---------------------------------------------------------------------

namespace metric_space_basic

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres topological_space.
-- ---------------------------------------------------------------------

open topological_space

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la distancia en los espacios métricos es no
-- negativa.
-- ---------------------------------------------------------------------

lemma dist_nonneg
  {X : Type}
  [metric_space_basic X]
  (x y : X)
  : 0 ≤ dist x y :=
begin
  have h : 0 ≤ 2 * dist x y,
    { calc 0
           = dist x x            : by rw (dist_eq_zero_iff x x).mpr rfl
       ... ≤ dist x y + dist y x : triangle x y x
       ... = dist x y + dist x y : by rw dist_symm
       ... = 2 * dist x y        : by rw two_mul (dist x y) },
  linarith,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Sea X un espacio métrico. Definir el espacio topológico
-- generado por X.
-- ---------------------------------------------------------------------

instance {X : Type} [metric_space_basic X] : topological_space X :=
  generate_from X { B | ∃ (x : X) r, B = {y | dist x y < r} }

-- end metric_space_basic
--
-- open metric_space_basic

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el producto de dos espacios métricos.
-- ---------------------------------------------------------------------

instance prod.metric_space_basic
  (X Y : Type)
  [metric_space_basic X]
  [metric_space_basic Y]
  : metric_space_basic (X × Y) :=
{ dist := λ u v, max (dist u.fst v.fst) (dist u.snd v.snd),
  dist_eq_zero_iff :=
    begin
      intros u v,
      split,
      { intro h,
        have hf := dist_nonneg u.fst v.fst,
        have hs := dist_nonneg u.snd v.snd,
        have := max_le_iff.mp (le_of_eq h),
        ext,
        { rw ← dist_eq_zero_iff, linarith, },
        { rw ← dist_eq_zero_iff, linarith, }},
      { intro h,
        rw h,
        rw (dist_eq_zero_iff _ _).mpr,
        { rw (dist_eq_zero_iff _ _).mpr,
          rw max_self,
          refl,  },
        { refl, }},
    end,
  dist_symm :=
    begin
      intros u v,
      simp [metric_space_basic.dist_symm],
    end,
  triangle :=
    begin
      intros x y z,
      have hf := triangle x.fst y.fst z.fst,
      have hs := triangle x.snd y.snd z.snd,
      simp only [max],
      split_ifs; linarith,
    end
  }

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase de los espacios topológicos de tipo T₂.
-- ---------------------------------------------------------------------

class t2_space (X : Type) [topological_space X] :=
(t2 : ∀ (x y : X) (h : x ≠ y), ∃ (Ux Uy : set X)
                                 (hUx : is_open Ux)
                                 (hUy : is_open Uy)
                                 (hx : x ∈ Ux)
                                 (hy : y ∈ Uy),
                                Ux ∩ Uy = ∅

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si X es un espacio topológico T₂, entonces
--    {xy : X × X | xy.fst ≠ xy.snd }
-- es abierto.
-- ---------------------------------------------------------------------

example
  (X : Type)
  [topological_space X]
  [t2_space X]
  : is_open {xy : X × X | xy.fst ≠ xy.snd } :=
begin
  rw is_open_prod_iff X X,
  intros x y h,
  obtain ⟨Ux, Uy, hUx, hUy, hx, hy, hxy⟩ := t2_space.t2 x y h,
  use [Ux, Uy, hUx, hUy, hx, hy],
  rintros ⟨tx, ty⟩ ⟨ht1, ht2⟩,
  dsimp,
  intro txy,
  rw txy at *,
  have : ty ∈ Ux ∩ Uy := ⟨ht1, ht2⟩,
  rw hxy at this,
  exact this,
end

-- Nota: Desgraciadamente, hemos creado dos topologías en `X × Y`, una a
-- través de `prod.topology` que hemos definido antes como el producto
-- de las dos topologías procedentes de las respectivas estructuras del
-- espacio métrico. Y una procedente de la métrica sobre el producto.
--
-- Estos son iguales, es decir, la misma topología (de lo contrario,
-- matemáticamente el producto no sería una buena definición). Sin
-- embargo no son iguales por definición, existe una prueba no trivial
-- para demostrar que son iguales. El sistema de clases de tipos (que
-- encuentra la instancia del espacio topológico relevante cuando usamos
-- lemas que implican espacios topológicos) no es capaz de comprobar que
-- las estructuras de espacios topológicos que son iguales por alguna
-- razón no trivial son iguales sobre la marcha, por lo que se bloquea.
--
-- Podemos usar `extends` para decir que un espacio métrico es una
-- estructura extra además de ser un espacio topológico por lo que
-- estamos haciendo una elección de topología para cada espacio métrico.
--
-- Esto puede no ser *definidamente* igual a la topología inducida, pero
-- deberíamos añadir el axioma de que la métrica y la topología son
-- iguales para evitar que creemos una métrica induciendo una topología
-- diferente a la estructura topológica que elegimos.


class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
  (compatible : ∀ U, is_open U ↔ generated_open X { B | ∃ (x : X) r, B = {y | dist x y < r}} U)

namespace metric_space

open topological_space

/- This might seem a bit inconvenient to have to define a topological space each time
we want a metric space.

We would still like a way of making a `metric_space` just given a metric and some
properties it satisfies, i.e. a `metric_space_basic`, so we should setup a metric space
constructor from a `metric_space_basic` by setting the topology to be the induced one. -/

def of_basic {X : Type} (m : metric_space_basic X) : metric_space X :=
{ compatible := begin intros, refl, /- this should work when the above parts are complete -/ end,
  ..m,
  ..@metric_space_basic.topological_space X m }

/- Now lets define the product of two metric spaces properly -/
instance {X Y : Type} [metric_space X] [metric_space Y] : metric_space (X × Y) :=
{ compatible :=
  begin
    -- Let's not fill this in for the demo, let me know if you do it!
    -- sorry
      rintros U,
      rw is_open_prod_iff,
      split; intro h,
      sorry,
      sorry,
    -- sorry
  end,
  ..prod.topological_space X Y,
  ..prod.metric_space_basic X Y, }

/- unregister the bad instance we defined earlier -/
local attribute [-instance] metric_space_basic.topological_space

/- Now this will work, there is only one topological space on the product, we can
rewrite like we tried to before a lemma about topologies our result on metric spaces,
as there is only one topology here.

## Exercise 6 [long?]:
Complete the proof of the example (you can generalise the 100 too if it makes it
feel less silly). -/

example (X : Type) [metric_space X] : is_open {xy : X × X | dist xy.fst xy.snd < 100 } :=
begin
  rw is_open_prod_iff X X,
  -- sorry
  intros x y h,
  use [{t | dist x t < 50 - dist x y / 2}, {t | dist y t < 50 - dist x y / 2}],
  split,
  { rw compatible,
    apply generated_open.basic,
    use [x, 50 - dist x y / 2], },
  split,
  { rw compatible,
    apply generated_open.basic,
    use [y, 50 - dist x y / 2], },
  split,
  { dsimp,
    rw (metric_space_basic.dist_eq_zero_iff x x).mpr rfl,
    change dist x y < 100 at h,
    linarith, },
  split,
  { dsimp,
    rw (metric_space_basic.dist_eq_zero_iff y y).mpr rfl,
    change dist x y < 100 at h,
    linarith, },
  rintros ⟨tx, ty⟩ ⟨htx, hty⟩,
  dsimp at *,
  calc dist tx ty ≤ dist tx x + dist x ty            : triangle tx x ty
             ...  ≤ dist tx x + dist x y + dist y ty : by linarith [triangle x y ty]
             ...  = dist x tx + dist x y + dist y ty : by rw dist_symm
              ... < 100                              : by linarith,
  -- sorry
end

end metric_space


namespace topological_space
/- As mentioned, there are many definitions of a topological space, for instance
one can define them via specifying a set of closed sets satisfying various
axioms, this is equivalent and sometimes more convenient.

We _could_ create two distinct Types defined by different data and provide an
equivalence between theses types, e.g. `topological_space_via_open_sets` and
`topological_space_via_closed_sets`, but this would quickly get unwieldy.
What's better is to make an alternative _constructor_ for our original
topological space. This is a function takes a set of subsets satisfying the
axioms to be the closed sets of a topological space and creates the
topological space defined by the corresponding set of open sets.

## Exercise 7 [medium]:
Complete the following constructor of a topological space from a set of subsets
of a given type `X` satisfying the axioms for the closed sets of a topology.
Hint: there are many useful lemmas about complements in mathlib, with names
involving `compl`, like `compl_empty`, `compl_univ`, `compl_compl`, `compl_sUnion`,
`mem_compl_image`, `compl_inter`, `compl_compl'`, `you can #check them to see what they say. -/

def mk_closed_sets
  (X : Type)
  (σ : set (set X))
  (empty_mem : ∅ ∈ σ)
  (univ_mem : univ ∈ σ)
  (inter : ∀ B ⊆ σ, ⋂₀ B ∈ σ)
  (union : ∀ (A ∈ σ) (B ∈ σ), A ∪ B ∈ σ) :
topological_space X := {
  is_open := λ U, U ∈ compl '' σ, -- the corresponding `is_open`
  empty_mem :=
    -- sorry
    begin
      use univ,
      split,
      assumption,
      exact compl_univ,
    end
    -- sorry
  ,
  univ_mem :=
    -- sorry
    begin
      use ∅,
      split,
      assumption,
      exact compl_empty,
    end
    -- sorry
  ,
  union :=
    -- sorry
    begin
      intros B hB,
      use (⋃₀ B)ᶜ,
      split,
      { rw compl_sUnion,
        apply inter,
        intros b hb,
        have := hB bᶜ ((mem_compl_image b B).mp hb),
        rw mem_compl_image at this,
        simpa, },
      { exact compl_compl (⋃₀ B) }
    end
    -- sorry
  ,
  inter :=
    -- sorry
    begin
      rintros A B ⟨Ac, hA, rfl⟩ ⟨Bc, hB, rfl⟩,
      rw [mem_compl_image, compl_inter, compl_compl, compl_compl],
      exact union _ hA _ hB,
    end
    -- sorry
    }

/- Here are some more exercises:

## Exercise 8 [medium/long]:
Define the cofinite topology on any type (PR it to mathlib?).

## Exercise 9 [medium/long]:
Define a normed space?

## Exercise 10 [medium/long]:
Define more separation axioms?

-/

end topological_space
