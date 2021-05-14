import tactic
import data.real.basic
import data.int.gcd
import data.padics

------------------------------------------------------------------------
-- § Primeros ejercicios                                              --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo del 3.
-- ----------------------------------------------------------------------

#check 3

-- Comentario: Al colocar el cursor sobre check se obtiene
--    3 : ℕ
-- que indica que 3 es un número natural.

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo del (3 : ℤ).
-- ----------------------------------------------------------------------

#check (3 : ℤ)

-- Comentario: Al colocar el cursor sobre check se obtiene
--    3 : ℤ
-- que indica que 3 es un número entero.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el número entero 3 es igual que el número
-- natural 3.
-- ----------------------------------------------------------------------

example : (3 : ℤ) = (3 : ℕ) :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el número real 3 es menor que 5.
-- ----------------------------------------------------------------------

example : (3 : ℝ) < 5 :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 3 es menor que 5.
-- ----------------------------------------------------------------------

example : 3 < 5 :=
by norm_num

-- ----------------------------------------------------------------------
-- Ejercicio. Demostrar que 3 más 20 es menor que 5 por 10.
-- ----------------------------------------------------------------------

example : 3 + 20 < 5 * 10 :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 11 es primo.
-- ----------------------------------------------------------------------

example : nat.prime 11 :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el valor de las siguientes expresiones
--    2 - 1
--    2 - 2
--    2 - 3
--    (2 : ℤ) - 3
--    6 / 3
--    6 / 4
--    (6 : ℚ) / 4
-- ----------------------------------------------------------------------

#eval 2 - 1
#eval 2 - 2
#eval 2 - 3
#eval (2 : ℤ) - 3
#eval 6 / 3
#eval 6 / 4
#eval (6 : ℚ) / 4

-- Comentario: Al colocar el cursor sobre eval se obtiene
--    2 - 1       = 1
--    2 - 2       = 0
--    2 - 3       = 0
--    (2 : ℤ) - 3 = -1
--    6 / 3       = 2
--    6 / 4       = 1
--    (6 : ℚ) / 4 = 3/2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b y c son número naturales y, para
-- todo entero b se tiene que (b + a < c + a), entonces (b < c).
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (a b c : ℕ)
  (h : (b : ℤ) + a < c + a)
  : b < c :=
begin
  rw ← (sub_lt_sub_iff_right (a : ℤ)) at h,
  rw add_sub_cancel at h,
  rw add_sub_cancel at h,
  norm_cast at h,
  exact h,
end

-- Prueba
-- ======

/-
a b c : ℕ,
h : ↑b + ↑a < ↑c + ↑a
⊢ b < c
  >> rw ← (sub_lt_sub_iff_right (a : ℤ)) at h,
h : ↑b + ↑a - ↑a < ↑c + ↑a - ↑a
⊢ b < c
  >> rw add_sub_cancel at h,
h : ↑b < ↑c + ↑a - ↑a
⊢ b < c
  >> rw add_sub_cancel at h,
h : ↑b < ↑c
⊢ b < c
  >> norm_cast at h,
h : b < c
⊢ b < c
  >> exact h,
no goals
-/

-- Comentarios:
-- 1. Se han usado los lemas
--    + sub_lt_sub_iff_right : a - c < b - c ↔ a < b
--    + add_sub_cancel : a + b - b = a
-- 2. La táctica (norma_cast at h) elimina las conversiones de la
--    hipótesis h.

-- 2ª demostración
-- ===============

example
  (a b c : ℕ)
  (h : (b : ℤ) + a < c + a)
  : b < c :=
begin
  rw ← (sub_lt_sub_iff_right (a : ℤ)) at h,
  rw add_sub_cancel at h,
  rw add_sub_cancel at h,
  exact_mod_cast h,
end

-- Prueba
-- ======

/-
a b c : ℕ,
h : ↑b + ↑a < ↑c + ↑a
⊢ b < c
  >> rw ← (sub_lt_sub_iff_right (a : ℤ)) at h,
h : ↑b + ↑a - ↑a < ↑c + ↑a - ↑a
⊢ b < c
  >> rw add_sub_cancel at h,
h : ↑b < ↑c + ↑a - ↑a
⊢ b < c
  >> rw add_sub_cancel at h,
h : ↑b < ↑c
⊢ b < c
  >> exact_mod_cast h,
no goals
-/

-- Comentarios:
-- 1. La táctica (exact_mod_cast h) normaliza el objetivo y lo resuelve
--    con exact.

-- 3ª demostración
-- ===============

example
  (a b c : ℕ)
  (h : (b : ℤ) + a < c + a)
  : b < c :=
begin
  rw ← (sub_lt_sub_iff_right (a : ℤ)) at h,
  rw add_sub_cancel at h,
  rw add_sub_cancel at h,
  assumption_mod_cast,
end

-- Prueba
-- ======

/-
a b c : ℕ,
h : ↑b + ↑a < ↑c + ↑a
⊢ b < c
  >> rw ← (sub_lt_sub_iff_right (a : ℤ)) at h,
h : ↑b + ↑a - ↑a < ↑c + ↑a - ↑a
⊢ b < c
  >> rw add_sub_cancel at h,
h : ↑b < ↑c + ↑a - ↑a
⊢ b < c
  >> rw add_sub_cancel at h,
h : ↑b < ↑c
⊢ b < c
  >> assumption_mod_cast,
no goals
-/

-- Comentarios:
-- 1. La táctica assumption_cast unifica el objetivo con una de las
--    hipótesis eliminando la conversión de tipos.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si n es un número primo, entonces
--    1 / n < 1
-- ----------------------------------------------------------------------

variable n : ℕ

-- 1ª demostración
-- ===============

example
  (hn : nat.prime n)
  : 1 / (n : ℝ) < 1 :=
begin
  rw one_div_lt,
  { norm_num,
    norm_cast,
    exact nat.prime.one_lt hn },
  { norm_cast,
    exact nat.prime.pos hn },
  { norm_num },
end

-- Prueba
-- ======

/-
n : ℕ,
hn : nat.prime n
⊢ 1 / ↑n < 1
  >> rw one_div_lt,
| | 3 goals
| | n : ℕ,
| | hn : nat.prime n
| | ⊢ 1 / 1 < ↑n
| |   >> { norm_num,
| | ⊢ 1 < ↑n
| |   >>   norm_cast,
| | ⊢ 1 < n
| |   >>   exact nat.prime.one_lt hn },
| 2 goals
| n : ℕ,
| hn : nat.prime n
| ⊢ 0 < ↑n
|   >> { norm_cast,
| ⊢ 0 < n
|   >>   exact nat.prime.pos hn },
n : ℕ,
hn : nat.prime n
⊢ 0 < 1
  >> { norm_num },
no goals
-/

-- Comentarios:
-- 1. Se han usado los lemas
--    + one_div_lt : 0 < a → 0 < b → (1 / a < b ↔ 1 / b < a)
--    + nat.prime.one_lt : nat.prime n → 1 < n
--    + nat.prime.pos : nat.prime n → 0 < n

-- 2ª demostración
-- ===============

example
  (hn : nat.prime n)
  : 1 / (n : ℝ) < 1 :=
begin
  rw one_div_lt,
  { norm_num,
    apply_mod_cast nat.prime.one_lt,
    assumption },
  { norm_cast,
    exact nat.prime.pos hn },
  { norm_num },
end

-- Comentario: La táctica (apply_mod_cast h) aplica h con conversiones
-- de tipos.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los cuerpos totalmente ordenados,
--    123 + 45 < 67890/3
-- ----------------------------------------------------------------------

example {α : Type} [linear_ordered_field α] : 123 + 45 < 67890/3 :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 7/3 no es mayor que 2.
-- ----------------------------------------------------------------------

example : ¬ 7/3 > 2 :=
by norm_num

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si el número real x es menor que 50 * 50,
-- entonces también es menor que 25 * 100.
-- ----------------------------------------------------------------------

example
  (x : ℝ)
  (hx : x < 50*50)
  : x < 25*100 :=
begin
  norm_num at hx ⊢,
  assumption,
end

-- Prueba
-- ======

/-
x : ℝ,
hx : x < 50 * 50
⊢ x < 25 * 100
  >> norm_num at hx ⊢,
hx : x < 2500
⊢ x < 2500
  >> assumption,
no goals
-/

-- Comentario: La táctica (norm_num at h ⊢) normaliza las expresiones
-- numéricas en la hipótesis h y en la conclusión.

-- ---------------------------------------------------------------------
-- Ejercicio. Sea x un número entero. Demostrar que si x (como número
-- real) es menor que 25*100, entonces x es menor que 25*100.
-- ----------------------------------------------------------------------

example
  (x : ℤ)
  (hx : (x : ℝ) < 25*100)
  : x < 25*100 :=
begin
  assumption_mod_cast,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Sea x un número entero. Demostrar que si x (como número
-- real) es menor que 2500, entonces x es menor que 25*100.
-- ----------------------------------------------------------------------

example
  (x : ℤ)
  (hx : (x : ℝ) < 2500)
  : x < 25*100 :=
begin
  norm_num,
  assumption_mod_cast,
end

-- Prueba
-- ======

/-
x : ℤ,
hx : ↑x < 2500
⊢ x < 25 * 100
  >> norm_num,
hx : ↑x < 2500
⊢ x < 2500
  >> assumption_mod_cast,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Sean p, q y r números naturales. Demostrar que si
--    r < p - q
--    q ≤ p
-- entonces r (como número real) es menor que p - q.
-- ----------------------------------------------------------------------

example
  (p q r : ℕ)
  (h : r < p - q)
  (hpq : q ≤ p)
  : (r : ℝ) < p - q :=
begin
  exact_mod_cast h,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Sean p, q y r números naturales tales que (r < p + 2 - p).
-- Demostrar que r (como entero) es menor que 5.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (p q r : ℕ)
  (hr : r < p + 2 - p)
  : (r : ℤ) < 5 :=
begin
  have : p ≤ p + 2, by linarith,
  zify [this] at hr,
  linarith,
end

-- Prueba
-- ======

/-
p q r : ℕ,
hr : r < p + 2 - p
⊢ ↑r < 5
  >> have : p ≤ p + 2, by linarith,
this : p ≤ p + 2
⊢ ↑r < 5
  >> zify [this] at hr,
hr : ↑r < ↑p + 2 - ↑p
⊢ ↑r < 5
  >> linarith,
-/

-- 2ª demostración
-- ===============

example
  (p q r : ℕ)
  (hr : r < p + 2 - p)
  : (r : ℤ) < 5 :=
begin
  norm_num at hr,
  norm_cast,
  linarith,
end

-- Prueba
-- ======

/-
p q r : ℕ,
hr : r < p + 2 - p
⊢ ↑r < 5
  >> norm_num at hr,
hr : r < 2
⊢ ↑r < 5
  >> norm_cast,
hr : r < 2
⊢ r < 5
  >> linarith,
no goals
-/

------------------------------------------------------------------------
-- § Números p-ádicos                                                 --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la teoría padic_val_rat
-- ----------------------------------------------------------------------

open padic_val_rat

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de los siguentes lemas
--    fpow_le_of_le
--    fpow_nonneg_of_nonneg
--    padic_val_rat_of_int
-- ----------------------------------------------------------------------

#check fpow_le_of_le
#check fpow_nonneg_of_nonneg
#check padic_val_rat_of_int

-- Comentario: Al colocar el cursor sobre check se obtiene
-- + fpow_le_of_le : 1 ≤ x → ∀ {a b : ℤ}, a ≤ b → x ^ a ≤ x ^ b
-- + fpow_nonneg_of_nonneg : 0 ≤ x → ∀ (z : ℤ), 0 ≤ x ^ z
-- + padic_val_rat_of_int :
--    ∀ (z : ℤ) (hp : x ≠ 1) (hz : z ≠ 0),
--    padic_val_rat x ↑z = ↑((multiplicity ↑x z).get _)

-- ---------------------------------------------------------------------
-- Ejercicio. Sean p y n números naturales y z un número entero.
-- Demostrar que si p es un número primo y p^n divide a z, entonces
--    padic_norm p z ≤ ↑p ^ (-n : ℤ)
-- ----------------------------------------------------------------------

example
  {p n : ℕ}
  (hp : p.prime)
  {z : ℤ}
  (hd : ↑(p^n) ∣ z)
  : padic_norm p z ≤ ↑p ^ (-n : ℤ) :=
begin
  have aux_lemma : ∀ inst, (n : ℤ) ≤ (multiplicity ↑p z).get inst,
  { intro,
    norm_cast,
    rw [← enat.coe_le_coe, enat.coe_get],
    apply multiplicity.le_multiplicity_of_pow_dvd,
    assumption_mod_cast },
  unfold padic_norm,
  split_ifs with hz hz,
  { apply fpow_nonneg_of_nonneg,
    exact_mod_cast le_of_lt hp.pos },
  { apply fpow_le_of_le,
    exact_mod_cast le_of_lt hp.one_lt,
    apply neg_le_neg,
    rw padic_val_rat_of_int _ hp.ne_one _,
    { apply aux_lemma },
    { assumption_mod_cast } }
end

------------------------------------------------------------------------
-- § Coprimos                                                         --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si p y q son coprimos, entonces existen
-- enteros u y v tales que
--    u*p+v*q = 1
-- ----------------------------------------------------------------------

example
  (p q : ℕ)
  (h : nat.coprime p q)
  : ∃ u v : ℤ, u*p+v*q = 1 :=
begin
  have := nat.gcd_eq_gcd_ab,
  specialize this p q,
  unfold nat.coprime at h,
  rw h at this,
  norm_cast at this,
  use [p.gcd_a q, p.gcd_b q],
  rw this,
  ring,
end

-- Prueba
-- ======

/-
p q : ℕ,
h : p.coprime q
⊢ ∃ (u v : ℤ), u * ↑p + v * ↑q = 1
  >> have := nat.gcd_eq_gcd_ab,
this : ∀ (x y : ℕ), ↑(x.gcd y) = ↑x * x.gcd_a y + ↑y * x.gcd_b y
⊢ ∃ (u v : ℤ), u * ↑p + v * ↑q = 1
  >> specialize this p q,
this : ↑(p.gcd q) = ↑p * p.gcd_a q + ↑q * p.gcd_b q
⊢ ∃ (u v : ℤ), u * ↑p + v * ↑q = 1
  >> unfold nat.coprime at h,
h : p.gcd q = 1
⊢ ∃ (u v : ℤ), u * ↑p + v * ↑q = 1
  >> rw h at this,
this : ↑1 = ↑p * p.gcd_a q + ↑q * p.gcd_b q
⊢ ∃ (u v : ℤ), u * ↑p + v * ↑q = 1
  >> norm_cast at this,
this : 1 = ↑p * p.gcd_a q + ↑q * p.gcd_b q
⊢ ∃ (u v : ℤ), u * ↑p + v * ↑q = 1
  >> use [p.gcd_a q, p.gcd_b q],
⊢ p.gcd_a q * ↑p + p.gcd_b q * ↑q = 1
  >> rw this,
⊢ p.gcd_a q * ↑p + p.gcd_b q * ↑q = ↑p * p.gcd_a q + ↑q * p.gcd_b q
  >> ring,
no goals
-/

------------------------------------------------------------------------
-- § Límite de una sucesión                                           --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Representar con |x| el valor absoluto de x.
-- ----------------------------------------------------------------------

notation `|`x`|` := abs x

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--     seq_limit : (ℕ → ℝ) → ℝ → Prop
-- tal que (seq_limit u l) afirma que l es el límite de la sucesión u.
-- ----------------------------------------------------------------------

def seq_limit : (ℕ → ℝ) → ℝ → Prop :=
λ u l, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el límite de la sucesión (n+1)/n es 1.
-- ----------------------------------------------------------------------

example : seq_limit (λ n : ℕ, (n+1)/n) 1 :=
begin
  intros ε ε_pos,
  dsimp,
  use nat_ceil (1/ε),
  intros n hn,
  have n_pos : 0 < n,
  { calc 0 < nat_ceil (1/ε) : _
       ... ≤ n : _,
    { rw lt_nat_ceil,
      simp,
      assumption },
    { assumption } },
  rw [abs_of_nonneg,
      sub_le_iff_le_add,
      div_le_iff,
      add_mul,
      one_mul,
      add_comm _ (n : ℝ),
      add_le_add_iff_left],
  { calc 1 = ε * (1/ε) : _
       ... ≤ ε * nat_ceil (1/ε) : _
       ... ≤ ε * n : _,
    { symmetry,
      apply mul_one_div_cancel,
      linarith },
    { rw mul_le_mul_left ε_pos,
      apply le_nat_ceil },
    { rw mul_le_mul_left ε_pos,
      exact_mod_cast hn } },
  { assumption_mod_cast },
  { field_simp,
    apply one_le_div_of_le;
    norm_cast;
    linarith }
end

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en la teoría numbers.lean de Robert Y. Lewis que se
-- encuentra en https://bit.ly/39teUbt y se comenta en el vídeo
-- "Numbers in Leann" que se encuentra en https://youtu.be/iEs2U_kzYy4
