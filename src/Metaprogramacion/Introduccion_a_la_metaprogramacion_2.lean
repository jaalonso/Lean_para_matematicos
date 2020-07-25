import tactic
set_option pp.numerals false
set_option pp.generalized_field_notation false

def n : ℕ := 3 * 2

#reduce n

-- Comentario: Al situar el cursor sobre reduce se obtiene
--    nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ nat.zero)))))

#reduce (show 2 ≤ 10, from dec_trivial)

-- Comentario: Al situar el cursor sobre reduce se obtiene
--    nat.less_than_or_equal.step
--     (nat.less_than_or_equal.step
--      (nat.less_than_or_equal.step
--       (nat.less_than_or_equal.step
--        (nat.less_than_or_equal.step
--         (nat.less_than_or_equal.step
--          (nat.less_than_or_equal.step 
--            (nat.less_than_or_equal.step nat.less_than_or_equal.refl)))))))

meta def f : ℕ → ℕ
| n := if n = 1 then 1
       else if n % 2 = 0 then f (n / 2)
       else f (3 * n + 1)

-- Comentario: Sin meta no acepta la definición porque no puede probar
-- su terminación. 

#eval f 23

-- Comentario: Al situar el cursor sobre eval se obtiene 1.

#eval (list.iota 10)

-- Comentario: Al situar el cursor sobre eval se obtiene 
--    [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]

#eval (list.iota 10).map f

-- Comentario: Al situar el cursor sobre eval se obtiene 
--    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Metaprogramming in Lean tutorial: video 2" de Rob
-- Lewis que se encuentra en https://youtu.be/ZPjXSTXSV-o
