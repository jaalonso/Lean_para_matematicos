import tactic

lemma my_lemma: ∀ n : ℕ, n ≥ 0 :=
λ n, nat.zero_le n

lemma my_lemma2: ∀ n : ℕ, n ≥ 0 :=
begin
  intro n,
  apply nat.zero_le,
end

#print my_lemma2

-- Comentario: Al colocar el cursor sobre print se obtiene
--    theorem my_lemma2 : ∀ (n : ℕ), n ≥ 0 :=
--    λ (n : ℕ), n.zero_le

lemma my_lemma3: ∀ n : ℕ, n ≥ 0 :=
begin
  show_term {intro n, apply nat.zero_le},
end

-- Comentario: Al colocar el cursor sobre show_term se obtiene
--    λ n, n.zero_le

------------------------------------------------------------------------
-- § Referencia                                                       --
------------------------------------------------------------------------

-- Basado en el vídeo "Metaprogramming in Lean tutorial: video 1" de Rob
-- Lewis que se encuentra en https://youtu.be/o6oUjcE6Nz4 

