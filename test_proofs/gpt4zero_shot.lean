-- import data.nat.basic -- import for problem odd_sum_even
-- open nat -- for odd_sum_even 

--def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
--def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1
--def divisible (x y : Nat) : Prop := ∃ (k : Nat), y = k * x
-- commented this out because gpt4 kept redefining it for me with different notation
theorem two_is_even : even 2 :=
begin
  unfold even,
  use 1,
  ring,
end

-- I gave it the same definitions and it included it in the message
-- def even (x : ℕ) : Prop := ∃ (k : ℕ), x = 2 * k
-- def odd (x : ℕ) : Prop := ∃ (k : ℕ), x = 2 * k + 1

theorem sum_of_two_odd_is_even (x y : ℕ) (hx : odd x) (hy : odd y) : even (x + y) :=
begin
  cases hx with k hxk,
  cases hy with l hyl,
  use k + l + 1,
  rw [hxk, hyl],
  ring,
end

-- gave definitions back to me in a different notation
theorem even_or_odd (n : ℕ) : even n ∨ odd n :=
nat.rec_on n
  (or.inl ⟨0, rfl⟩) -- base case: 0 is even
  (λ _ ih => -- inductive step: assume n is either even or odd
    or.elim ih
      (λ ⟨k, hk⟩ => or.inr ⟨k, by rw [hk, mul_succ, add_comm]⟩) -- if n is even, then n+1 is odd
      (λ ⟨k, hk⟩ => or.inl ⟨k+1, by rw [hk, mul_succ, add_comm]⟩)) -- if n is odd, then n+1 is even

theorem odd_mul_odd : ∀ (m n : ℕ), odd m → odd n → odd (m * n) :=
begin
  intros m n hm hn,
  cases hm with k hk,
  cases hn with l hl,
  use 2 * k * l + k + l,
  rw [hk, hl],
  ring,
end

def even (n : ℕ) := ∃ k, n = 2 * k
def odd (n : ℕ) := ∃ k, n = 2 * k + 1
def divisible (x y : ℕ) := ∃ k, y = k * x

theorem even_plus_even_is_even {a b : ℕ} (h1 : even a) (h2 : even b) : even (a + b) :=
begin
  cases h1 with k1 hk1,
  cases h2 with k2 hk2,
  use k1 + k2,
  rw [hk1, hk2, two_mul, two_mul, add_mul],
end