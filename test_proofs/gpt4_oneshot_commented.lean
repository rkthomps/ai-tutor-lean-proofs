import Mathlib.Tactic.Linarith
-- import data.nat.basic -- even_or_odd
-- open nat -- even_or_odd

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1
def divisible (x y : Nat) : Prop := ∃ (k : Nat), y = k * x

theorem odd_sum_even : ∀ x y, odd x -> odd y -> even (x + y) :=
begin
  intros x y h1 h2 ,
  -- introduces the variables x and y, along with 2 hypotheses
  -- h1 and h2 where h1 asserts that x is odd, and h2 asserts that y is odd --
  unfold odd at h1,
  unfold odd at h2,
  -- instead of odd x and odd y, work with their definitions: there exist natural 
  -- numbers k1 and k2 such that x = 2 * k1 + 1 and y = 2 * k2 + 1
  cases h1 with k1 hk1,
  -- introduces a new variable k1 and a hypothesis hk1 that x = 2 * k1 + 1
  cases h2 with k2 hk2,
  -- introduces a variable k2 and a hypothesis hk2 that y = 2 * k2 + 1
  exists (k1 + k2 + 1),
  -- assert that there exists a natural number that will represent the form



def evenNum (n : ℕ) : Prop := ∃ k, n = 2 * k
def oddNum (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

theorem even_or_odd : ∀ n : ℕ, evenNum n ∨ oddNum n :=
begin
  intro n,
  induction n with d hd,
  { left, use 0, simp },
  { cases hd with even_d odd_d,
    { right, use d, linarith },
    { left, cases odd_d with k hk, use k + 1, linarith }}
end

theorem odd_mul_even : ∀ x y, odd x -> odd y -> even (x * y) :=
begin
  intros x y h1 h2,
  -- introducing the variables x and y, along with 2 hypotheses
  -- h1 and h2 where h1 asserts that x is odd, and h2 asserts that y is odd --
  unfold odd at h1,
  unfold odd at h2,
  -- unfolds the definition of odd at hypotheses h1 and h2
  -- it replaces h1 and h2 with their definitions
  cases h1 with k1 hk1,
  cases h2 with k2 hk2,
  -- starting a case analysis on the hypotheses h1 and h2
  -- analyzing structure of h1 and h2 after unfolding 
  -- involves an existential quantifier
  use k1 * k2 + k1 + k2,
  -- asserts the existence of an integer (k1 * k2 + k1 + k2)
  -- (used to prove that x * y is even)
  rw [hk1, hk2],
  -- rewriting expression using
  hk1 and hk2, replacing x with 2k1+1 and y with 2k2+1
  ring,
  -- concludes the proof using ring theory
  -- simplifies and proves that the resulting expression represents an even number
end

theorem even_sum_even : ∀ x y, even x -> even y -> even (x + y) :=
begin
  intros x y h1 h2,
  -- introducing the variables x and y, along with 2 hypotheses
  -- h1 and h2 where h1 asserts that x is even, and h2 asserts that y is even
  unfold even at h1,
  unfold even at h2,
  -- unfolding the definition of even at hypotheses h1 and h2
  cases h1 with k1 hk1,
  cases h2 with k2 hk2,
  -- starting a case analysis on the hypotheses h1 and h2
  -- introducing new variables k1 and k2 and hypotheses hk1 and hk2 from the case analysis
  -- hk1 is the statement that x = 2*k1 and hk2 is the statement that y = 2*k2
  use k1 + k2,
  -- asserting the existence of an integer (k1 + k2)
  -- used to prove that x + y is even
  rw [hk1, hk2],
  --
-- didn't even finish it