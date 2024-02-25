import Mathlib.Tactic.Linarith

def even(x: Nat): Prop := ∃ (k: Nat), x = 2 * k
def odd(x: Nat): Prop := ∃ (k: Nat), x = 2 * k + 1
def divisible (x y : Nat) : Prop := ∃ (k : Nat), y = k * x

theorem two_even: even 2 := by
  unfold even
  exists 1

theorem odd_not_even: ∀ x, odd x -> ¬ even x := by
  intros x
  intros h
  unfold odd at h
  cases h with
  | intro k1 hk1 =>
    unfold even
    rw [hk1]
    sorry

-- the sum of two odd integers is even --
-- for all natural numbers x and y, if x is odd and y is odd, then x + y is even.
theorem odd_sum_even_comments: ∀ x y, odd x -> odd y -> even (x + y) := by
  intros x y h1 h2
  -- introducing the variables x and y, along with 2 hypotheses
  -- h1 and h2 where h1 asserts that x is odd, and h2 asserts that y is odd --
  unfold odd at h1
  -- unfolds the definition of odd at hypothesis h1
  -- it replaces h1 with its definition, like saying
  -- "there exists an integer k such that x = 2k + 1"
  unfold odd at h2
  -- similar to line above but replaces h2 with the definition
  -- for y being an odd number
  cases h1 with
  -- starting a case analysis on the hypothesis h1
  -- analyzing structure of h1 after unfolding 
  -- involves an existential quantifier
  | intro k1 hk1 =>
    -- introducing  a new variable k1 and hypothesis hk1 from the case 
    -- analysis of h1. hk1 is the statement that x = 2k1 + 1.
    cases h2 with
    --  starting a case analysis on the hypothesis h2, following the same logic as for h1
    | intro k2 hk2 => 
    -- introducing a new variable k2 and hypothesis hk2, which is the statement y = 2k2 + 1
      exists (k1 + k2 + 1)
      -- asserts the existence of an integer (k1 + k2 + 1)
      -- (used to prove that x + y is even)
      rw [hk1]
      -- rewriting expression using hk1, replacing x with 2k+1
      rw [hk2]
      -- rewriting expression using hk2, replaying y with 2k2+1
      rw [<- Nat.add_assoc]
      -- associativity of addition to rearrange the terms in the expression
      linarith
      -- concludes the proof using linear arithmetic
      -- simplifies and proves that the resulting expression represnts an even number

theorem odd_sum_even: ∀ x y, odd x -> odd y -> even (x + y) := by
  intros x y h1 h2
  unfold odd at h1
  unfold odd at h2
  cases h1 with
  | intro k1 hk1 =>
    cases h2 with
    | intro k2 hk2 => 
      exists (k1 + k2 + 1)
      rw [hk1]
      rw [hk2]
      rw [<- Nat.add_assoc]
      linarith

theorem all_nat_even_or_odd: ∀ x, odd x ∨ even x := by
  intro x; induction x with
  | zero        =>
    apply Or.intro_right
    unfold even
    exists 0
  | succ n ihn  =>
    cases ihn
    case inr h =>
      apply Or.inl
      unfold even at h
      cases h with
      | intro hk hn =>
        unfold odd
        exists hk
        rw [hn]
    case inl h =>
      apply Or.inr
      unfold odd at h
      cases h with
      | intro ho hn =>
        unfold even
        exists ho + 1
        linarith

-- product of two odd integers is odd -- 
-- for all natural numbers x and y, if x is odd and y is odd, then their product x * y is also odd --
theorem odd_product_odd_comments : ∀ x y, odd x -> odd y -> odd (x * y) := by
  intros x y h1 h2
  -- introduces the variables x and y, along with 2 hypotheses
  -- h1 and h2 where h1 asserts that x is odd, and h2 asserts that y is odd --
  unfold odd at h1
  unfold odd at h2
  -- instead of odd x and odd y, work with their definitions: there exist natural 
  -- numbers k1 and k2 such that x = 2 * k1 + 1 and y = 2 * k2 + 1
  cases h1 with
  | intro k1 hk1 =>
  -- introduces a new variable k1 and a hypothesis hk1 that x = 2 * k1 + 1
    cases h2 with
    | intro k2 hk2 =>
    -- introduces a variable k2 and a hypothesis hk2 that y = 2 * k2 + 1
      exists (2 * k1 * k2 + k1 + k2)
      -- assert that there exists a natural number that will represent the form of an odd number for x * y
      rw [hk1, hk2]
      -- rewrites the expressions of x and y in the theorem using the hypotheses hk1 and hk2
      -- replacing x with 2 * k1 + 1 and y with 2 * k2 + 1
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, <- Nat.add_assoc]
      -- arithmetic distribution and associative laws to transform the expression
      repeat {rw [Nat.mul_assoc]}
      --  associative property of multiplication to rearrange the terms in preparation for the final linear arithmetic step
      linarith
      -- applied to confirm that the constructed expression indeed represents an odd number

theorem odd_product_odd : ∀ x y, odd x -> odd y -> odd (x * y) := by
  intros x y h1 h2
  unfold odd at h1
  unfold odd at h2
  cases h1 with
  | intro k1 hk1 =>
    cases h2 with
    | intro k2 hk2 =>
      exists (2 * k1 * k2 + k1 + k2)
      rw [hk1, hk2]
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, <- Nat.add_assoc]
      repeat {rw [Nat.mul_assoc]}
      linarith

theorem even_sum_even : ∀ x y, even x -> even y -> even (x + y) := by
  intros x y h1 h2
  unfold even at h1
  unfold even at h2
  cases h1 with
  | intro k1 hk1 =>
    cases h2 with
    | intro k2 hk2 =>
      exists (k1 + k2)
      -- rw [hk1, hk2]
      linarith

theorem div_6_implies_div_3 : ∀ x, divisible 6 x -> divisible 3 x := by
  intros x h1
  unfold divisible at h1
  cases h1 with 
  | intro k hk =>
    exists (2 * k)
    rw [hk]
    rw [Nat.mul_assoc]
    linarith
