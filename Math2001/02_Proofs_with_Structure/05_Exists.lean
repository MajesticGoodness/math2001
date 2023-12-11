/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]

    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have ha :=
      calc
      -0 < -(x * t) := by rel [hxt]
      _ = x * (-t) := by ring
    have haa :=
      calc
      x * (-t) > -0 := by rel [ha]
      _ = 0 := by ring
    cancel x at haa
    apply ne_of_lt
    have haaa :=
      calc
        - (-t) < -0 := by rel [haa]
        _ = 0 := by ring
    have : t < 0 := by addarith [haaa]
    apply this

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  calc
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  calc
    (p + q) / 2 < (q + q) / 2 := by rel [h]
    _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use (13 / 10)
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9
  use 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use (-1/2)
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0
  use 0
  numbers

-- example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
--   use (x + 1)
--   have h0 :=
--     calc
--     x = x := by ring
--     _ < x + 1 := by addarith
--   have h1 :=
--   calc
--     x = x := by ring
--     _ ≤ x + x ^ 2 := by extra
--     _ = x * (x + 1) := by ring
--     -- _ < (x + 1) * (x + 1) := by rel [h0] - doesn't work unforunately, we don't know if x > 0
--   have h2 :=
--   calc
--     2*x ≤ 2 * x + x ^ 2 := by extra
--     _ ≤ 2 * x + x ^ 2 + 1 ^ 2 := by extra
--     _ = (x + 1) ^ 2 := by ring
--   have h3 :=
--     calc
--     x ≤ x + 0 ^ 2 / 2 := by extra
--     _ = (2 * x + 0) / 2 := by ring
--     _ ≤ ((x + 1) ^ 2 + 0) / 2 := by rel [h2]
--     _ = (x + 1) ^ 2 / 2 := by ring

-- example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
--   use (x ^ 2 + 1)
--   have h0 :=
--     calc
--     x ^ 2 < x ^ 2 + 1 := by extra
--     _ = x ^ 2 + 1 := by ring
--   have h1 :=
--     calc
--     x ^ 2 ≤ x ^ 2 + x ^ 4 := by extra
--     _ = x ^ 2 * (x ^ 2 + 1) := by ring
--     _ < (x ^ 2 + 1) * (x ^ 2 + 1) := by rel [h0]

-- example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
--   use (x + 1) / 2
--   have h00 :=
--     calc
--     x > x - 1 := by addarith
--     _ = x - 1 := by ring
--   have h0 :=
--     calc
--     x < x + 1 := by addarith
--     _ = x + 1 := by ring
--   have h1337 :=
--     calc
--     x = x / 2 + x / 2 := by ring
--     _ ≤ (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by extra
--   have h13377 :=
--     calc
--     x = x / 2 + x / 2 := by ring
--     _ ≤ (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by extra
--     _ < (x + 1) / 2 + (x + 1) / 2 + ((x - 1) / 2) ^ 2 := by rel [h0]
--   have homie :=
--     calc
--     x ≤ ((x + 1) / 2) ^ 2 := by rel[h2]
--   have h2 :=
--     calc
--     ((x + 1) / 2) ^ 2 = x / 2 + x ^ 2 / 4 + 1 / 4 := by ring
--     _ = (x / 2 + x / 2) + (x ^ 2 / 4 - 2 * x / 4 + 1 / 4) := by ring
--     _ = (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by ring
--     _ ≥ x := by rel [h1337] -- Close! But how do I get it with '>' instead of '≥'?
  -- have h2 :=
  --   calc
  --   ((x + 1) / 2) ^ 2 > ((x + 1) / 2) ^ 2 - 1 := by addarith
  --   _ = (x / 2 + x / 2) + (x ^ 2 / 4 - 2 * x / 4 + 1 / 4) - 1:= by ring
  --   _ = (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 - 1:= by ring
  --   _ ≥ x - 1:= by rel [h1337] -- Close! But how do I get it with '>' instead of '≥'?
  -- have h9000 :=
  --   calc
  --   ((x + 1) / 2) ^ 2 > ((x + 1) / 2) ^ 2 - 1 := by addarith
  --   _ > ((x + 1) / 2) ^ 2
  -- have kewl :=
  --   calc
  --   ((x + 1) / 2) ^ 2 = (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by ring
  --   _ > (x + 1) / 2 + (x + 1) / 2 + ((x - 1) / 2) ^ 2 := by rel [h0]
  -- have h1 :=
  --   calc
  --   x = x / 2 + x / 2 := by ring
  --   _ ≤ (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by extra
  --   _ = (x / 2 + x / 2) + (x ^ 2 / 4 - 2 * x / 4 + 1 / 4) := by ring
  --   _ = x / 2 + x ^ 2 / 4 + 1 / 4 := by ring
  --   _ = ((x + 1) / 2) ^ 2 := by ring
  -- have h2 :=
  --   calc
  --   ((x + 1) / 2) ^ 2 = x / 2 + x ^ 2 / 4 + 1 / 4 := by ring
  --   _ = (x / 2 + x / 2) + (x ^ 2 / 4 - 2 * x / 4 + 1 / 4) := by ring
  --   _ = (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by ring
  --   _ ≥ x := by rel [h1337] -- Close! But how do I get it with '>' instead of '≥'?
  --   _ > x - 1 := by rel [h00]
  -- have h3 :=
  --   calc
  --   ((x + 1) / 2) ^ 2 = x / 2 + x ^ 2 / 4 + 1 / 4 := by ring
  --   _ = (x / 2 + x / 2) + (x ^ 2 / 4 - 2 * x / 4 + 1 / 4) := by ring
  --   _ > (x / 2 + (x) / 2) + (x ^ 2 / 4 - 2 * (x + 1) / 4 + 1 / 4) := by rel [h0]
  --   _ > (x-1) / 2 + (x-1) / 2 + (x ^ 2 / 4 - 2 * (x + 1) / 4 + 1 / 4) := by rel [h00]
  --   _ = (x-1) / 2 - (x+1) / 2 + (x-1)/2 + (x ^2 / 4 + 1 / 4) := by ring
  --   _ = -2 / 2 + (x-1)/2 + (x ^2 / 4 + 1 / 4) := by ring
  --   _ = x / 2 - 3 / 2 + (x ^2 / 4 + 1 / 4) := by ring --idk where i was going with this lmao
  --   _ = ((x + 1) / 2) ^ 2 - 3 / 2 := by ring -- might be a clue, who knows.

/-
Oh my god, I fucking did it. And the solution was so simple too...Sometimes you just don't
connect the dots. Once I realized my work was a dead-end, I started gazing at:

(x / 2) + x ^ 2 / 4 + 1 / 4

I thought, jee, we would be finished with our proof if instead of an x / 2 term, we had
just an x. So, I started asking myself, what kind of square might result in that term being
reduced to just an x? I started going through the list of perfect squares in my head, to see if
I could find some combination of integers, that when squared, are reduced to just an x on the
middle term. Something like:

((3 / 2) * (x + 1)) ^ 2

But I was trying to do the impossible. I don't think there's any combination that would have
given me what I wanted.

Was there another way? I finally started to consider:
"what if I just use (2x + 1) / 2 instead of (x + 1) / 2"?
Damn. That actually works out. I wasn't even considering doing something like that until
I exhausted all my options lol. Took us a while but we got there.

-/
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use (2 * x + 1) / 2
  have h00 :=
    calc
    ((2 * x + 1) / 2) ^ 2 = 4 * x ^ 2 / 4 + 4 * x / 4 + 1 / 4 := by ring
     _ ≥ 0 + 4 * x / 4 + 1 / 4 := by extra
     _ = x + 1 / 4 := by ring
     _ > x := by addarith
  apply h00

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b)
    (ha' : 0 ≤ a) (hb' : 0 ≤ b) (hc' : 0 ≤ c) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
