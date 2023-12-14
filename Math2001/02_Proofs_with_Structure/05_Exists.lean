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

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use (x + 1) / 2
  have h00 :=
    calc
    x > x - 1 := by addarith
    _ = x - 1 := by ring
  have h0 :=
    calc
    x < x + 1 := by addarith
    _ = x + 1 := by ring
  have h1337 :=
    calc
    x = x / 2 + x / 2 := by ring
    _ ≤ (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by extra
  have h13377 :=
    calc
    x = x / 2 + x / 2 := by ring
    _ ≤ (x / 2 + x / 2) + ((x - 1) / 2) ^ 2 := by extra
    _ < (x + 1) / 2 + (x + 1) / 2 + ((x - 1) / 2) ^ 2 := by rel [h0]
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

/- Cleaned up proof of Exercise 6 in section 2.5.9. -/

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by

  obtain ⟨x, h0⟩ := h
  have H := le_or_gt x 1
  obtain h1 | h1 := H

  · have h2 :=
      calc
      0 < - x * t - 1 + x + t := by addarith [h0]
      _ = (1 - x) * (t - 1) := by ring

    have h3 :=
      calc
      1 - x ≥ 1 - 1 := by rel [h1]
      _ = 0 := by ring

    cancel 1 - x at h2
    apply ne_of_gt
    addarith [h2]

  · have h2 :=
      calc
      0 < - x * t - 1 + x + t := by addarith [h0]
      _ = (x - 1) * (1 - t) := by ring

    have h3 :=
      calc
      x - 1 > 1 - 1 := by rel [h1]
      _ = 0 := by ring

    cancel x - 1 at h2
    apply ne_of_lt
    addarith [h2]

/-
This is my raw proof. It has a bunch of uneccessary filler, but I chose to
leave it here for posterity.
-/
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, h0⟩ := h
  have ayy := le_or_gt x 1

  obtain sheesh | sheesh := ayy
  · have h1 :=
      calc
      x + t = x + t := by ring
      _ ≤ 1 + t := by rel [sheesh]
      _ = 1 + t := by ring
    have h11 : x * t + 1 - x - t < 0 := by addarith [h0]
    have h111 :=
      calc
      0 > x * t + 1 - x - t := by rel [h11]
      _ = (x - 1) * (t - 1) := by ring
    have h1111 :=
      calc
       -0 < -((x - 1) * (t - 1)) := by rel [h111]
       _ = (1 - x) * (t - 1) := by ring
    have h1337 :=
      calc
      (1 - x) * (t - 1) > -0 := by rel [h1111]
      _ = 0 := by ring
    have h2 :=
      calc
      x * t + 1 < x + t := by rel[h0]
      _ ≤ 1 + t := by rel [h1]
    have h22 : x * t < t := by addarith [h2]
    have h222 : x * t - t < 0 := by addarith [h22]
    have h2222 :=
      calc
      t - x * t > 0 := by addarith [h222]
      _ = 0 := by ring
    have h3 :=
      calc
      1 - x < t - x * t := by addarith [h0]
      _ = t * (1 - x) := by ring
    have h4 :=
      calc
      1 - x = 1 - x := by ring
      _ ≥ 1 - 1 := by rel [sheesh]
      _ = 0 := by ring
    --cancel 1 - x at h3
    have h5 :=
      calc
      t * (1 - x) > 1 - x := by rel [h3]
      _ ≥ 1 - 1 := by rel [sheesh]
      _ = 0 := by ring

    cancel 1 - x at h1337

    have h6 : 1 < t := by addarith [h1337]

    apply ne_of_gt

    apply h6

  · have h1 :=
      calc
      0 > x * t + 1 - x - t := by addarith [h0]
      _ = (x - 1) * (t - 1) := by ring
    have h2 :=
      calc
      x - 1 = x - 1 := by ring
      _ > 1 - 1 := by rel [sheesh]
      _ = 0 := by ring
    have h1111 :=
      calc
       -0 < -((x - 1) * (t - 1)) := by rel [h1]
       _ = (x - 1) * (1 - t) := by ring
    have h1337 :=
      calc
      (x - 1) * (1 - t) > -0 := by rel [h1111]
      _ = 0 := by ring
    have h13 : 0 < (x - 1) * (1 - t) := by rel [h1337]

    cancel x - 1 at h13
    apply ne_of_lt

    calc
      t < 1 := by addarith [h13]

/- Failed Attempts for Exercise 6 of section 2.5.9 -/

/-
My intuition told me that dividing the case around 1 was probably a good idea. I ran
into trouble applying the 'cancel' tactic though, so I assumed I was wrong and abandoned the proof.
Then, I tried breaking the case around '0' and I was able to prove the first case, when x ≤ 0.
The second case, when x > 0, though proved impossible for me to prove. I had to spin in place for
quite a while before I realized this. I was able to prove the first case, and now all that was left
was to prove the second case, and I was determined to not give up, because after all, I was half of
the way there. Ultimately, I had to swallow my disappointment and abandon the proof. Then, I tried
to break the cases around 1 again, like I originally thought. This time I was successful in
proving not just the first case, but the second case as well.

It turns out that the cancel tactic is pretty finicky to use! It expects the expression to be
in a very particular form before letting you apply it. Your thinking is probably correct, you just
have to get in the right form.
-/

-- example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
--   obtain ⟨x, h0⟩ := h
--   have ayy := le_or_gt x 1

--   obtain sheesh | sheesh := ayy
--   · have h1 :=
--       calc
--       x + t = x + t := by ring
--       _ ≤ 1 + t := by rel [sheesh]
--       _ = 1 + t := by ring
--     have h2 :=
--       calc
--       x * t + 1 < x + t := by rel[h0]
--       _ ≤ 1 + t := by rel [h1]
--     have h22 : x * t < t := by addarith [h2]
--     have h222 : x * t - t < 0 := by addarith [h22]
--     have h2222 :=
--       calc
--       t - x * t > 0 := by addarith [h222]
--       _ = 0 := by ring
--     have h3 :=
--       calc
--       1 - x < t - x * t := by addarith [h0]
--       _ = t * (1 - x) := by ring
--     have h4 :=
--       calc
--       1 - x = 1 - x := by ring
--       _ ≥ 1 - 1 := by rel [sheesh]
--       _ = 0 := by ring
--     --cancel 1 - x at h3
--     have h5 :=
--       calc
--       t * (1 - x) > 1 - x := by rel [h3]
--       _ ≥ 1 - 1 := by rel [sheesh]
--       _ = 0 := by ring
--     cancel 1 - x at h5
--     have h6 :=
--       calc
--       x * t + 1 ≤ (1) * t + 1 := by rel [sheesh]
--       _ = t + 1 := by ring

-- example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
--   obtain ⟨x, h0⟩ := h
--   have ayy := le_or_gt x 0

--   obtain sheesh | sheesh := ayy
--   · have h1 :=
--       calc
--       x + t = x + t := by ring
--       _ ≤ 0 + t := by rel [sheesh]
--       _ = t := by ring
--     have h11 : x * t + 1 - x - t < 0 := by addarith [h0]
--     have h111 :=
--       calc
--       0 > x * t + 1 - x - t := by rel [h11]
--       _ = (x - 1) * (t - 1) := by ring
--     have h1111 :=
--       calc
--        -0 < -((x - 1) * (t - 1)) := by rel [h111]
--        _ = (1 - x) * (t - 1) := by ring
--     have h1337 :=
--       calc
--       (1 - x) * (t - 1) > -0 := by rel [h1111]
--       _ = 0 := by ring
--     have h2 :=
--       calc
--       x * t + 1 < x + t := by rel[h0]
--       _ ≤ t := by rel [h1]
--     have h22 : x * t < t := by addarith [h2]
--     have h222 : x * t - t < 0 := by addarith [h22]
--     have h2222 :=
--       calc
--       t - x * t > 0 := by addarith [h222]
--       _ = 0 := by ring
--     have h3 :=
--       calc
--       1 - x < t - x * t := by addarith [h0]
--       _ = t * (1 - x) := by ring
--     have h4 :=
--       calc
--       1 - x = 1 - x := by ring
--       _ ≥ 1 - 0 := by rel [sheesh]
--       _ = 1 := by ring
--     --cancel 1 - x at h3
--     have h5 :=
--       calc
--       t * (1 - x) > 1 - x := by rel [h3]
--       _ ≥ 1 - 0 := by rel [sheesh]
--       _ = 1 := by ring
--     cancel 1 - x at h1337
--     have h6 : 1 < t := by addarith [h1337]
--     apply ne_of_gt
--     apply h6

--   · have h1 :=
--       calc
--       0 > x * t + 1 - x - t := by addarith [h0]
--       _ = (x - 1) * (t - 1) := by ring
--     have h2 :=
--       calc
--       x - 1 = x - 1 := by ring
--       _ > 0 - 1 := by rel [sheesh]
--       _ = - 1 := by ring

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b)
    (ha' : 0 ≤ a) (hb' : 0 ≤ b) (hc' : 0 ≤ c) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
