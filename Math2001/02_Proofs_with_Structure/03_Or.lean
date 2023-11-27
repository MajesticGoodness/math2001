/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    2 < 2 ^ 2 := by numbers
    _ ≤ (n) ^ 2 := by rel [hn]

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h3 := h2
  have h4 : x = 1 := by addarith [h2]
  left
  calc
    x = x := by ring
    _ = 1 := by rw [h4]
  right
  have h4 : x = 2 := by addarith [h3]
  calc
    x = x := by ring
    _ = 2:= by rw [h4]

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by

  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h3 := h2
  have : x = 1 := by addarith[h2]
  have h4 : x = 1 := by addarith [h2]
  left
  calc
    x = x := by ring
    _ = 1 := by rw [h4]
  right
  have h4 : x = 2 := by addarith [h3]
  calc
    x = x := by ring
    _ = 2:= by rw [h4]

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]

/-
Playing around with Heather's proof to see what happens when I delete stuff >:)
-/
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]

/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h0 | h0 := h
  · calc
    x ^ 2 + 1 = (4) ^ 2 + 1 := by rw [h0]
    _ = (16) + 1 := by ring
    _ = 17 := by ring
  · calc
    x ^ 2 + 1 = (-4) ^ 2 + 1 := by rw[h0]
    _ = (16) + 1 := by ring
    _ = 17 := by ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h0 | h0 := h
  · calc
    x ^ 2 - 3 * x + 2 = (1) ^ 2 - 3 * (1) + 2 := by rw [h0]
    _ = 1 - 3 + 2 := by ring
    _ = 0 := by ring
  · calc
    x ^ 2 - 3 * x + 2 = (2) ^ 2 - 3 * (2) + 2 := by rw [h0]
    _ = 0 := by ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h0 | h0 := h
  · calc
    t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h0]
    _ = 0 := by ring
  · calc
    t ^ 2 - t - 6 = (3) ^ 2 - (3) - 6 := by rw [h0]
    _ = 0 := by ring

/-Not sure how to go about linking y and x so that I can go through with a
calculational proof. At minimum I feel like I should be able to say that
either y = x ∨ y ≠ x, but that would complicate things a bit. is that really
the way forward?-/

/-Nevermind, there's a small typo in the version that's up on the website
It reads:
Show that: x ^ 2 + 2 * x = 2 * y + 4

But the problem as written in Lean is actually:

Show that: x * y + 2 * x = 2 * y + 4
which is a very different problem.

So this becomes another straight substitution problem. Actually, nevermind.
The first case is easy. The second case requires a bit of thinking.
How do we get 2y + 4 from xy + 2x in the second case?

Not to complicate things, but I could potentially use an inequality and
add a square. Does 2y + 4 look like something we could get from a square?
'Cause, at the moment, xy + 2x resolves to 0 when I simply plug in y = - 2.
So, right now I can literally add anything to that and simply call it an
inequality.

Actually, nevermind. Inequalities take precedence over equalitities, so my proof
won't be in the correct form. Maybe I can still use some fact from one of the calc
blocks I've done so far.
-/
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h0 | h0 := h
  · calc
    x * y + 2 * x = (2) * y + 2 * (2) := by rw [h0]
    _ = 2 * y + 4 := by ring
  have h1 :=
    calc
    2 * y + 4 = 2 * (-2) + 4 := by rw [h0]
    _ = 0 := by ring
  · calc
    x * y + 2 * x = (x) * (-2) + 2 * x := by rw[h0]
    _ = -2 * x + 2 * x := by ring
    _ = 0 := by ring
    _ = (2 * y + 4) := by rw [h1]

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = (3 - t) + t := by rw [h]
    _ = 3 := by ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc
    b = -a / 2 + 2 * b / 2 + a / 2 := by ring
    _ = -a / 2 + (1 / 2) * (a + 2 * b) := by ring
    _ < -a / 2 + (1 / 2) * (0) := by rel [h]
    _ = -a / 2 := by ring

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  have h0 : y - 1 ≤ 2 * x := by addarith [h] -- Not sure where I was going with this.
  have h1 : y - 2 * x = 1 := by addarith [h]
  left
  calc
    x < x + 1 / 2 := by extra
    _ = x + (y - 2 * x) / 2 := by rw [h1]
    _ = y / 2 := by ring

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

example {x : ℤ} : 2 * x ≠ 3 := by
  sorry

example {t : ℤ} : 5 * t ≠ 18 := by
  sorry

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
