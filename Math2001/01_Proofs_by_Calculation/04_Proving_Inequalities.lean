/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Section 1.4: Proving inequalities -/

/-
Examples from section 1.4:
Trying to solve these on my own as I work through the examples.
-/

/-Example 1.4.2 (Own attempts):-/
/-
example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = s + r - s := by ring
  _ ≤ s + (s + 3) - s := by rel[h1]
  _ ≤ s + (s + (s + r)) - s := by sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = s + r - s := by ring
  _ ≤ (s + (s + 3)) - s := by rel[h1]
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = - (s + r) + r + (s + r):= by ring
  _ ≤ - (s + r) + (r) + 3 := by rel[h2]
  _ ≤ - (s + r) + (s + 3) + 3 := by rel[h1]
  _ = - s - r + (s + 3) + 3 := by ring
  _ = - r + 3 + 3 := by ring
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = (s + r) - (s + 3) + 3 := by ring
  _ ≤ (s + r) - (r) + 3 := by rel[h1]
  _ ≤ (s + (s + 3)) - (r) + 3 := by rel[h1]
  _ = (s + (s + 3)) - (r + s) + 3 + s := by ring
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = (s + r) - (s + 3) + 3 := by ring
  _ = (s + r) - s - 3 + 3 := by ring
  _ ≤ (s + r) - s - (s + r) + 3 := by rel[h2]
  _ ≤ (s + (s + 3)) - s - (s + r) + 3 := by rel[h1]
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = (s + r) - (s + 3) + 3 := by ring
  _ = (s + r) - s - 3 + 3 := by ring
  _ ≤ (s + (s + 3)) - s - 3 + 3 := by rel[h1]
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = (s + r) - (s + 3) + 3 := by ring
  _ = (s + r) - s - 3 + 3 := by ring
  _ ≤ (s + r) - s - (s + r) + 3 := by rel[h2]
  _ ≤ (s + (s + 3)) - s - (s + r) + 3 := by rel[h1]
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = 2 * (s + r) - (s + 3) - r - s + 3 := by ring
  _ = (s + r) + (s + r) - (s + 3) - r - s + 3 := by ring
  _ ≤ (s + (s + 3)) + (s + r) - (s + 3) - r - s + 3 := by rel[h1]
  _ = s + 3 := by ring

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = 2 * (s + r) - s - r - s := by ring
  _ ≤ (s + r) + 3 - s - r - s := by rel[h2]
  _ = (s + r) + (- 2 * s + s + 3) - r - s := by ring
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = r + r - (s + r) + s:= by ring
  sorry

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = r + (s + 3) - s - 3 := by ring
  _ = (r + s) + 3 - s - 3 := by ring
-/
/-
Finally had to look at the solutions I would have never
thought to start out with a division.
-/

example
{s r : ℚ}
(h1: s + 3 ≥ r)
(h2: s + r ≤ 3) :
r ≤ 3 :=
  calc
  r = (1 / 2) * ((s + r) - s + r) := by ring
  _ ≤ (1 / 2) * (s + r - s + (s + 3)) := by rel[h1]
  _ ≤ (1 / 2) * ((3) - s + (s + 3)) := by rel[h2]
  _ = (1 / 2) * (6) := by ring
  _ ≤ (6 / 2) := by numbers
  _ ≤ 3 := by numbers

/-Example 1.4.3 (Own attempts):-/

example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  x + y = (x + 5) - (y - 5) + 2 * y - 5 := by ring



-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.2
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by sorry
    _ ≤ (3 + (s + 3) - s) / 2 := by sorry
    _ = 3 := by sorry

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  sorry

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by sorry
    _ ≤ A * B + A * B + A * v := by sorry
    _ ≤ A * B + A * B + 1 * v := by sorry
    _ ≤ A * B + A * B + B * v := by sorry
    _ < A * B + A * B + B * A := by sorry
    _ = 3 * A * B := by sorry

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by sorry
    _ ≥ 10 * t - 3 * t - 17 := by sorry
    _ = 7 * t - 17 := by sorry
    _ ≥ 7 * 10 - 17 := by sorry
    _ ≥ 5 := by sorry

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  sorry

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]


-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by sorry
    _ = 2 * (x ^ 2 + y ^ 2) := by sorry
    _ ≤ 2 * 1 := by sorry
    _ < 3 := by sorry

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by sorry
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by sorry
    _ ≤ 2 * (8 * b) + 8 * a + a := by sorry
    _ = 7 * b + 9 * (a + b) := by sorry
    _ ≤ 7 * b + 9 * 8 := by sorry
    _ = 7 * b + 72 := by sorry

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  sorry

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  sorry

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  sorry

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  sorry

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  sorry

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  sorry

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  sorry
