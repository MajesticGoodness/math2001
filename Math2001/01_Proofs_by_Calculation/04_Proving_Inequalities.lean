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
  x + y = (x - 2) / 2 + (x + 5) / 2 + y - (3 / 2) := by ring
  _ := sorry

example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  x + y = (2 - y) + (2 - x) + 2 * (x + y) - 4 := by ring
  _ := sorry

example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  x + y = ((2 - y) + (-x - (-2))) / 2 + (3 / 2) * (x + y) - 2 := by ring
  _ ≤ ((2 - y) + (-x - x)) / 2 + (3 / 2) * (x + y) - 2 := by rel[h2]
  _ = ((2 - y) - 2 * x) / 2 + (3 / 2) * (x + y) - 2 := by ring
  _ = (2 / 2) - (y / 2) - x + (3 * x) / 2 + (3 * y) / 2 - 2 := by ring
  _ = (2 / 2) + (y) - x + (3 * x) / 2 - 2 := by ring
  _ ≤ (2 / 2) + (x + 5) - x + (3 * x) / 2 - 2 := by rel[h1]
  _ = (2 / 2) + 5 + (3 * x) / 2 - 2 := by ring
  _ ≤ (2 / 2) + 5 + (3 * (-2)) / 2 - 2 := by rel[h2]
  _ = (2 / 2) + 5 - 6 / 2 - 2 := by ring
  _ = (2 / 2) + 5 - 3 - 2 := by ring
  _ := sorry

/-
Reversing the second inequality wasn't working the way I expected.
It turns out you just have to be really particular about the way you write it in Lean.

I had written down (just as some random scratch work):
1. -x + 2
2. ≤ -x (-x) using the fact that x ≤ - 2 becomes - x ≥ 2 when subtracted.


I tried to do that in Lean, but you really have to make it clear that you're
subtracting a term, not just negating it with a -1. The example directly below shows
how to write it so Lean accepts it.
-/
/-
example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  2 - x = - x - (-2) := by ring
  _ ≤ - x - x := by rel[h2]
  sorry

example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  x + y = (2 - x) / 2 + (3 / 2) * (x + 5) + y - 17 / 2 := by ring
  sorry

example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  x + y = (2 - x) / 2 + (3 * (x + y)) / 2 + (2 - y) / 2 - 2 := by ring
  sorry
-/

example
{x y : ℝ}
{h1: y ≤ x + 5}
{h2: x ≤ -2} :
x + y < 2 :=
  calc
  x + y = x + y := by ring
  _ ≤ x + (x + 5) := by rel[h1]
  _ = 2 * x + 5 := by ring
  _ ≤ 2 * (-2) + 5 := by rel[h2]
  _ < 2 := by numbers /-Didn't know you could do this lol-/

/-Example 1.4.4 (Own Attempts)-/
example
{A B x y u v : ℝ}
{h1: 0 < A}
{h2: A ≤ 1}
{h3: B ≥ 1}
{h4: x ≤ B}
{h5: y ≤ B}
{h6: 0 ≤ u}
{h7: u < A}
{h8: 0 ≤ v}
{h9: v < A} :
u * y + v * x + u * v ≤ 3 * A * B
:=
  calc
  u * y + v * x + u * v = u * y + v * x + u * v := by ring
  _ ≤ u * y + v * x + A * v := by rel [h7, h8]
  _ ≤ u * (B) + v * x + A * v := by rel[h5]
  _ < (A) * B + v * x + A * v := by rel[h7]
  _ ≤ A * B + v * (B) + A * v := by rel[h4]
  _ < A * B + (A) * B + A * A := by rel[h9]
  _ ≤ A * B + A * B + (1) * A := by rel[h2]
  _ ≤ A * B + A * B + (1) * (1) := by rel[h2]
  _ = A * B + A * B + 1 := by ring
  _ ≤ A * B + A * B + (B) := by rel[h3]
  _ = 2 * (A * B) + B := by ring
  _ = := by sorry

example
{A B x y u v : ℝ}
{h1: 0 < A}
{h2: A ≤ 1}
{h3: B ≥ 1}
{h4: x ≤ B}
{h5: y ≤ B}
{h6: 0 ≤ u}
{h7: u < A}
{h8: 0 ≤ v}
{h9: v < A} :
u * y + v * x + u * v ≤ 3 * A * B
:=
  calc
  u * y + v * x + u * v = u * y + v * x + u * v := by ring
  _ ≤ u * y + v * x + A * v := by rel [h7, h8]
  _ ≤ u * (B) + v * x + A * v := by rel[h5]
  _ < (A) * B + v * x + A * v := by rel[h7]
  _ ≤ A * B + v * (B) + A * v := by rel[h4]
  _ < A * B + (A) * B + A * A := by rel[h9]
  _ ≤ A * B + A * B + (1) * A := by rel[h2]
  _ ≤ A * B + A * B + (1) * (1) := by rel[h2]
  _ = A * B + A * B + 1 := by ring
  _ ≤ A * B + A * B + (B) := by rel[h3]
  _ = 2 * (A * B) + B := by ring
  _ = := by sorry

example
{A B x y u v : ℝ}
{h1: 0 < A}
{h2: A ≤ 1}
{h3: B ≥ 1}
{h4: x ≤ B}
{h5: y ≤ B}
{h6: 0 ≤ u}
{h7: u < A}
{h8: 0 ≤ v}
{h9: v < A} :
u * y + v * x + u * v ≤ 3 * A * B
:=
  calc
  u * y + v * x + u * v = u * y + v * x + u * v := by ring
  _ ≤ u * y + v * x + A * v := by rel [h7, h8]
  _ ≤ u * (B) + v * x + A * v := by rel[h5]
  _ < (A) * B + v * x + A * v := by rel[h7]
  _ ≤ A * B + v * (B) + A * v := by rel[h4]
  _ < A * B + (A) * B + A * A := by rel[h9]
  _ ≤ A * B + A * B + (1) * A := by rel[h2]
  _ = := sorry

/-Final solution for 1.4.4: -/
example
{A B x y u v : ℝ}
{h1: 0 < A}
{h2: A ≤ 1}
{h3: B ≥ 1}
{h4: x ≤ B}
{h5: y ≤ B}
{h6: 0 ≤ u}
{h7: u < A}
{h8: 0 ≤ v}
{h9: v < A} :
u * y + v * x + u * v < 3 * A * B
:=
  calc
  u * y + v * x + u * v = u * y + v * x + u * v := by ring
  _ ≤ u * y + v * x + A * v := by rel [h7, h8]
  _ ≤ u * (B) + v * x + A * v := by rel[h5]
  _ < (A) * B + v * x + A * v := by rel[h7]
  _ ≤ A * B + v * (B) + A * v := by rel[h4]
  _ < A * B + (A) * B + A * A := by rel[h9]
  _ ≤ A * B + A * B + (1) * A := by rel[h2]
  _ ≤ A * B + A * B + (B) * A := by rel[h3]
  _ = 3 * A * B := by ring

/-Example 1.4.5 (Own attempts):-/
example
{t : ℝ}
{h1: t ≥ 10} :
t ^ 2 - 3 * t + 17 ≥ 5
:=
  calc
  t ^ 2 - 3 * t + 17 = t * t - 3 * t + 17 := by ring
  _ ≥ (10) * t - 3 * t + 17 := by rel[h1]
  _ = 7 * t + 17 := by ring
  _ ≥ 7 * (10) + 17 := by rel[h1]
  _ = 70 + 17 := by ring
  _ = 87 := by ring
  _ ≥ 5 := by numbers

/-Example 1.4.6 (Own attempts):-/
example
{n : ℤ}
{h1 : n ≥ 5} :
n ^ 2 ≥ 2 * n + 11 :=
  calc
  n ^ 2 = n * n := by ring
  _ ≥ (5) * n := by rel [h1]
  _ ≥ 5 * n + 11 := by rel [h1]
  _ :=sorry

example
{n : ℤ}
{h1 : n ≥ 5} :
n ^ 2 ≥ 2 * n + 11 :=
  calc
  n ^ 2 = n * n + 5 - 5 := by ring
  _ ≥ (5) * n + 5 - 5 := by rel [h1]
  _ ≥ (5) * n + 5 - n := by rel [h1]
  _ = 4 * n + 5 := by ring
  _ := sorry

/-Final Solution for 1.4.6 (I think?)-/
example
{n : ℤ}
{h1 : n ≥ 5} :
n ^ 2 > 2 * n + 11 :=
  calc
  n ^ 2 = n * n + 15 - 15 := by ring
  _ ≥ (5) * n + 15 - 15 := by rel [h1]
  _ = (5) * n + 15 - 5 - 5 - 5 := by ring
  _ ≥ (5) * n + 15 - n - n - n := by rel [h1]
  _ = 2 * n + 11 + 4 := by ring
  _ > 2 * n + 11 := by extra -- Learned to use 'extra' after looking at example 1.4.7

/-Example 1.4.7 (Own attempts):-/
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
  n = m ^ 2 + n - m ^ 2:= by ring
  _ ≤ (2) - m ^ 2 := by rel[h]
  _ ≤ 2 := by sorry

/-Example 1.4.8 (Own attempts):-/
example
{x y : ℝ}
{h1 : x ^ 2 + y ^ 2 ≤ 1} :
(x + y) ^ 2 < 3 :=
  calc
  (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
  _ = 2 * (x ^ 2 + y ^ 2) := by ring
  _ ≤ 2 * (1) := by rel [h1]
  _ = 2 := by ring
  _ < 3 := by numbers

/-Example 1.4.9 (Own attempts):-/
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
      calc
      3 * a * b + a ≤ 3 * a * b + a + (7 * b + 9 * (a + b)):= by extra
      _ = 3 * a * b + a + 7 * b + 9 * (a + b) := by ring
      _ ≤ 3 * a * b + a + 7 * b + 9 * (8) := by rel [h3]
      _ = 3 * a * b + a + 7 * b + 72 := by ring
      _ = 7 * b + 72 + 3 * a * b + a := by ring
      _ ≤ 7 * b + 72 := by extra -- Nice try lmao
      _ := sorry

example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
      calc
      3 * a * b + a ≤ 3 * a * b + a

/-
Let a and b be nonnegative rational numbers, and suppose that a + b ≤ 8.
Show that 3ab + a ≤ 7b + 72

Solution:
3ab + a ≤ 2b^2 + a^2 + (3ab + a)
= 2(a + b)b + (a + b)a + a
≤ 2 * 8b + 8a + a
= 7b + 9(a + b)
≤ 7b + 9 * 8
= 7b + 72.
-/

/-Example 1.4.10
I attempted for a bit to come up with my own squares to add but quickly got lost.
I then looked at Heather's squares, and attempted to come up with a solution using them.
In general, it looks like you want to add squares that give you at least two terms that
you actually want. It's fine if the square you add gives you one term you don't want;
you can always find a way to get rid of it. But, if you add a square that only gives
you one term you actually want, and two other terms you don't, then your life becomes
harder. You might actually still be able to pull it off, just with a lot more effort.
Actually, I haven't tested if that's true. You might just end up in a loop of
continously adding squares and never ending up where you want.

The square I came up with was: (a^2 - b^3 * c^3) ^ 2. I wanted to desperately get
rid of the 8 * a^2 * b^3 * ^c3 term first. While my square did that, it also
introduced two erroneous terms I did not want: b ^ 6 and c ^ 6. I ended up getting
rid of one thing I did not want, and ended with two things I don't want! Not a great
trade imo.

  + (b ^ 4 - c ^ 4) ^ 2
  + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2:
-/
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
  a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) = a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3
  := by ring
  _ ≤ a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3 + 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2
  := by extra
  _ = a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3
      + 2 * a ^ 4 * b ^ 4 - 4 * a ^ 4 * b ^ 2 * c ^ 2 + 2 * a ^ 4 * c ^ 4
      := by ring
  _ ≤ a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3
      + 2 * a ^ 4 * b ^ 4 - 4 * a ^ 4 * b ^ 2 * c ^ 2 + 2 * a ^ 4 * c ^ 4
      + (b ^ 4 - c ^ 4) ^ 2
      := by extra
  _ = a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3
      + 2 * a ^ 4 * b ^ 4 - 4 * a ^ 4 * b ^ 2 * c ^ 2 + 2 * a ^ 4 * c ^ 4
      + b ^ 8 - 2 * b ^ 4 * c ^ 4 + c ^ 8
      := by ring
  _ ≤ a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3
      + 2 * a ^ 4 * b ^ 4 - 4 * a ^ 4 * b ^ 2 * c ^ 2 + 2 * a ^ 4 * c ^ 4
      + b ^ 8 - 2 * b ^ 4 * c ^ 4 + c ^ 8
      + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
      := by extra
  _ = a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3
      + 2 * a ^ 4 * b ^ 4 - 4 * a ^ 4 * b ^ 2 * c ^ 2 + 2 * a ^ 4 * c ^ 4
      + b ^ 8 - 2 * b ^ 4 * c ^ 4 + c ^ 8
      + 4 * a ^ 4 * b ^ 2 * c ^ 2 - 8 * a ^ 2 * b ^ 3 * c ^ 3 + 4 * b ^ 4 * c ^ 4
      := by ring
  _ = a ^ 8 + b ^ 8 + c ^ 8 + 2 * a ^ 4 * b ^ 4 + 2 * a ^ 4 * c ^ 4 + 2 * c ^ 4 * b ^ 4 := by ring
  _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


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
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h1, h2]
    _ = 3 := by ring

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
  x + y = x + y := by ring
  _ ≤ x + (x + 5) := by rel[h1]
  _ = 2 * x + 5 := by ring
  _ ≤ 2 * (-2) + 5 := by rel[h2]
  _ < 2 := by numbers /-Didn't know you could do this lol-/

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h4, h5]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ ≥ 5 := by numbers

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
  n ^ 2 = n * n := by ring
  _ ≥ 5 * n := by rel [hn]
  _ = 2 * n + 3 * n := by ring
  _ ≥ 2 * n + 3 * (5) := by rel [hn]
  _ = 2 * n + 15 := by ring
  _ = 2 * n + 11 + 4 := by ring
  _ > 2 * n + 11 := by extra

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]

-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by numbers

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel [h3]
    _ = 7 * b + 72 := by ring

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
  calc
  x = x + 3 - 3 := by ring
  _ ≥ 2 * (y) - 3 := by rel [h1]
  _ ≥ 2 * (1) - 3 := by rel [h2]
  _ = 2 - 3 := by ring
  _ = -1 := by ring

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
  a + b = (1 / 2) * (a + 2 * b) + (1 / 2) * a := by ring
  _ ≥ (1 / 2) * (4) + (1 / 2) * a := by rel [h2]
  _ = 2 + (1 / 2) * a := by ring
  _ ≥ 2 + (1 / 2) * (3) := by rel [h1]
  _ = 3 + (1 / 2) := by ring
  _ ≥ 3 := by numbers

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
  x ^ 3 - 8 * x ^ 2 + 2 * x = (x ^ 3 + 2 * x) - 8 * x ^ 2 := by ring
  _ = x * (x ^ 2 + 2) - 8 * x ^ 2 := by ring
  _ ≥ (9) * (x ^ 2 + 2 ) - 8 * x ^ 2 := by rel [hx]
  _ = 9 * x ^ 2 + 18 - 8 * x ^ 2 := by ring
  _ = x ^ 2 + 18 := by ring
  _ ≥ (9) ^ 2 + 18 := by rel [hx]
  _ = 81 + 18 := by ring
  _ = 99 := by ring
  _ ≥ 3 := by numbers

/- Attempts for exercise 4 that didn't quite get us there:

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc
  n ^ 4 - 2 * n ^ 2 = n ^ 4 - 2 * n ^ 2 := by ring
  _ ≥ (10) ^ 4 - 2 * n ^ 2 := by rel [hn]
  _ ≥ (10) ^ 4 - 2 * (10) ^ 2 := by sorry

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc
  n ^ 4 - 2 * n ^ 2 = n ^ 4 - 2 * n ^ 2  + 3 * 10 ^ 3 - 3 * 10 ^ 3:= by ring
  _ = n ^ 2 * (n ^ 2 - 2) + 3 * 10 ^ 3 - 3 * 10 ^ 3 := by ring
  _ ≥ (10) ^ 2 * ((10) ^ 2 - 2) + 3 * 10 ^ 3 - 3 * 10 ^ 3 := by rel [hn]
  _ = 9800 + 3 * 10 ^ 3 - 3 * 10 ^ 3 := by ring
  _ = 3 * 10 ^ 3 + 6800 := by ring
  _ ≥ 3 * (n) ^ 3 + 6800 := by sorry

-/
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc
  n ^ 4 - 2 * n ^ 2 = n ^ 4 - 10 * n ^ 2 + 8 * n ^ 2 := by ring
  _ ≥ n ^ 4 - (n) * n ^ 2 + 8 * n ^ 2 := by rel [hn]
  _ = n ^ 3 * (n - 1) + 8 * n ^ 2 := by ring
  _ ≥ n ^ 3 * ((10) - 1) + 8 * n ^ 2 := by rel [hn]
  _ = n ^ 3 * (9) + 8 * n ^ 2 := by ring
  _ = 3 * n ^ 3 + 6 * n ^ 3 + 8 * n ^ 2 := by ring
  _ ≥ 3 * n ^ 3 + 6 * (10) ^ 3 + 8 * n ^ 2 := by rel [hn]
  _ ≥ 3 * n ^ 3 + 6 * (10) ^ 3 + 8 * (10) ^ 2 := by rel [hn]
  _ = 3 * n ^ 3 + 6000 + 800 := by ring
  _ = 3 * n ^ 3 + 6800 := by ring
  _ > 3 * n ^ 3 := by extra

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
  n ^ 2 - 2 * n + 3 = n ^ 2 - 2 * n + 3 := by ring
  _ = n * (n - 2) + 3 := by ring
  _ ≥ n * (5 - 2) + 3 := by rel [h1]
  _ = n * (3) + 3 := by ring
  _ ≥ (5) * (3) + 3 := by rel [h1]
  _ = 15 + 3 := by ring
  _ = 18 := by ring
  _ > 14 := by numbers

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
  x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 := by ring
  _ ≥ -1 := by extra

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
  a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring
  _ ≥ 2 * a * b := by extra
