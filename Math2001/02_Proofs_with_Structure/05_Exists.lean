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

/-

Failed Attempts for Exercise 6 of section 2.5.9

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

/-
Inuititively, this is kind of what I wanted to do. I could see that the cases of
interest were the ones that split between the integers 2 and 3. I completely
had forgotton about le_or_succ_le up until now, and just defaulted to using
le_or_gt to split cases, because that's what worked in the previous problem.

I should be a little more careful about mindlessly applying lemmas to problems that
don't even benefit from them. In the future, try to not let a previous problem influence
your thinking in the next. Pretend that these exercises weren't grouped together.
That should help open up your thinking.
-/

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, h0⟩ := h
  have h1 := le_or_succ_le x 2

  obtain h2 | h2 := h1
  · have h3 :=
      calc
      m = 2 * x := by rw [h0]
      _ ≤ 2 * (2) := by rel [h2]
      _ = 4 := by ring
      _ < 5 := by numbers
    apply ne_of_lt
    apply h3

  · have h3 :=
      calc
      m = 2 * x := by rw [h0]
      _ ≥ 2 * (3) := by rel [h2]
      _ = 6 := by ring
      _ > 5 := by numbers
    apply ne_of_gt
    apply h3

/-

Failed Attempts for Exercise 7 of section 2.5.9

A lot like the previous problem. Proving the first case is easy, then the second
is impossible. That's probably a hint that we need to approach it differently, right
from the start.

-/

-- example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
--   obtain ⟨x, h0⟩ := h
--   have H := le_or_gt x (-1)
--   obtain h1 | h1 := H

--   have h00 : 2 * x - m = 0 := by addarith [h0]

--   have h2 :=
--     calc
--     m = 2 * x := by rw [h0]
--     2 * x ≤ 2 * -1 := by rel [h1]
--     _ = -2 := by ring
--     _ < 5 := by numbers

--   apply ne_of_lt
--   apply h2

--   have h100 : 0 = m - 2 * x := by addarith [h0]
--   have h101 : 2 * x - m = 0 := by addarith [h0]

--   have h1337 :=
--     calc
--     -x < - -1 := by rel [h1]
--     _ = 1 := by ring

--   have h2 :=
--     calc
--     2 * x ≤ 2 * x + 8 * 0 := by addarith
--     _ = 2 * x + 8 * (m - 2 * x) := by rw [h100]
--     _ = 2 * x + 8 * m + 16 * (-x) := by ring
--     _ < 2 * x + 8 * m + 16 * (1) := by rel [h1337]
--     _ = 2 * x +

-- example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
--   obtain ⟨x, h0⟩ := h
--   have H := le_or_gt x 0
--   obtain h1 | h1 := H

--   have h100 : 0 = m - 2 * x := by addarith [h0]
--   have h101 : 2 * x - m = 0 := by addarith [h0]

--   have h2 :=
--     calc
--     m = 2 * x := by rw [h0]
--     _ < 2 * x + 5 := by addarith
--     _ ≤ 2 * (0) + 5 := by rel [h1]
--     _ = 5 := by ring

--   apply ne_of_lt
--   apply h2

--   have h100 : 0 = m - 2 * x := by addarith [h0]
--   have h101 : 2 * x - m = 0 := by addarith [h0]

--   have h00 :=
--     calc
--     - x < - 0 := by rel [h1]
--     _ = 0 := by ring

--   have h2 :=
--     calc
--     2 * x ≤ 2 * x + (2 * x) ^ 2 := by extra

-- example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
--   obtain ⟨x, h0⟩ := h
--   have H := le_or_gt x 3
--   obtain h1 | h1 := H

--   have h2 :=
--     calc
--     2 * x ≤ 2 * x  + x ^ 2 := by extra
--     _ ≤ 2 * 3 + (3) ^ 2 := by rel [h1]
--     _ = 6 := by ring

--   apply ne_of_lt
--   apply h2

-- example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
--   obtain ⟨x, h0⟩ := h
--   have H := le_or_gt x 2
--   obtain h1 | h1 := H

--   have h2 :=
--     calc
--     m = 2 * x := by rw [h0]
--     _ ≤ 2 * 2 := by rel [h1]
--     _ = 4 := by ring
--     _ < 5 := by numbers

--   apply ne_of_lt
--   apply h2

--   have h2 :=
--     calc
--     2 * x > 2 * x - 2 := by addarith
--     _ > 2 * x - x := by rel [h1]
--     _ = x := by ring

-- example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
--   obtain ⟨x, h0⟩ := h
--   have H := le_or_gt x 3
--   obtain h1 | h1 := H

--   have h2 :=
--     calc
--     2 * x ≤ 2 * x  + x ^ 2 := by extra
--     _ ≤ 2 * 3 + (3) ^ 2 := by rel [h1]
--     _ = 6 := by ring

--   apply ne_of_lt
--   apply h2


/- Naive attempt at exercise 8, omegalul -/
-- example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
--   have h0 := le_or_succ_le n 0
--   use 2
--   have ay :=
--     calc
--     16 ≥ 7 := by numbers
--     _ = 7 := by ring
--   obtain h1 | h1 := h0
--   · have h00 :=
--       calc
--       n * 2 + 7 ≤ (0) * 2 + 7 := by rel [h1]
--       _ = 7 := by ring
--     have h2 :=
--       calc
--       (2 * 2 ^ 3 : ℤ) = 16 := by ring
--       _ ≥ 7 := by numbers
--       _ ≥ n * 2 + 7 := by rel [h00]
--     apply h2
--   · have h00 :=
--       calc
--       1 * 2 + 7 ≤ n * 2 + 7 := by rel [h1]

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  use n
  have h0 := le_or_succ_le n 0
  obtain h1 | h1 := h0
  have nauhgt :=
    calc
    n ^ 2 = n * n := by ring
    _ ≥ 0 * 0 := by rel [h1]

/- Exercise 9 of section 2.5.9 -/
/-
I knew something wonky would be happening here with the signs, I just didn't
know how it would work out. I was totally stumped for a while, and nothing seemed to jump
out at me as an obvious subsitution for x, y, and z.

I wrote the following down on scratch paper:

a = y + z
b = x + z
c = x + y

I noticed how z appeared in the first two equations, but not the last. I started
to think of z as an adjustor term. Something that could be added to an expression
to get the result we're looking for. I know it sounds silly, but thinking in this way is
what actually enabled me to press forward. I was completely paralyzed trying to find
the right combination of terms that prove all three equations.

I wrote down:

a = a + 0 (let y be a, let z be 0)
b = b + 0 (let x be b, let z be 0)
c = a + b (because it's defined to be x + y)

This was another kind of silly thing I did, which clearly wasn't a solution, but it clued me
into the fact that the last equation was special somehow. I needed to make sure that, whichever
a + b I chose, they had to somehow equal c when summed. The first two equations seemed 'easier'
to work with, because I had an 'adjustor' term of z which I could use to get the result I needed
from those two equations.

Up until this point, my approach consisted of trying to find a combination that worked for the
first equation, then finding another combination that worked for the second, then I would get
hard-stuck on the third. The combinations I had previously chosen worked for the first two
equations, but they trapped me into an impossible situation for the third. The scratch work
I wrote up above encouraged me to flip my approach and start working with the last equation
first, at least then the 'hard' part would be done, and I would be free to find a z term that would
'adjust' the first two equations into something useful. Again, silly, because the x and y
terms can also be thought of in this way, but this is the thinking that allowed the solution to
'fall through' for me.

I wrote down:

x = (1/2) * a - (1/2) * b + (1/2) * c
y = -(1/2) * a + (1/2) * b + (1/2) * c

This works for the last equation! If we sum these two equations, we get c, like we want.

Then I just started looking for a z that would give me what I wanted for the first two equations:

z = (1/2) * a + (1/2) * b - (1/2) * c

This was easy to find because I knew I wanted to use the z term to 'adjust' the first two equations
in such a way that the c term was always eliminated, so I knew the sign on the c term would be
negative for sure. The signs for a and b were easy to see that they would work out, because I
could just compare them with what I wrote down for x and y.

One last thing: the x and y I wrote down on in my scratch work are actually flipped to what
I ended up using in the proof. In my proof, x is actually y, and y is x.

-/

/- Cleaned up proof for exercise 9, section 2.5.9 -/
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by

    use -(1/2) * a + (1/2) * b + (1/2) * c
    use (1/2) * a - (1/2) * b + (1/2) * c
    use (1/2) * a + (1/2) * b - (1/2) * c

    constructor

    · have x1 :=
        calc
        -(1 / 2) * a + 1 / 2 * b + 1 / 2 * c = (1/2) * (-a + b + c) := by ring
        _ ≥ (1/2) * (-(b + c) + b + c) := by rel [ha]
        _ = (1/2) * (0) := by ring
        _ = 0 := by ring
      apply x1

    constructor

    · have y1 :=
        calc
        1 / 2 * a - 1 / 2 * b + 1 / 2 * c = (1/2) * (a - b + c) := by ring
        _ ≥ (1/2) * (a - (a + c) + c) := by rel [hb]
        _ = 0 := by ring
      apply y1

    constructor

    · have z1 :=
        calc
        1 / 2 * a + 1 / 2 * b - 1 / 2 * c = (1/2)  * (a + b - c) := by ring
        _ ≥ (1/2) * (a + b - (a + b)) := by rel [hc]
        _ = 0 := by ring
      apply z1

    constructor
    ring
    constructor
    ring
    ring



/- Raw, uncleaned proof for exercise 9 of section 2.5.9 -/
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by

    have huh :=
      calc
      a ≤ b + c := by rel [ha]
      _ ≤ (a + c) + c := by rel [hb]
      _ = a + 2 * c := by ring

    have duh :=
      calc
      c ≤ a + b := by rel [hc]
      _ ≤ (b + c) + b := by rel [ha]
      _ = 2 * b + c := by ring

    have bruh :=
      calc
      b ≤ a + c := by rel [hb]
      _ ≤ a + (a + b) := by rel [hc]
      _ = 2 * a + b := by ring

    have huh1 : 0 ≤ c := by addarith [huh]
    have duh1 : 0 ≤ b := by addarith [duh]
    have bruh1 : 0 ≤ a := by addarith [bruh]

    use -(1/2) * a + (1/2) * b + (1/2) * c
    use (1/2) * a - (1/2) * b + (1/2) * c
    use (1/2) * a + (1/2) * b - (1/2) * c

    constructor

    · have x1 :=
        calc
        -(1 / 2) * a + 1 / 2 * b + 1 / 2 * c = (1/2) * (-a + b + c) := by ring
        _ ≥ (1/2) * (-(b + c) + b + c) := by rel [ha]
        _ = (1/2) * (0) := by ring
        _ = 0 := by ring
      apply x1

    constructor

    · have y1 :=
        calc
        1 / 2 * a - 1 / 2 * b + 1 / 2 * c = (1/2) * (a - b + c) := by ring
        _ ≥ (1/2) * (a - (a + c) + c) := by rel [hb]
        _ = 0 := by ring
      apply y1

    constructor

    · have z1 :=
        calc
        1 / 2 * a + 1 / 2 * b - 1 / 2 * c = (1/2)  * (a + b - c) := by ring
        _ ≥ (1/2) * (a + b - (a + b)) := by rel [hc]
        _ = 0 := by ring
      apply z1

    constructor
    ring
    constructor
    ring
    ring
