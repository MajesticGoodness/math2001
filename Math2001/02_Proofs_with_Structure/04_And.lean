/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1, h2⟩ := hp'
  calc
  p ≥ -3 := by rel [h1]
  _ ≥ -5 := by numbers


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra
  constructor
  cancel 2 at h2
  have h3 :=
  calc
    b ^ 2 = 0 - a ^ 2 := by addarith [h1]
    _ = 0 - (0) := by rw [h2]
    _ = 0 := by ring
  cancel 2 at h3

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ a + (3) := by rel [h2]
    _ ≤ 1 + 3 := by rel [h1]
    _ = 4 := by ring

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = (r + s) + (r - s) := by ring
    _ ≤ (1) + (r - s) := by rel [h1]
    _ ≤ 1 + (5) := by rel [h2]
    _ = 6 := by ring

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
/- We could've solved this by using addarith on h2 to subtract 5 from both sides, but
   Heather spent a lot of time showing us how to prove things the "hard" way, using
   a single, long calculational step in Chapter 1 and I felt like it's important
   to not let that effort go to waste. So, whenever it isn't too much of a pain,
   I like to try to prove things that way instead. -/
  obtain ⟨h1, h2⟩ := H
  calc
    m = m - n + n := by ring
    _ ≤ m - n + (8) := by rel[h1]
    _ = m + 5 - n + 3 := by ring
    _ ≤ (n) - n + 3 := by rel[h2]
    _ = 3 := by ring

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h1 : p ≥ 7 := by addarith [hp]
  constructor
  calc
    p ^ 2 ≥ (7) ^ 2 := by rel [h1]
    _ = 49 := by ring
  calc
    7 ≤ p := by rel [h1]
/-
There's a small typo in the exercise as it's written on the website. It is
written as:
a - 1 ≥ 6
when it should be :
a - 1 ≥ 5
-/
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h0 : a ≥ 6 := by addarith [h]
  constructor
  calc
    a ≥ 6 := by rel [h0]
    _ = 6 := by ring
  calc
    3 * a ≥ 3 * 6 := by rel [h0]
    _ = 18 := by ring
    _ ≥ 10 := by numbers

/-
I'm starting to see why Heather really wanted us to grasp calculational proofs.
They often free us of having to come up with intermediate hypothesis when
everything we need has already been laid out for us.

I was trying to work this problem in the "old" way:
Solve for x in one equation, then plug it in to the other.

It's totally doable, but it becomes somewhat cumbersome having to
create a bunch of new hypothesis like this:

have h3 : x = 5 - y := by addarith [h1]
have h4 : x + 2 * y = 5 - y + 2 * y := by rw [h3]
have h5 :=
  calc
  5 - y + 2 * y = x + 2 * y := by rw [h4]
  _ = 7 := by rw [h2
have h6 :=
  calc
  7 = 5 - y + 2 * y := by rw [h5]
  _ = 5 + y := by ring
have h7 : 2 = y := by addarith [h6]

We finally showed that y = 2, but jeez, that took a lot. By constrast,
the calculational proof is very simple and direct.

-/
example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  calc
    x = 2 * (x + y) - (x + 2 * y) := by ring
    _ = 2 * (5) - (7) := by rw [h1, h2]
    _ = 10 - 7 := by ring
    _ = 3 := by ring
  calc
    y = x + 2 * y - (x + y) := by ring
    _ = (7) - (5) := by rw [h1, h2]
    _ = 2 := by ring


/-
Finally solved it. The trick was to not narrow the goal with the 'constructor' keyword
too soon. We need to wait until we use 'obtain', otherwise we'll be left with a goal
that looks like this:

a = 0 ∧ b = 0

which is going to be impossible to solve when we 'obtain' from

a * b - a = 0
a * (b - 1) = 0

a = 0 ∨ b = 1

We're going to be able to show a = 0 easily here. Then, from a = b,
we can easily deduce that b = 0. Awesome.

But what happens when we have show that the same holds when we consider the right case, b = 1?
How can we show that a = 0 ∧ b = 0, when b = 1? It's impossible, and would contradict what
we've established so far.

What we need to do is switch the goal context to the other side of our initial goal. We do that
by calling the keywords 'left' and 'right' depending on which side we want to focus on. In this
case, we've already done what we could with the left side, so we're switching to right.

a = 1 ∧ b = 1

When we switch to this side, we're able to easily show that b = 1, from (b - 1). Not just that,
but we're also able to show that a = 1, from a = b.

The takeaway here is that working with or can be quite tricky. I remember when I was learning
a little bit of logic through Jeremy Avigad's Logic and Proof (Ch. 4, section 4.3.3 specifically)
(https://lean-lang.org/logic_and_proof/propositional_logic_in_lean.html)
that dealing with or-elimination can be kind of a headache, especially for novices like myself.
I never did fully make it through Avigad's textbook; it just felt like I wasn't learning anything
that would help me in my mathematical journey. I made to chapter 9 and I felt like I wasn't any
better off in terms of my reasoning skills, so I gave up on it. I think I wanted more of a
mathematical treatment of things, rather than a logic-based one.

-/

/- Cleaned Up Solution -/
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
    have h0 :=
      calc
      a = a * b := by rw [h1]
      _ = b := by rw [h2]
    have h3 : a * b - a = 0 := by addarith [h1]
    have h4 :=
      calc
      a * (b - 1) = a * b - a := by ring
      _ = 0 := by rw [h3]
    have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h4
    · obtain h | h := h5
      left
      constructor
      addarith [h]
      · have hb :=
          calc
          b = a := by rw [h0]
          _ = 0 := by rw [h]
        addarith [hb]
      right
      constructor
      have : b = 1 := by addarith [h]
      have ha :=
        calc
        a = b := by rw [h0]
        _ = 1 := by rw [this]
      addarith [ha]
      addarith [h]

/-
Leaving my raw, unfiltered solution below as a testament to
how working up a proof is never pretty.
-/
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
    have h0 :=
      calc
      a = a * b := by rw [h1]
      _ = b := by rw [h2]
    have h00 : a - b = 0 := by addarith [h0]
    have h3 : a * b - a = 0 := by addarith [h1]
    have h000 :=
      calc
      a = a * b := by rw [h1]
      _ = a * (a) := by rw [h0]
      _ = a ^ 2 := by ring
    have h4 :=
      calc
      a * (b - 1) = a * b - a := by ring
      _ = 0 := by rw [h3]
    have h5 : a * b - b = 0 := by addarith [h2]
    have h6 :=
      calc
      b * (a - 1) = a * b - b := by ring
      _ = 0 := by rw [h5]
    have h7 := eq_zero_or_eq_zero_of_mul_eq_zero h4
    have h8 := eq_zero_or_eq_zero_of_mul_eq_zero h6
    · obtain h999 | h999 := h7
      left
      constructor
      addarith [h999]
      have h1337 :=
        calc
        b = a := by rw [h0]
        _ = 0 := by rw [h999]
      addarith [h1337]
      right
      constructor
      have : b = 1 := by addarith [h999]
      have h907 :=
        calc
        a = b := by rw [h0]
        _ = 1 := by rw [this]
      addarith [h907]
      addarith [h999]

/-Failed Attempts on Last Exercise: -/
-- example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
--     a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
--     have h0 :=
--       calc
--       a = a * b := by rw [h1]
--       _ = b := by rw [h2]
--     have h00 : a - b = 0 := by addarith [h0]
--     have h3 : a * b - a = 0 := by addarith [h1]
--     have h000 :=
--       calc
--       a = a * b := by rw [h1]
--       _ = a * (a) := by rw [h0]
--       _ = a ^ 2 := by ring
--     have h4 :=
--       calc
--       a * (b - 1) = a * b - a := by ring
--       _ = 0 := by rw [h3]
--     have h5 : a * b - b = 0 := by addarith [h2]
--     have h6 :=
--       calc
--       b * (a - 1) = a * b - b := by ring
--       _ = 0 := by rw [h5]
--     -- have h7 :=
--     --   calc
--     --   a * (a - 1) = b * (a - 1) := by rw [h0]
--     --   _ = 0 := by rw [h6]
--     have h7 := eq_zero_or_eq_zero_of_mul_eq_zero h4
--     have h8 := eq_zero_or_eq_zero_of_mul_eq_zero h6
--     left
--     constructor
--     obtain h9 | h9 := h8
--     have :=
--       calc
--       a = b := by rw [h0]
--       _ = 0 := by rw [h9]
--     addarith [this]
--     · obtain h10 | h10 := h7
--       addarith [h10]

-- example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
--     a = 0 ∧ b = 0 := by
--     have ha :=
--       calc
--       a = a * b := by rw [h1]
--       _ = b := by rw [h2]
--     have haa :=
--       calc
--       a = a * b := by rw [h1]
--       _ = a * a := by rw [ha]
--       _ = a ^ 2 := by ring
--     have haaa : a ^ 2 - a = 0 := by addarith [haa]
--     have haaaa :=
--       calc
--       a * (a - 1) = a ^ 2 - a := by ring
--       _ = 0 := by rw [haaa]
--     have hbb :=
--       calc
--       b = a * b := by rw [h2]
--       _ = b * b := by rw [ha]
--       _ = b ^ 2 := by ring
--     have hbbb : b ^ 2 - b = 0 := by addarith [hbb]
--     have hbbbb :=
--       calc
--       b * (b - 1) = b ^ 2 - b := by ring
--       _ = 0 := by rw [hbbb]
--     have hA := eq_zero_or_eq_zero_of_mul_eq_zero haaaa
--     have hB := eq_zero_or_eq_zero_of_mul_eq_zero hbbbb
--     constructor
--     · obtain h0 | h0 := hA
--       addarith [h0]
--     · obtain h3 | h3 := hB
--     -- calc
--     --   a = b := by rw [ha]
--     --   _ = 0 := by rw [h3]

/-
I'm at a stand-still here. I can't seem to find a way to reconcile these two
equations:

ab - a = 0
a(b - 1) = 0
a = 0 v b = 1

I need to show that a = 0 in both cases. The left case is easy.
The right case is impossible lol. We established that a = b, so
how can it be that when b = 1, a = 0? This problem might become do-able
if I can establish that a = 0, or a = 1, or b = 0, or b = 1, before I
ever begin to use the obtain keyword. I'll think about it, but I don't
really see an easy way to do that at the moment.

ab - b = 0
b(a - 1) = 0
b = 0 v a = 1

Working with this equation results in the same problemo as above.

-/

-- example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
--     a = 0 ∧ b = 0 := by
--     have h :=
--       calc
--       a = a * b := by rw [h1]
--       _ = b := by rw [h2]
--     have h0 :=
--       calc
--       a = a * b := by rw [h1]
--       _ = a * a := by rw [h]
--       _ = a ^ 2 := by ring
--     have ha : a * b - a = 0 := by addarith [h1]
--     have haa :=
--       calc
--       a * (a - 1) = a * a - a := by ring
--       _ = a * b - a := by rw [h]
--       _ = 0 := by rw [ha]
--     have hA := eq_zero_or_eq_zero_of_mul_eq_zero haa
--     have h3 : a ^ 2 = 1
--     · apply le_antisymm
--       obtain h4 | h4 := hA
--       calc
--         a ^ 2 ≤ a ^ 2 + 0 ^ 2 := by extra
--         _ = a ^ 2 := by ring
--         _ = (0) ^ 2 := by rw [h4]
--         _ ≤ 1 := by numbers
--       calc
--         a ^ 2 ≤ a ^ 2 + (a - 1) ^ 2 := by extra
--         _ = 2 * (a ^ 2) - 2 * a + 1 := by ring
--         _ = 2 * a ^ 2 - a - a + 1 := by ring
--         _ = 2 * a * (a - 1) + 1 := by ring
--         _ = 2 * a * (0) + 1 := by rw [h4]
--         _ = 1 := by ring

/-End Failed Ateempts-/
