/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
  a = 2 * b + 5 := by rw[h1]
  _ = (2 * 3) + 5 := by rw[h2]
  _ = 6 + 5 := by ring
  _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
  x = x + 4 - 4 := by ring
  _ = 2 - 4 := by rw[h1]
  _ = -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
  a = a - (5 * b) + (5 * b) := by ring
  _ = 4 + (5 * b) := by rw[h1]
  _ = 4 + (5 * b) + (5 * (b + 2)) - (5 * (b + 2)) := by ring
  _ = 4 + (5 * b) + (5 * (3)) - (5 * (b + 2)) := by rw[h2]
  _ = 4 + (5 * b) + 15 - (5 * (b + 2)) := by ring
  _ = 4 + (5 * b) + 15 - 5 * b - 10 := by ring
  _ = 15 - 10 + 4 + (5 * b) - (5 * b) := by ring
  _ = 15 - 10 + 4 := by ring
  _ = 9 := by ring

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
  w = (3 * w + 1 ) / 3 - (1 / 3) := by ring
  _ = 4 / 3 - 1 / 3 := by rw[h1]
  _ = 1 := by ring

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
  x = 2 * x - x := by ring
  _ = 2 * x - (2 * x + 3) := by rw[h1]
  _ = 2 * x - 2 * x - 3 := by ring
  _ = -3 := by ring

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
  x = (2 * x - y) + (y - x + 1) - 1 := by ring
  _ = 4 + (y - x + 1) - 1 := by rw[h1]
  _ = 4 + 2 - 1 := by rw[h2]
  _ = 5 := by ring

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
  u = (u + 2 * v) / 2 + (u - 2 * v) / 2 := by ring
  _ = (4) / 2 + (u - 2 * v) / 2 := by rw[h1]
  _ = (4) / 2 + (6) / 2 := by rw[h2]
  _ = 2 + 3 := by ring
  _= 5 := by ring

-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
  x = (5 * x - 3 * y) / 8 + (3 * (x + y) / 8) := by ring
  _ = (4) / 8 + 3 * (x + y) / 8 := by rw[h2]
  _ = (4) / 8 + 3 * (4) / 8 := by rw[h1]
  _ = (4) / 8 + 12 / 8 := by ring
  _ = 16 / 8 := by ring
  _ = 2 := by ring

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
  a ^ 2 - a + 3 = ((a-3) ^ 2 + 6 * a - 9 ) - a + 3 := by ring
  _ = ((a-3) ^ 2 + 3 * (2 * a - 3) - a + 3) := by ring
  _ = ((a-3) ^ 2 + 3 * (2 * a - 3)) - (a - 3) := by ring
  _ = ((a-3) ^ 2 - (a - 3) + 3 * (2 * a - 3)) := by ring
  _ = ((a-3) * ((a - 3) - 1) + 3 * (2 * a - 3)) := by ring
  _ = (a-3) * (a - 4) + 3 * (2 * a - 3) := by ring
  _ = (a ^ 2) - (3 * a) - (4 * a) + 12 + 3 * (2 * a - 3) := by ring
  _ = (a ^ 2) - (3 * a) - (4 * a) + 12 + (6 * a) - 9 := by ring
  _ = (a ^ 2) - (6 * a) - a + 12 + (6 * a) - 9 := by ring
  _ = (a ^ 2) - (6 * a) + 9 - a + (6 * a) - 6 := by ring
  _ = (a - 3) ^ 2 - a + (6 * a) - 6 := by ring
  _ = (2 * b) ^ 2 - a + (6 * a) - 6 := by rw[h1]
  _ = (2 * b) ^ 2 + (2 * a) - 6 + (4 * a) - a := by ring
  _ = (2 * b) ^ 2 + 2 * (a - 3) + (4 * a) - a := by ring
  _ = (2 * b) ^ 2 + 2 * (a - 3) + (4 * a) - a + 3 * (a - 3) - 3 * (a - 3) := by ring
  _ = (2 * b) ^ 2 + 5 * (a - 3) + (4 * a) - a - 3 * (a - 3) := by ring
  _ = (2 * b) ^ 2 + 5 * (2 * b) + (4 * a) - a - 3 * (a - 3) := by rw[h1]
  _ = (2 * b) ^ 2 + (10 * b) + (4 * a) - a - (3 * a) + 9 := by ring
  _ = (2 * b) ^ 2 + (10 * b) + (4 * a) - (4 * a) + 9 := by ring
  _ = (2 * b) ^ 2 + (10 * b) + 9 := by ring
  _ = 4 * b ^ 2 + (10 * b) + 9 := by ring

example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
  a ^ 2 - a + 3 = ((a-3) ^ 2 + 6 * a - 9 ) - a + 3 := by ring
  _ = (a-3) ^ 2 + (3 * a) - 9 - a + 3 + (3 * a) := by ring
  _ = (a-3) ^ 2 + 3 * (a - 3) - a + 3 + (3 * a) := by ring
  _ = (a - 3) ^ 2 + 3 * (a - 3) - a + 3 + (3 * a) + 2 * (a - 3) - 2 * (a - 3) := by ring
  _ = (a - 3) ^ 2 + 5 * (a - 3) - a + 3 + (3 * a) - 2 * (a - 3) := by ring
  _ = (a - 3) ^ 2 + 5 * (a - 3) - a + 3 + (3 * a) - (2 * a) + 6 := by ring
  _ = (a - 3) ^ 2 + 5 * (a - 3) + 3 + (2 * a) - (2 * a) + 6 := by ring
  _ = (a - 3 ) ^ 2 + 5 * (a - 3) + 3 + 6 := by ring
  _ = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
  _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw[h1]
  _ = 4 * b ^ 2 + 10 * b + 9 := by ring

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
  z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 + 4 - 4 := by ring
  _ = z ^ 4 - 4 - z ^ 3 - z ^ 2 + 2 * z + 1 + 4 := by ring
  _ = (z ^ 2 - 2) * (z ^ 2 + 2) - z ^ 3 - z ^ 2 + 2 * z + 1 + 4 := by ring
  _ = (z ^ 2 - 2) * (z ^ 2 + 2) - z * (z ^ 2 - 2) - z ^ 2 + 1 + 4 := by ring
  _ = (0) * (z ^ 2 + 2) - z * (0) - z ^ 2 + 1 + 4 := by rw[h1]
  _ = - z ^ 2 + 2 + 1 + 2 := by ring
  _ = - (z ^ 2 - 2) + 3 := by ring
  _ = - (0) + 3 := by rw[h1]
  _ = 3 := by ring

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
  y = 4 * x - 3 := by rw[h2]
  _ = 4 * 3 - 3 := by rw[h1]
  _ = 12 - 3 := by ring
  _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
  a = a - b + b := by ring
  _ = 0 + b := by rw[h]
  _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
  x = x - 3 * y + 3 * y := by ring
  _ = 5 + 3 * y := by rw[h1]
  _ = 5 + 3 * 3 := by rw[h2]
  _ = 5 + 9 := by ring
  _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
  p =  p - 2 * q + 2 * q := by ring
  _ = 1 + 2 * q := by rw[h1]
  _ = 1 + 2 * (-1) := by rw[h2]
  _ = 1 - 2 := by ring
  _ = - 1 := by ring


example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
  x = x + 2 * y - 2 * (y + 1) + 2 := by ring
  _ = x + 2 * y - 2 * (3) + 2 := by rw[h1]
  _ = 3 - 2 * (3) + 2 := by rw[h2]
  _ = 3 - 6 + 2 := by ring
  _ = - 3 + 2 := by ring
  _ = - 1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
  p = p + 4 * q - 4 * (q - 1) - 4 := by ring
  _ = p + 4 * q - 4 * (2) - 4 := by rw[h2]
  _ = p + 4 * q - 8 - 4 := by ring
  _ = 1 - 8 - 4 := by rw[h1]
  _ = -11 := by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
  a = a + 2 * b + 3 * c - 2 * (b + 2 * c) + c := by ring
  _ = 7 - 2 * (b + 2 * c) + c := by rw[h1]
  _ = 7 - 2 * (3) + c := by rw[h2]
  _ = 7 - 2 * (3) + 1 := by rw[h3]
  _ = 7 - 6 + 1 := by ring
  _ = 2 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
  u = (1 / 4) * (4 * u + v) - (1 / 4) * v := by ring
  _ = (1 / 4) * (3) - (1 / 4) * v := by rw[h1]
  _ = (1 / 4) * (3) - (1 / 4) * 2 := by rw[h2]
  _ = (3 / 4) - (2 / 4) := by ring
  _ = (1 / 4) := by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
  c = 4 * c + 1 - (3 * c - 2) - 3 := by ring
  _ = (3 * c - 2) - (3 * c - 2) - 3 := by rw[h1]
  _ = - 3 := by ring

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  calc
  p = (1 / 2) * (5 * p - 3) - (1 / 2) * (3 * p + 1) + 2 := by ring
  _ = (1 / 2) * (5 * p - 3) - (1 / 2) * (5 * p - 3) + 2 := by rw[h1]
  _ = 2 := by ring

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
  x = (2 * x) + y - (x + y) := by ring
  _ = 4 - (x + y) := by rw[h1]
  _ = 4 - 1 := by rw[h2]
  _ = 3 := by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
  a = (a + 2 * b) / 3 + (2 / 3) * (a - b) := by ring
  _ = (4) / 3 + (2 / 3) * (a - b) := by rw[h1]
  _ = (4) / 3 + (2 / 3) * (1) := by rw[h2]
  _ = 4 / 3 + 2 / 3 := by ring
  _ = 6 / 3 := by ring
  _ = 2 := by ring

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
  u ^ 2 + 3 * u + 1 = (u + 1) ^ 2 + u := by ring
  _ = v ^ 2 + u:= by rw[h1]
  _ = v ^ 2 + u + 1 - 1 := by ring
  _ = v ^ 2 + (u + 1) - 1 := by ring
  _ = v ^ 2 + v - 1 := by rw[h1]

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
  t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
  = t ^ 4 - 16 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 + 16 := by ring
  _ = (t ^ 2 - 4) * (t ^ 2 + 4) + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 + 16 := by ring
  _ = (0) * (t ^ 2 + 4) + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 + 16 := by rw[ht]
  _ = 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 + 16 := by ring
  _ = 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 + 16 - 10 * t + 10 * t := by ring
  _ = 3 * t ^ 3 - 12 * t - 3 * t ^ 2 - 2 + 16 + 10 * t := by ring
  _ = 3 * t * (t ^ 2 - 4) - 3 * t ^ 2 - 2 + 16 + 10 * t := by ring
  _ = 3 * t * (0) - 3 * t ^ 2 - 2 + 16 + 10 * t := by rw[ht]
  _ = -3 * t ^ 2 - 2 + 16 + 10 * t := by ring
  _ = -3 * t ^ 2 + 12 + 4 - 2 + 10 * t := by ring
  _ = -3 * (t ^ 2 - 4) + 4 - 2 + 10 * t := by ring
  _ = -3 * (0) + 4 - 2 + 10 * t := by rw[ht]
  _ = 4 - 2 + 10 * t := by ring
  _ = 2 + 10 * t := by ring
  _ = 10 * t + 2 := by ring

/-
Failed Attempts on exercise 15. It really kicked my ass!

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
  y = y * x + 3 * y + 2 * x - y * x - 2 * y - 2 * x := by ring
  _ = - (2 * x - y * x) + 3 * y + 2 * x - y * x - 2 * y := by ring

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
  y = y / 3 * (x + 3) - y * x / 3 + 2 * x / 3 - 2 * x / 3 := by sorry

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
  y = (1 / x) * (0) + y := by ring
  _ = (1 / x) * (2 * x - y * x) + y := by rw[h2]
  _ = x * x⁻¹ * 2 - x * x⁻¹ * y + y := by ring
  _ = 2 - y + y := by sorry

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
  y = 0 / (5 - 3) + y + 2 - 2 := by ring
  _ = 0 / (x + 3 - 3) + y + 2 - 2 := by rw[h1]
  _ = 0 / (x) + y + 2 - 2 := by ring
  _ = (0 - 2 * x + 2 * x) / (x) + y := by ring

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
  y = (1 / x) * (0) + y - 2 + 2 := by ring
  _ = (1 / x) * (2 * x - y * x) + y - 2 + 2 := by rw[h2]
  _ = (2 * x - y * x) / x + (y - 2) + 2 := by ring
  _ = 2 * x / x - y * x / x + y * x / x - 2 * x / (x) + 2 := by sorry

-/
/-
It wasn't immediately obvious to me hat you could take
advantage of subsitution by simplying rewriting x as (x + 3 - 3).
I kept trying to find a way retrieve a y term out of (2x - yx)
by multiplying it by (1 / x). It turns out you can't actually
perform that distribution, because x might be 0. So it was back
to the drawing board for me. Then, I started to multiply the
(x + 3) term by y, to hopefully get a y that way instead.
That turned out to be a dead end too, and I knew it in my gut
while I was doing it; I just didn't know what else to try.

Ultimately after I realized I wasn't ever going to get anywhere
with those kinds of manipulations. I returned to the
equations given:
1. x + 3 = 5
2. 2x - yx = 0

I traced the "moves" you go through when you solve this the usual way.
1. Solve for x, so that you find x = 2
2. Substitute that x into the second equation.
3. Solve the second equation, which is now only in terms of y.

As I worked this out, that substitution step was what really caught
my attention. I asked myself "How can we map that substitution step to
an algebraic manipulation in the proof?" I started to mess around
with 2x - yx = 0 on a piece of scrap paper and wrote the following:

Question: How can we write x as a substitution?
2x - xy = 2(x + 3 - 3) - (x + 3 - 3)y
        = 2(5 - 3) - (5 - 3)y
        = 2(2) - (2)y
        = 4 - 2y

Looking at the way this worked out clued me in. I finally
had a constant, and a y term on its own. Now, all I needed
to do was bring that 4 down to a 2, and bring that y down to
only a single y, so that I could have something like:

2 - y

But how do we do that? Looking at

4 - 2y

we can see that they're both divisble by 2, so perhaps starting
out our proof by (1 / 2) * (2x - yx) will work! This will leave us:

2 - y

Now we are even closer to our proof. We just have to add a y term
and we'll be left with just 2, which is what we want! So we add a
y term at the start of the proof. Now the start of our proof looks
like this:

(1 / 2) * (2x - yx) + y

Nice. This works out to just 2. Awesome! It's just what we need.
Now we just remember that we can rewrite (2x - yx) as 0 and it
becomes the perfect way to start our proof.

y = (1 / 2) * (0) + y
-/

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
  y = (1 / 2) * (0) + y := by ring
  _ = (1 / 2) * (2 * x - y * x) + y := by rw[h2]
  _ = (1 / 2) * (2 * (x + 3 - 3) - (x + 3 - 3) * y) + y := by ring
  _ = (1 / 2) * (2 * (5 - 3) - (5 - 3) * y) + y := by rw[h1]
  _ = (1 / 2) * (2 * (2) - (2) * y) + y := by ring
  _ = (4 / 2) - (2 * y) / 2 + y := by ring
  _ = 2 - y + y := by ring
  _ = 2 := by ring

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  sorry
