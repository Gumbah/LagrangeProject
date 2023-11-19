import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

--First we want to prove Bézout's lemma, first we will
--need the (extended) Euclidean Algorithm.
--We know x = qy + r for a unique q,r < y and so we
--will define a function to give us these q,r given x,y.

def div_alg (x y : ℕ) : (ℕ × ℕ) :=
  ((((x-(x % y))/y),(x % y)) : ℕ × ℕ)

--Now (div_alg x y).1 returns q,
--and (div_alg x y).2 returns r.

--The way we will prove Bézout's lemma is by defining some
--function that returns integers a,b such that ax+by=gcd(x,y)


@[simp] theorem mod_less_right : (x : ℕ) % (y : ℕ) < y ∨ y=0 := by
  by_cases (y = 0)
  · exact Or.inr h
  refine (or_iff_left h).mpr ?_
  refine Nat.mod_lt x ?_
  exact Nat.pos_of_ne_zero h

mutual

  def bez_a (x y : ℕ) : ℤ :=
    if y ≠ 0 then
      bez_b y (x % y)
    else
      1

  def bez_b (x y : ℕ) : ℤ :=
    if y ≠ 0 then
      bez_a x (x % y) - (x/y) * bez_b x (x % y)
    else
      0

end
termination_by bez_a x y => y ; bez_b x y => y
decreasing_by sorry

theorem bezout (x y : ℕ) : (bez_a x y)*x + (bez_b x y)*y = (Nat.gcd x y) := by
  sorry
