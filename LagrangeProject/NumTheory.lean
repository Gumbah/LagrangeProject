import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

import Mathlib.Data.Nat.Prime
import Mathlib.Data.List.Intervals
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors



--18/11/23 - Jakub

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

--19/11/23 - Jakub

--The following function takes two natural numbers as input
--and repeatedly applies the division algorithm to obtain
--lists of dividends and remainders, we will use these
--to extend the Euclidean algorithm to give us our coeffs
--for Bézout's lemma

def div_lists (x y : ℕ) : (List ℤ × List ℤ) := Id.run do
  let mut (Q : List ℤ) := [1, 1]
  let mut (R : List ℤ) := [(x : ℤ), (y : ℤ)]
  let mut z := x
  let mut w := y
  let mut a := 0
  for i in [0:x] do
    if (div_alg z w).2 == 0 then
      break
    else
      Q := Q.concat ((div_alg z w).1)
      R := R.concat ((div_alg z w).2)
      a := w
      w := (div_alg z w).2
      z := a
  return (Q, R)

#eval div_lists 2023 70

--Now to reverse this process:
--if r_n ∈ R is the final element of this list, it is the gcd
--(to be proved later), we can write it as r_(n-2)-q_n*r_(n-1)
--and r_(n-1) can be written as r_(n-3)-q_(n-1)*r_(n-2), so we
--may substitute this into our inital equation recursively
--until we reach r_0 and r_1 (which are x, y) giving us an
--equation of the form r_n = ax+by for some a,b ∈ ℤ.

def bezout_coeffs_old (x y : ℕ) : (ℤ × ℤ) := Id.run do
  let (D : List ℤ) := ((div_lists x y).1).reverse
  let mut (a : ℤ) := (1 : ℤ)
  let mut (b : ℤ) := -(D[0]!)
  let mut (c : ℤ) := (0 : ℤ)
  for i in [1:D.length-2] do
    c := b
    b := a-(b*(D[i]!))
    a := c
  return (a, b)

#eval bezout_coeffs_old 2023 70

--Now it remains to prove Bézout's lemma, given this explicit
--construction for the coefficients. I aim to do this by
--induction.

--20/11/23 - Jakub

--I now understand that this approach using for loops and
--explicit construction to prove Bézout's lemma has made it
--very difficult for myself to do so. I will think on this
--and come back at a later time with a new approach to
--proving this lemma. For now I will `sorry` it out and move
--on.

--24/11/23 - Jakub

--I have now learned how to define such an algorithm recursively.
--with the help of fellow MA4N1 student Gareth Ma, I learned the syntax for
--such a recursive definition, and translated the algorithm found
--at `https://en.wikibooks.org/wiki/Algorithm_Implementation/Mathematics/Extended_Euclidean_algorithm#Recursive_algorithm_2`
--into LEAN, I used the Python recursive algorithm as it is the language
--I am most familiar with. With this new definition I hope I will be able
--to finally prove Bézout's lemma using induction.

def gcd_bezout : ℕ → ℕ → (ℕ × ℤ × ℤ)
| 0, y => (y, 0, 1)
| (x + 1), y =>
  /- for well-foundedness -/
  have := Nat.mod_lt y (Nat.succ_pos x)
  let (g, a, b) := gcd_bezout (y%(x+1)) (x+1)
  (g, b - y/(x+1) * a, a)

--checking it works, and agrees with the old algorithm
#eval bezout_coeffs_old 2023 70
#eval gcd_bezout 2023 70
#eval gcd_bezout (2023%70) 2023
#eval bezout_coeffs_old 20 9
#eval (gcd_bezout 20 9).2.1

--25/11/23 - Jakub

--I want to prove Bézout's lemma, but first we need some more definitions and lemmas. I am
--proving many basic facts about my `gcd_bezout` function in order to make the final proof of
--Bézout's lemma as simple as possible.

--I wanted to lead up to proving that the first term of the output of the `gcd_bezout` function,
--labelled `my_gcd` is equal to the gcd already in mathlib, but this proved difficult, as
--I do not understand how gcd is defined within mathlib, I may instead use my own definition of
--gcd from the `gcd_bezout` algorithm throughout the rest of the project, or prove it is equivalent
--to a more concise and useful definition I can make to save unfolding `gcd_bezout` every time.

--I have tried looking at the proof of Bézout's lemma that is already in mathlib (`https://github.com/leanprover-community/mathlib/blob/65a1391a0106c9204fe45bc73a039f056558cb83/src/data/int/gcd.lean#L107`)
--for inspiration on how to prove it for myself, but the proofs there are very concise and it
--is difficult to understand what each part is actually doing, I don't think that this gives much
--insight into my own proving of this theorem.

def bez_a (x y : ℕ): ℤ := (gcd_bezout x y).2.1
def bez_b (x y : ℕ): ℤ := (gcd_bezout x y).2.2
def my_gcd (x y : ℕ) : ℕ := (gcd_bezout x y).1

@[simp] lemma gcd_bez_expand (x y : ℕ) : gcd_bezout x y = (my_gcd x y, bez_a x y, bez_b x y) := by
  unfold my_gcd bez_a bez_b
  rfl

@[simp] lemma gcd_bez_zero_left {y : ℕ} : gcd_bezout Nat.zero y = (y, 0, 1) := by
  unfold gcd_bezout
  rfl

@[simp] lemma bez_a_zero_left {y : ℕ} : bez_a Nat.zero y = 0 := by
  unfold bez_a
  simp? says simp only [Nat.zero_eq, gcd_bez_zero_left]

@[simp] lemma bez_b_zero_left {y : ℕ} : bez_b Nat.zero y = 1 := by
  unfold bez_b
  simp? says simp only [Nat.zero_eq, gcd_bez_zero_left]

@[simp] lemma my_gcd_zero_left {y : ℕ} : my_gcd Nat.zero y = y := by
  unfold my_gcd
  simp? says simp only [Nat.zero_eq, gcd_bez_zero_left]

@[simp] lemma bez_a_zero_right {x : ℕ} (h : x ≠ 0) : bez_a x Nat.zero = 1 := by
  unfold bez_a gcd_bezout
  induction x with
  | zero => exact absurd rfl h
  | succ x => simp? says simp only [Nat.zero_eq, Nat.zero_mod, gcd_bez_zero_left, CharP.cast_eq_zero,
    EuclideanDomain.zero_div, mul_zero, sub_zero]

@[simp] lemma bez_b_zero_right {x : ℕ} (h : x ≠ 0) : bez_b x Nat.zero = 0 := by
  unfold bez_b gcd_bezout
  induction x with
  | zero => exact absurd rfl h
  | succ x => simp? says simp only [Nat.zero_eq, Nat.zero_mod, gcd_bez_zero_left]

--27/11/23 - Jakub

--The way `Nat.gcd` is defined in mathlib4 makes it very difficult to prove that my construction is equal.
--I do not know how to work around the `WellFounded.fix` and `WellFounded.fixF` and `Acc.rec` that come
--out when I try to unfold the definition of `Nat.gcd`, I have a different approach where I will prove by
--induction that the two functions agree at every input value. I have successfully proved that for the zero
--case and I have also managed to reduce in the `succ` case using `my_gcd_succ` and `Nat.gcd_succ` so all
--that remains is to understand how to use strong induction in LEAN. The `induction` tactic appears to use
--weak induction that does not help me in this case as I have only been able to reduce to
--`(y&(Nat.succ x)), Nat.succ x` instead of `x, y`. I also see that I may have to show that `x < y` without
--loss of generality using the symmetry of the `my_gcd` and `Nat.gcd` functions.

@[simp] lemma my_gcd_self {x : ℕ} : my_gcd x x = x := by
  induction x with
  | zero => apply my_gcd_zero_left
  | succ =>
    unfold my_gcd gcd_bezout
    simp only [Nat.mod_self, gcd_bez_expand, my_gcd_zero_left, bez_a_zero_left, bez_b_zero_left]

@[simp] lemma my_gcd_succ (x y : ℕ) : my_gcd (Nat.succ x) y = my_gcd (y%(Nat.succ x)) (Nat.succ x) := by
  unfold my_gcd
  rfl

@[simp] lemma my_gcd_zero_right {x : ℕ} : my_gcd x Nat.zero = x := by
  unfold my_gcd gcd_bezout
  induction x with
  | zero => rfl
  | succ x => simp? says simp only [Nat.zero_eq, Nat.zero_mod, gcd_bez_zero_left]

@[simp] lemma gcd_bez_zero_right {x : ℕ} (h : x ≠ 0) : gcd_bezout x Nat.zero = (x, 1, 0) := by
  rw[gcd_bez_expand x Nat.zero]
  induction x with
  | zero => exact absurd rfl h
  | succ => simp? says simp only [Nat.zero_eq, ne_eq, Nat.succ_ne_zero, not_false_eq_true, my_gcd_zero_right,
    bez_a_zero_right, bez_b_zero_right]

--28/11/23 - Jakub

--I have discovered the `Nat.gcd.induction` tactic and will apply it to prove that `my_gcd` is equivalent
--to `Nat.gcd` in mathlib, which I will then use to help my proof of Bézout's lemma. I will try also
--using `Nat.gcd.induction` in my proof of Bézout's lemma, since I think it will be helpful. The equality
--of `my_gcd` and `Nat.gcd` gives us all the lemmas in `Mathlib,Data.Nat.GCD.Basic` for free now to apply
--in this proof, so I hope that it will now be feasible for me. I think it will also be useful to prove
--some smaller lemmas like `my_gcd_succ` and `my_gcd_rec` for the `bez_a` and `bez_b` functions.

@[simp] theorem my_gcd_rec (x y : Nat) : my_gcd x y = my_gcd (y % x) x :=
  match x with
  | 0 => by
    have := (Nat.mod_zero y).symm
    simp only [my_gcd_zero_left, Nat.mod_zero, my_gcd_zero_right]
  | x + 1 => by exact (my_gcd_succ x y).symm

@[simp] theorem dvd_my_gcd : k ∣ x → k ∣ y → k ∣ my_gcd x y := by
  induction x, y using Nat.gcd.induction with intro kx ky
  | H0 y => rw [my_gcd_zero_left]; exact ky
  | H1 y x _ IH => rw [my_gcd_rec]; exact IH ((Nat.dvd_mod_iff kx).2 ky) kx

theorem my_gcd_eq_gcd (x y : ℕ) : Nat.gcd x y = my_gcd x y := by
  induction x, y using Nat.gcd.induction with
  | H0 y =>
    rw [my_gcd_zero_left, Nat.gcd_zero_left]
  | H1 x y _ ih =>
    rw [Nat.gcd_rec, my_gcd_rec]
    exact ih

@[simp] lemma bez_a_succ (x y : ℕ) : bez_a (Nat.succ x) y = bez_b (y%(Nat.succ x)) (Nat.succ x) - y/(Nat.succ x) * bez_a (y%(Nat.succ x)) (Nat.succ x) := by
  unfold bez_a bez_b
  rfl

@[simp] lemma bez_b_succ (x y : ℕ) : bez_b (Nat.succ x) y = bez_a (y%(Nat.succ x)) (Nat.succ x) := by
  unfold bez_a bez_b
  rfl

@[simp] lemma bez_a_rec (x y : ℕ) (h : 0 < x) : bez_a x y = bez_b (y%x) x - y/x * bez_a (y%x) x := by
  match x with
  | 0 => contradiction
  | x + 1 => exact bez_a_succ x y

@[simp] lemma bez_b_rec (x y : ℕ) (h : 0 < x): bez_b x y = bez_a (y%x) x := by
  match x with
  | 0 => contradiction
  | x + 1 => exact bez_b_succ x y

--29/11/23 - Jakub

--I have managed to reduce the proof of Bézout's lemma to now simply rearranged the following theorem
--from mathlib, I have proved the rest of `bez_rec` now excluding this, which was previously entirely
--`sorry`-d out and is necessary for my proof of Bézout's lemma
#check Int.ediv_add_emod
@[simp] lemma my_ediv_add_emod (x y : ℤ) : y-x*(y/x) = (y%x) := by
  nth_rewrite 1 [← Int.ediv_add_emod y x]
  simp only [add_sub_cancel']

--Remains to prove this !!! I will continue work on this part later.
@[simp] lemma bez_rec (x y : ℕ) (h : 0 < x) : bez_a (y%x) x * (y%x) + bez_b (y%x) x * x = bez_a x y * x + bez_b x y * y := by
  rw [bez_a_rec x y, bez_b_rec x y]
  rw [mul_sub_right_distrib]
  rw [mul_comm (y/x * bez_a (y%x) x) x,← mul_assoc]
  rw [mul_comm (bez_a (y%x) x) y]
  rw [← add_sub_right_comm ((bez_b (y%x) x)*x) (y*(bez_a (y%x) x)) (x*(y/x)*(bez_a (y%x) x))]
  rw [add_sub_assoc ((bez_b (y%x) x)*x) (y*(bez_a (y%x) x)) (x*(y/x)*(bez_a (y%x) x))]
  rw [← mul_sub_right_distrib (y : ℤ) ((x*(y/x)) : ℤ) (bez_a (y%x) x)]
  -- here I want to use a rearranged version of Int.ediv_add_emod to change
  --`(y-x*(y/x))` into `(y%x)` (see above lemma for this)
  simp only [my_ediv_add_emod]
  linarith
  exact h
  exact h

--Statement of Bézout's lemma using `my_gcd`
theorem bez_a_left_mul_bez_b_right_eq_my_gcd (x y : ℕ) : (bez_a x y)*x+(bez_b x y)*y=(my_gcd x y) := by
  induction x, y using Nat.gcd.induction with
  | H0 y =>
    simp only [bez_a_zero_left, bez_b_zero_left, my_gcd_zero_left,
      CharP.cast_eq_zero, mul_zero, one_mul, zero_add]
  | H1 x y h ih =>
    rw [← bez_rec, my_gcd_rec]
    exact ih
    exact h

--Statement of Bézout's lemma using `Nat.gcd`
theorem bezout (x y : ℕ) : (bez_a x y)*x+(bez_b x y)*y=(Nat.gcd x y) := by
  rw [my_gcd_eq_gcd]
  apply bez_a_left_mul_bez_b_right_eq_my_gcd

--30/11/23 - Jakub

--I have now finally managed to fully prove Bézout's lemma without any remaining `sorry`s. Next I will
--begin work on defining `ℤ/nℤ` as a ring and use this to prove the Chinese remainder theorem
--(Sun Tzu's theorem). The proof of Bézout's lemma proved to be far more difficult than I had anticipated,
--and I now see that I need to be very careful defining things in such a way to make the proofs as
--simple as possible.

-- Katie

-- Now to utilise Bezout's lemma in some smaller lemmas building our number theory library.
-- After trying to rephrase Euclid's lemma many different ways, I came to the conclusion that
-- it would be easier to separate the cases of which variable was coprime to p into their own
-- respective theorems. Following this, I needed even more preceding results regarding prime divisors.
-- Structuring the proof of Euclid's lemma was fairly difficult;

theorem bezout_exists (x y : ℕ) : ∃ (a b : ℕ) , (Nat.gcd x y) = a*x + b*y := by
  sorry

@[simp] lemma gcd_eq_1 {x : ℕ}(p : Nat.Primes)(h: p < x) : (Nat.gcd x p = 1) ↔ ¬((p : ℕ) ∣ x) := by
  constructor
 -- we have theorem dvd_my_gcd : k ∣ x → k ∣ y → k ∣ my_gcd x y
  --Nat.gcd x p = 1 => any k that divides both x and p must be 1 => the only common divisor of x and p is 1 => ¬(p ∣ x)
  --struggling to find a way to formalise this argument - if needs be it will be imported


-- nat.gcd x p = 1 => exists a,b st ax + bp = 1 => x = (1 - bp)/a => ¬(p ∣ x)
-- ¬(p ∣ x) =>
  · intro h1
   -- rw[← bezout] at h1
    sorry


@[simp] lemma gcd_eq_p {x : ℕ}(p : Nat.Primes)(h: p < x) : (Nat.gcd x p = 1) ↔ ((p : ℕ)∣ x) := by
  constructor
  intro h1
  sorry

  -- nat.gcd (x,p) = p => p ∣ x and p ∣ p
  -- p ∣ x => ∃ α ∈ ℕ s.t. x = αp => Nat.gcd(x,p) = Nat.gcd(αp,p) = p
  · --intro h1
    --simp only at h1

@[simp] lemma coprime_p {m : ℕ}(p : Nat.Primes)(h: p < m) : (Nat.gcd m p = 1) ∨ (Nat.gcd m p = p):= by
 intros


 -- use nat.prime_def_lt'' after showing gcd x p divides p
 sorry

theorem euclid_l1_coprime {m n : ℕ}(p : Nat.Primes)(h_n : p < n)(h_m : p < m): ((p : ℕ) ∣ m*n) ∧ ((Nat.gcd (p : ℕ) m)=1) → ((p : ℕ) ∣ n):= by
  intros h1
  rw[bezout] at h1
  -- rewrite gcd p m as its bezout identity: ∃ x,y s.t. mx + py =1
  -- n = n(1) = n(mx + py)
  sorry

theorem euclid_r1_coprime {m n : ℕ}(p : Nat.Primes)(h_n : p < n)(h_m : p < m): ((p : ℕ) ∣ m*n) ∧ ((Nat.gcd (p : ℕ) n)=1) → ((p : ℕ) ∣ m):= by
  intros h2
  rw[bezout] at h2
  -- rewrite gcd p n as its bezout identity
  -- m = m(1) = m(nx + py)
  sorry

theorem euclid_l2_coprime {m n : ℕ}(p : Nat.Primes ) : ((p : ℕ) ∣ m*n) ∧ ((Nat.gcd (p : ℕ) n) = 1) → ((Nat.gcd (p : ℕ) m) = p)  := by
  intros h1
  norm_cast
  sorry

theorem euclid_r2_coprime {m n : ℕ}(p : Nat.Primes) : ((p : ℕ) ∣ m*n) ∧ ((Nat.gcd (p : ℕ) m) = 1) → ((Nat.gcd (p : ℕ) n) = p)  := by
 sorry

-- we have:
-- gcd p n = 1 or p
-- gcd p m = 1 or p
-- if p ∣ m*n and gcd(p,m)=1, then p ∣ n
-- if p ∣ m*n and gcd(p,n)=1 then p ∣ m
-- if ¬(p ∣ n) then p ∣ m
-- if ¬(p ∣ m) then p ∣ n
-- so we cannot have a case where both ¬(p ∣ n) and ¬(p ∣ n)

-- wlts: p ∣ m*n → p ∣ n or p ∣ m
theorem euclid {m n : ℕ}(p : Nat.Primes)(h_n : p < n)(h_m : p < m) : ((p : ℕ) ∣ m*n) → ((p : ℕ) ∣ n) ∨ ((p : ℕ) ∣ m) := by
  intro h1
  apply Or.inl
  sorry
  --either gcd(p,m) = p or gcd(p,m)=1
  --case 1: gcd(p,m)=p => p ∣ m
  --case 2: gcd(p,m)=1 => gcd(p,n)=p => p ∣ n


-- Structuring the proof of Euclid's lemma was fairly difficult; I knew how to prove it easily
-- by hand with the theorems listed above in just a couple lines, but constructing a sort of contradiction
-- (i.e. either gcd p n = 1 or gcd p m = 1, but can't have both occur simultaneously and wanting to structure
-- the proof like suppose p ∣ m, and then supose p ∣ n) was very new to me.
theorem gauss {d m n : ℕ} (h1 : d ∣ m * n) (h2 : Nat.gcd m d = 1) : d ∣ n := by
 sorry


def tot {0 m : ℕ}(x : List.Ico (0 m+1)) := {(Nat.gcd x m) = 1}.card


theorem coprime_mult {a b : ℕ}((Nat.gcd a m)=1) : ((Nat.gcd b m)=1) → ((Nat.gcd a*b m)=1) := by

sorry


open BigOperators
def fun_sum_of_divisors_1 (n : ℕ) : ℕ := ∑ d in Nat.divisors n, d
-- Defining the sum of divisors function took a lot of trial and erroe/tweaking in the syntax, but with the help of the
-- module leader it became clear that, for the sum function to work, I needed to "open BigOperators" - it is a relief to
-- see that the finite sets are not an issue as of yet.

#eval fun_sum_of_divisors_1 4




--Sun Tzu's Theorem

--11/12/23 - Jakub

--Unfortunately, the modulo notation from mathlib comes from a file where the CRT is already proven, so I will define
--it and prove basic features about it myself, as we had initially planned

--The following two lines of LEAN code are almost identical to mathlib, but I will prove the basic lemmas myself.
--Note the use of different syntax to mathlib to avoid accidentally using their proofs.
def Mod_eq (n a b : ℕ) := a%n = b%n
notation:50 a "≡" b " [mod " n "]" => Mod_eq n a b

--It turned out that most of the lemmas follow trivially from the properties of `=`, though I had to do a fair
--amount of adjusting the statements slightly to get them in the same form to simply exact these properties.

@[simp] lemma Mod_eq_rfl {n a: ℕ} : a ≡ a [mod n] := by
  rfl

@[simp] lemma Mod_eq_symm {n a b: ℕ} : a ≡ b [mod n] → b ≡ a [mod n] := by
  exact Eq.symm

@[simp] lemma Mod_eq_trans {n a b c : ℕ} : a ≡ b [mod n] → b ≡ c [mod n] → a ≡ c [mod n] := by
  exact Eq.trans

@[simp] lemma Mod_eq_n_zero {n : ℕ} : n ≡ 0 [mod n] := by
  rw [Mod_eq]
  rw [Nat.zero_mod]
  rw [Nat.mod_self]

@[simp] lemma Mod_eq_zero_iff_dvd {n a : ℕ} : a ≡ 0 [mod n] ↔ n ∣ a := by
  rw [Mod_eq]
  rw [Nat.zero_mod]
  rw [Nat.dvd_iff_mod_eq_zero]

@[simp] lemma Mod_eq_add_mul (n a b: ℕ) : a + b*n ≡ a [mod n] := by
  rw [Mod_eq]
  rw [Nat.add_mod]
  simp? says simp only [Nat.mul_mod_left, add_zero, Nat.mod_mod]

--Here I have defined a function to give a `x` such that, given `m,n,a,b ∈ ℕ`, we have
--`x ≡ a [mod m], x ≡ b [mod n]`, it  remains to prove this property of the construction.
--I have used the syntax of a set with a condition like Mathlib uses for the chinese remainder theorem.
--I initially experimented with defining `x` then separately proving that it satisfied the required condition
--imposed here, but navigating the if statements proved cumbersome, so I opted to  arrange it like so.
--I believe that understanding how to use this syntax will prove useful in the future, and the proof is my own.

def classical_crt (m n a b : ℕ) (h: Nat.Coprime m n) : {x // x ≡ a [mod m] ∧ x ≡ b [mod n]} :=
  if hm : m = 0 then ⟨a, by
    constructor
    · simp only [Mod_eq_rfl]
    rw [Mod_eq]
    have hhn : n = 1 := by
      rw [hm] at h
      rw [Nat.coprime_zero_left n] at h
      exact h
    rw [hhn]
    rw [Nat.mod_one a, Nat.mod_one b]⟩
  else
    if hn : n = 0 then ⟨b, by
      constructor
      · have hhm : m = 1 := by
          rw [hn] at h
          rw [Nat.coprime_zero_right m] at h
          exact h
        rw [hhm]
        rw [Mod_eq]
        rw [Nat.mod_one a, Nat.mod_one b]
      simp only [Mod_eq_rfl]⟩
    else
      let y := Int.toNat (bez_b m n % m)
      let z := Int.toNat (bez_a m n % n)
      ⟨Int.toNat (a*n*y+b*m*z) % (Nat.lcm m n), by
        --Here I want to use Bézout's lemma to give me that `n*y ≡ 1 [mod m]` and `m*z ≡ 1 [mod n]`, with which
        --I will then be able to show that `a*n*y ≡ a [mod m]` and similarly for `b`, which will complete the proof.
        have hny : n*y ≡ 1 [mod m] := by
          sorry
        have hmz : m*z ≡ 1 [mod n] := by
          sorry
        sorry
        ⟩



--With these we can prove the `Algebraic Chinese Remainder theorem` for coprime m,n, i.e. ℤ/mnℤ = ℤ/mℤ × ℤ/nℤ

--With this statement we can prove the `multiplicity` of the Euler Totient function for coprime m n, i.e. phi(mn)=phi(m)*phi(n)

--We will also prove that phi(p)=|(ℤ/pℤ)^×|=p-1 and phi(p^n)=p^n-p^(n-1) for p prime, which then will lead into proving that
--∑_(a∣n) phi(a)=n for n ∈ ℕ

--After we prove these we will have all the tools from number theory to collaborate with the group theory side to prove
--Euler's theorem and Fermat's little theorem.
