--Please read the README.md, as well as our code comments, for determining individual grades.

--Number Theory Imports
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.List.Intervals
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Logic.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Image
import Mathlib.Init.Data.List.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
--Group Theory Imports
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Setoid.Partition
--import Mathlib.Data.Finite.Card
--Universal imports
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic



--Rose + Ed
--In this section we will use the basic definitions of Groups to
--prove basic things about them only using the axioms of acossiativity,
--inverses and the identity

--Specifically we are using
--one_mul
--mul_left_inv
--mul_assoc
--which are used to define the Group.ofLeftAxioms in Mathlib

--(Rose) I have written out and formatted all the basic lemmas

section group

namespace groupsMul

  variable [Group G]

  @[simp]lemma LeftCancelMul (a b c : G) : a * b = a * c → b = c := by
    intro h
    rw[← one_mul b]
    rw[← one_mul c]
    rw[← mul_left_inv a]
    rw[mul_assoc]
    rw[h]
    rw[← mul_assoc]
    done

  @[simp]lemma MulOne (a : G) : a * 1 = a := by
    nth_rewrite 2 [← one_mul a]
    apply LeftCancelMul a⁻¹
    rw[← mul_assoc]
    rw[mul_left_inv]
    rw[one_mul]
    rw[one_mul]
    rw[mul_left_inv]
    done

  @[simp]lemma InvInvMul (a : G) : (a⁻¹)⁻¹ = a := by
    rw[← MulOne a⁻¹⁻¹]
    rw[← mul_left_inv a]
    rw[← mul_assoc a⁻¹⁻¹ a⁻¹ a]
    rw[mul_left_inv a⁻¹]
    rw[one_mul]
    done

  @[simp]lemma MulInv (a : G) : a * a⁻¹ = 1 := by
    nth_rewrite 1 [← InvInvMul a]
    rw[mul_left_inv a⁻¹]
    done

    @[simp]lemma RightCancelMul (a b c : G) : b * a = c * a → b = c := by
    intro h
    rw[← MulOne b]
    rw[← MulOne c]
    rw[← MulInv a]
    rw[← mul_assoc]
    rw[h]
    rw[← mul_assoc]
    done

  @[simp]lemma LeftInvEqMul (a b c : G) : a = b⁻¹ * c ↔ b * a = c := by
    constructor
    · intro h1
      rw[h1]
      rw[← mul_assoc]
      rw[MulInv]
      rw[one_mul]
    · intro h2
      rw[← h2]
      rw[← mul_assoc]
      rw[mul_left_inv]
      rw[one_mul]
    done

  @[simp]lemma RightInvEqMul (a b c : G) : a = b * c⁻¹ ↔ a * c = b := by
    constructor
    · intro h1
      rw[h1]
      rw[mul_assoc]
      rw[mul_left_inv]
      rw[MulOne]
    · intro h2
      rw[← h2]
      rw[mul_assoc]
      rw[MulInv]
      rw[MulOne]
    done

  @[simp]lemma IdUniqueMul (a b : G) : a * b = b ↔ a = 1 := by
    constructor
    · intro h1
      rw[← MulOne a]
      rw[← MulInv b]
      rw[← mul_assoc]
      rw[h1]
    · intro h2
      rw[h2]
      rw[one_mul]
    done

  @[simp]lemma InvUniqueRightMul (a b : G) : a * b = 1 ↔ a = b⁻¹ := by
    constructor
    · intro h
      rw[← MulOne a]
      rw[← MulInv b]
      rw[← mul_assoc]
      rw[h]
      rw[one_mul]
    · intro h
      rw[h]
      rw [mul_left_inv]
    done

  @[simp]lemma InvUniqueLeftMul (a b : G) :a * b = 1 ↔ b = a⁻¹ := by
    constructor
    · intro h
      rw[← one_mul b]
      rw[← mul_left_inv a]
      rw[mul_assoc]
      rw[h]
      rw[MulOne]
    · intro h
      rw[h]
      rw[MulInv]
    done

  @[simp]lemma InvBracketsMul (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    apply LeftCancelMul (a*b)
    rw[MulInv (a*b)]
    rw[← mul_assoc, mul_assoc a b]
    rw[MulInv, MulOne, MulInv]
    done

end groupsMul

--For this next bit we are using
--zero_add
--add_left_neg
--add_assoc
--these are the equivalent of the other 3, but for additive groups

namespace addGroups

  variable {G : Type} [AddGroup G]

  @[simp]lemma LeftCancelAdd (a b c : G) : a + b = a + c → b = c := by
    intro h
    rw[← zero_add b]
    rw[← zero_add c]
    rw[← add_left_neg a]
    rw[add_assoc]
    rw[h]
    rw[← add_assoc]
    done

  @[simp]lemma AddZero (a : G) : a + 0 = a := by
    nth_rewrite 2 [← zero_add a]
    apply LeftCancelAdd (-a)
    rw[← add_assoc]
    rw[add_left_neg]
    rw[zero_add]
    rw[zero_add]
    rw[add_left_neg]
    done

  @[simp]lemma NegNegAdd (a : G) : -(-a) = a := by
    rw[← AddZero (-(-a))]
    rw[← add_left_neg a]
    rw[← add_assoc (-(-a)) (-a) a]
    rw[add_left_neg (-a)]
    rw[zero_add]
    done

  @[simp]lemma AddNeg (a : G) : a + -a = 0 := by
    nth_rewrite 1 [← NegNegAdd a]
    rw[add_left_neg (-a)]
    done

  @[simp]lemma RightCancelAdd (a b c : G) : b + a = c + a → b = c := by
    intro h
    rw[← AddZero b]
    rw[← AddZero c]
    rw[← AddNeg a]
    rw[← add_assoc]
    rw[h]
    rw[← add_assoc]
    done

  @[simp]lemma LeftNegEqAdd (a b c : G) : a = -b + c ↔ b + a = c := by
    constructor
    · intro h1
      rw[h1]
      rw[← add_assoc]
      rw[AddNeg]
      rw[zero_add]
    · intro h2
      rw[← h2]
      rw[← add_assoc]
      rw[add_left_neg]
      rw[zero_add]
    done

  @[simp]lemma RightNegEqAdd (a b c : G) : a = b + -c ↔ a + c = b := by
    constructor
    · intro h1
      rw[h1]
      rw[add_assoc]
      rw[add_left_neg]
      rw[AddZero]
    · intro h2
      rw[← h2]
      rw[add_assoc]
      rw[AddNeg]
      rw[AddZero]
    done

  @[simp]lemma IdUniqueAdd (a b : G) : a + b = b ↔ a = 0 := by
    constructor
    · intro h1
      rw[← AddZero a]
      rw[← AddNeg b]
      rw[← add_assoc]
      rw[h1]
    · intro h2
      rw[h2]
      rw[zero_add]
    done

  @[simp]lemma InvUniqueRightAdd (a b : G) (h : a + b = 0) : a = -b := by
    rw[← AddZero a]
    rw[← AddNeg b]
    rw[← add_assoc]
    rw[h]
    rw[zero_add]
    done

  @[simp]lemma InvUniqueLeftAdd (a b : G) (h : a + b = 0) : b = -a := by
    rw[← zero_add b]
    rw[← add_left_neg a]
    rw[add_assoc]
    rw[h]
    rw[AddZero]
    done

end addGroups

end group

--Now we will do what we did earlier with groups, but for rings
--We will only make use of only:
--add_comm
--add_assoc
--zero_add
--add_left_neg
--mul_assoc
--one_mul
--mul_one
--left_distrib
--right_distrib
--which are what are used in Ring.ofMinimalAxioms

section rings

  variable {R : Type} [Ring R]

  --Edward (Rings)
  --we're first going to prove all the results from additive rings on groups

  @[simp]lemma LeftCancelAdd (a b c : R) : a + b = a + c → b = c := by
    intro h
    rw[← zero_add b]
    rw[← zero_add c]
    rw[← add_left_neg a]
    rw[add_assoc]
    rw[h]
    rw[← add_assoc]
    done

  @[simp]lemma AddZero (a : R) : a + 0 = a := by
    nth_rewrite 2 [← zero_add a]
    apply LeftCancelAdd (-a)
    rw[← add_assoc]
    rw[add_left_neg]
    rw[zero_add]
    rw[zero_add]
    rw[add_left_neg]
    done

  @[simp]lemma NegNegAdd (a : R) : -(-a) = a := by
    rw[← AddZero (-(-a))]
    rw[← add_left_neg a]
    rw[← add_assoc (-(-a)) (-a) a]
    rw[add_left_neg (-a)]
    rw[zero_add]
    done

  @[simp]lemma AddNeg (a : R) : a + -a = 0 := by
    nth_rewrite 1 [← NegNegAdd a]
    rw[add_left_neg (-a)]
    done

  @[simp]lemma RightCancelAdd (a b c : R) : b + a = c + a → b = c := by
    intro h
    rw[← AddZero b]
    rw[← AddZero c]
    rw[← AddNeg a]
    rw[← add_assoc]
    rw[h]
    rw[← add_assoc]
    done

  @[simp]lemma LeftNegEqAdd (a b c : R) : a = -b + c ↔ b + a = c := by
    constructor
    · intro h1
      rw[h1]
      rw[← add_assoc]
      rw[AddNeg]
      rw[zero_add]
    · intro h2
      rw[← h2]
      rw[← add_assoc]
      rw[add_left_neg]
      rw[zero_add]
    done

  @[simp]lemma RightNegEqAdd (a b c : R) : a = b + -c ↔ a + c = b := by
    constructor
    · intro h1
      rw[h1]
      rw[add_assoc]
      rw[add_left_neg]
      rw[AddZero]
    · intro h2
      rw[← h2]
      rw[add_assoc]
      rw[AddNeg]
      rw[AddZero]
    done

  @[simp]lemma IdUniqueAdd (a b : R) : a + b = b ↔ a = 0 := by
    constructor
    · intro h1
      rw[← AddZero a]
      rw[← AddNeg b]
      rw[← add_assoc]
      rw[h1]
    · intro h2
      rw[h2]
      rw[zero_add]
    done

  @[simp]lemma InvUniqueRightAdd (a b : R) (h : a + b = 0) : a = -b := by
    rw[← AddZero a]
    rw[← AddNeg b]
    rw[← add_assoc]
    rw[h]
    rw[zero_add]
    done

  @[simp]lemma InvUniqueLeftAdd (a b : R) (h : a + b = 0) : b = -a := by
    rw[← zero_add b]
    rw[← add_left_neg a]
    rw[add_assoc]
    rw[h]
    rw[AddZero]
    done

    --one would be tempted to try and do the same thing with multiplicative groups
    --however this won't work as multiplicative inverses aren't a thing in rings
    --I'm going to start writing some new properties

  @[simp]lemma ZeroMul (a : R) : 0 * a = 0 := by
  apply LeftCancelAdd (0 * a)
  rw[← right_distrib]
  rw[AddZero (0 * a)]
  rw[AddZero]
  done

  @[simp]lemma MulZero (a : R) : a * 0 = 0 := by
  apply RightCancelAdd (a * 0)
  rw[← left_distrib]
  rw[zero_add (a * 0)]
  rw[zero_add]
  done

  @[simp]lemma NegOneMul (a : R) : -1 * a = -a := by
  apply InvUniqueRightAdd
  nth_rewrite 2 [← one_mul a]
  rw[← right_distrib]
  rw[add_left_neg]
  rw[ZeroMul]
  done

  @[simp]lemma MulNegOne (a : R) : a * -1 = -a := by
  apply InvUniqueLeftAdd
  nth_rewrite 1 [← mul_one a]
  rw[← left_distrib]
  rw[AddNeg]
  rw[MulZero]
  done

  variable {S : Type} [Ring S]

  def DirectRingProd [Ring R] [Ring S] (a : R) (b : S) : R × S :=
    (a, b)

end rings


--Rose (Cosets)

--We now will define Multiplitive left and right cosets (We do both as it will
--be useful for quotient groups later). I first define the cosets as a function
--the image of the function taking an element, h, from a Subgroup H of G and multiplying
--it with elements from the group. This was heavily inspired from mathlib
--

--I then defined notation associated with taking a coset, which highly improves
--readability of the code

--From this I wrote basic lemmas for facts about cosets and things to lead
--up to Lagranges theroems, adding more as I went along as necessary.
--Since we are using our own lemmas for facts about elements in a group,
--I had to take particular care not to use the facts about Groups.Defs in my
--proofs and to use our own lemmas stating these facts. This also ended up
--involving a lot of maintanance as many previous lemmas and definitions had
--to be slightly altered as the project progressed.

--Edward (Quotient groups)
section cosetsMul

  namespace CosetsMul

  variable [Group G] (H : Subgroup G)

  --(Rose) To prove Lagrange's Thoerem, Cosets must be used, and so the bulk of my work will be done here
  --I first defined the left and right cosets with the group G and subgroup H in the defintion
  --but later moved them out to the general namespace, as i wanted to use the variables for the proofs of lemmas
  --and theorems with out initalising them everytime. This definition is near identical to the definition in MathLib
  --as it is so fundimental I was unsure on how to it in my own way. The main difference
  --to Mathlib is using a Set G and subset H instead of group and subgroup, this was mainly as it will be
  --easier to unsure what is being referenced in the project are groups and not just sets

  def LeftCosetMul (g : G) (H : Set G) : Set G :=
    Set.image (fun h => g * h) H

  def RightCosetMul (H : Set G) (g : G) : Set G :=
    Set.image (fun h => h * g) H

  --(Rose) Here I define notation for cosets, as it was proving very annoying to use the coset definitons
  --in practice as "LeftCosetMul g H" was not a very readable goal or hypothesis especially when getting even
  --slightly more complicated, so I looked around the lean documentation and found the user defined notation
  --after some tinkering to get it to work, i eventally decided upon the given notation. This was because it was
  --both readable, and although long, gave a distict differentablity to just using "*" so it was very clear
  --that it was a Coset by my definition and not any other operation or object.

  notation:70 i:70 "LCoset*" H:70 => LeftCosetMul i H
  notation:70 H:70 "RCoset*" i:70 => RightCosetMul H i

  --(Rose) I originally was also going to define a equivilence relation between two cosets just by the elment it
  -- is being multiplied by, however this proved to be quite difficult notationally and also kind of useless as just
  --using = between 2 cosets worked completly fine and so I abandoned it.

  /-
  def LeftCosetEqMul (g h : G):=
    g LCoset* H = h LCoset* H

  def RightCosetEqMul (g h : G):=
    H RCoset* g = H RCoset* h

  set_option quotPrecheck false
  notation:50 i:50 "LC=" j:50 => LeftCosetEqMul (i LCoset* H) (j LCoset* H)
  notation:50 i:50 "RC=" j:50 => RightCosetEqMul (H RCoset* i) (H LCoset* j)
  set_option quotPrecheck true
  -/

  --Edward
  --Some definitions for NormEquiv and tne meaning of quotient group

  def NormEquiv[Group G] (H: Set G) (a b : G):= a * b⁻¹ ∈ H

  def LeftQuotientGroup(G) [Group G] (H : Subgroup G) [H.Normal] :=
    Set (∀(g:G), g LCoset* H)

  #check LeftQuotientGroup

  def RightQuotientGroup(G) [Group G] (H : Subgroup G) [H.Normal] :=
    Set (∀(g:G), H RCoset* g)

  /-
  def QuotientGroup (G) [Group G] (H : Subgroup G) [H.Normal] :=
    G⧸H
  -/

  open groupsMul
  open Set Function

  --(Rose) This lemma I initially did not write as I just forgot about it, however while proving later
  --lemmas, I found it was an obvious fact I had left out and was very useful at the end of proofs, and so came
  --back to write it here

  lemma ElemInOwnLeftCosetMul (i : G) : i ∈ i LCoset* H := by
    simp only [LeftCosetMul, image_mul_left, mem_preimage]
    rw[mul_left_inv]
    exact Subgroup.one_mem H
    done

  lemma ElemInOwnRightCosetMul (i : G) : i ∈ H RCoset* i := by
    simp only [RightCosetMul, image_mul_right, mem_preimage]
    rw[MulInv]
    exact Subgroup.one_mem H
    done

  --(Rose) This is the first lemma I proved about cosets. I initally was using refines which ended
  --up splitting into cases of elements being in sets from iff statments. This was a very poor method and I eventually realised
  --I could just simply use the basic definitions and came to the much shorter proof I have here.

  lemma AssocLeftCosetMul (a b : G) :
  a LCoset* (b LCoset* H) = (a*b) LCoset* H := by
    repeat rw[LeftCosetMul]
    rw[(image_comp _ _ _).symm]
    simp only [comp]
    refine image_congr ?h
    exact fun a_1 a_2 ↦ (mul_assoc a b a_1).symm
    done


  lemma AssocRightCosetMul (a b : G) :
  (H RCoset* a) RCoset* b = H RCoset* (a*b) := by
    repeat rw[RightCosetMul]
    rw[(image_comp _ _ _).symm]
    simp only [comp]
    refine image_congr ?h
    exact fun a_1 a_2 ↦ mul_assoc a_1 a b
    done

  --(Rose) This again was another lemma similar to ElemInOwnCoset where I realised
  --I forgot it but ends up being very useful. The proof is trivial but having the statement
  --as a lemma makes it much easier to use in longer proofs

  lemma LeftCosetElemImpEqMul (a b : G) (h : a = b):
  a LCoset* H = b LCoset* H := by
    rw [h]
    done

  lemma RightCosetElemImpEqMul (a b : G) (h : a = b):
  H RCoset* a = H RCoset* b := by
    rw[h]
    done

  --(Rose) Next was a very simply lemma to just build up tools for proving harder lemmas.
  lemma LeftCosetClosureMul (g i : G) :
  g ∈ i LCoset* H ↔ i⁻¹ * g ∈ H := by
    constructor
    · intro h
      simp only [LeftCosetMul._eq_1, image_mul_left, mem_preimage, SetLike.mem_coe] at h
      exact h
    · intro h
      simp only [LeftCosetMul._eq_1, image_mul_left, mem_preimage, SetLike.mem_coe]
      exact h
    done
    --May be more lemmas needed

  lemma RightCosetClosureMul (g i : G) :
  g ∈ H RCoset* i ↔ g * i⁻¹ ∈ H := by
    constructor
    · intro h
      simp only [RightCosetMul._eq_1, image_mul_right, mem_preimage, SetLike.mem_coe] at h
      exact h
    · intro h
      simp only [RightCosetMul._eq_1, image_mul_right, mem_preimage, SetLike.mem_coe]
      exact h
    done

  lemma LeftCosetOne : (1 : G) LCoset* H = H := by
    refine (ext ?h).symm
    intro x
    constructor
    · intro h1
      rw[LeftCosetClosureMul]
      rw[← one_mul (1⁻¹)]
      rw[MulInv]
      rw[one_mul]
      exact h1
    · intro h2
      rw[LeftCosetClosureMul] at h2
      rw[← one_mul (1⁻¹)] at h2
      rw[MulInv] at h2
      rw[one_mul] at h2
      exact h2
    done

  lemma RightCosetOne : H RCoset* (1 : G) = H := by
    refine (ext ?h).symm
    intro x
    constructor
    · intro h1
      rw[RightCosetClosureMul]
      rw[← one_mul (1⁻¹)]
      rw[MulInv]
      rw[mul_one]
      exact h1
    · intro h2
      rw[RightCosetClosureMul] at h2
      rw[← one_mul (1⁻¹)] at h2
      rw[MulInv] at h2
      rw[mul_one] at h2
      exact h2
    done

  --(Rose) This lemma was created after some futile attempts to prove LeftCosetEqNotDisjointMul, and I realised
  --it was a much needed step to prove this first. The ← direction was extremly trivial as it was just using a
  --previous lemma, however the → direction
  lemma LeftCosetEqIffContained (i j : G) :
  j ∈ i LCoset* H ↔ i LCoset* H = j LCoset* H := by
    constructor
    · intro h
      refine ext ?h
      intro x
      rw[LeftCosetClosureMul] at h
      let α := i⁻¹ * j
      constructor
      · intro k
        let β := i⁻¹*x
        rw[LeftCosetClosureMul] at k
        have e : x = j*α⁻¹*β := by
          simp only [α, β]
          rw[InvBracketsMul, InvInvMul]
          repeat rw[← mul_assoc]
          rw[MulInv, one_mul, MulInv, one_mul]
        rw[LeftCosetClosureMul]
        rw[e]
        repeat rw[← mul_assoc]
        rw[mul_left_inv, one_mul, mul_assoc]
        refine (mul_mem_cancel_left ?h.mp.h).mpr k
        exact Subgroup.inv_mem H h
      · intro k
        let β := j⁻¹*x
        rw[LeftCosetClosureMul] at k
        have e : x = i*α*β := by
          simp only [α, β]
          repeat rw[← mul_assoc]
          rw[MulInv, one_mul, MulInv, one_mul]
        rw[LeftCosetClosureMul]
        rw[e]
        rw[← mul_assoc, ← mul_assoc, ← mul_assoc]
        rw[mul_left_inv, one_mul, mul_assoc]
        exact Subgroup.mul_mem H h k
    · intro h
      rw [h]
      exact ElemInOwnLeftCosetMul H j
    done

  lemma RightCosetEqIffContained (i j : G) :
  j ∈ H RCoset* i ↔ H RCoset* i = H RCoset* j := by
    constructor
    · intro h
      refine ext ?h
      intro x
      rw[RightCosetClosureMul] at h
      let α := j * i⁻¹
      constructor
      · intro k
        let β := x*i⁻¹
        rw[RightCosetClosureMul] at k
        have e : x = β*α⁻¹*j := by
          simp only [α, β]
          rw[InvBracketsMul, InvInvMul]
          repeat rw[mul_assoc]
          rw[mul_left_inv, MulOne, mul_left_inv, MulOne]
        rw[RightCosetClosureMul]
        rw[e]
        repeat rw[mul_assoc]
        rw[MulInv, MulOne, ← mul_assoc]
        refine (mul_mem_cancel_right ?h.mp.h).mpr k
        exact Subgroup.inv_mem H h
      · intro k
        let β := x*j⁻¹
        rw[RightCosetClosureMul] at k
        have e : x = β*α*i := by
          simp only [α, β]
          repeat rw[mul_assoc]
          rw[mul_left_inv, MulOne, mul_left_inv, MulOne]
        rw[RightCosetClosureMul]
        rw[e]
        repeat rw[mul_assoc]
        rw[MulInv, MulOne, ← mul_assoc]
        exact Subgroup.mul_mem H k h
    · intro h
      rw [h]
      exact ElemInOwnRightCosetMul H j
    done

  --Edward
  /-These next 2 theorems were needed for showing that normality
  is the same as having equivalent cosets. This is a result that is neede
  in order to establish a link between the world of cosets and quotient
  groups, which will help later on-/

  theorem MemLeftCoset (g : G): x ∈ H ↔ g * x ∈ g LCoset* H := by
  constructor
  · intro h1
    have e: x LCoset* H = H := by
        have e1: H = (1 : G) LCoset* H := by
          rw[LeftCosetOne]
        have e2: x ∈ H ↔ x ∈ (1 : G) LCoset* H := by
          constructor
          · intro h1h1
            rw[← e1]
            exact h1h1
          · intro h1h2
            rw[← e1] at h1h2
            exact h1h2
        rw[e2] at h1
        rw[LeftCosetEqIffContained] at h1
        rw[← h1]
        nth_rewrite 2 [e1]
        rfl
    rw[LeftCosetEqIffContained]
    rw[← AssocLeftCosetMul]
    rw[e]
  · intro h2
    rw[LeftCosetClosureMul] at h2
    rw[← mul_assoc] at h2
    rw[mul_left_inv] at h2
    rw[one_mul] at h2
    exact h2
  done

  theorem MemRightCoset (g : G): x ∈ H ↔ x * g ∈ H RCoset* g := by
  constructor
  · intro h1
    have e: H RCoset* x = H := by
        have e1: H = H RCoset* (1 : G) := by
          rw[RightCosetOne]
        have e2: x ∈ H ↔ x ∈ H RCoset* (1 : G) := by
          constructor
          · intro h1h1
            rw[← e1]
            exact h1h1
          · intro h1h2
            rw[← e1] at h1h2
            exact h1h2
        rw[e2] at h1
        rw[RightCosetEqIffContained] at h1
        rw[← h1]
        nth_rewrite 2 [e1]
        rfl
    rw[RightCosetEqIffContained]
    rw[← AssocRightCosetMul]
    rw[e]
  · intro h2
    rw[RightCosetClosureMul] at h2
    rw[mul_assoc] at h2
    rw[MulInv] at h2
    rw[MulOne] at h2
    exact h2
  done

  --(Rose)
  lemma LeftCosetEqNotDisjointMul (g i j : G) :
  g ∈ (i LCoset* H) ∧ g ∈ (j LCoset* H) → i LCoset* H = j LCoset* H := by
    intro h
    let ⟨a, b⟩ := h
    have h1 : g LCoset* H = i LCoset* H := by
      rw[LeftCosetEqIffContained] at a
      symm
      exact a
    have h2 : g LCoset* H = j LCoset* H := by
      rw[LeftCosetEqIffContained] at b
      symm
      exact b
    rw [h1] at h2
    exact h2
    done

  lemma RightCosetEqNotDisjointMul (g i j : G) :
  g ∈ (H RCoset* i) ∧ g ∈ (H RCoset* j) → H RCoset* i = H RCoset* j := by
    intro h
    let ⟨a, b⟩ := h
    have h1 : H RCoset* g = H RCoset* i := by
      rw[RightCosetEqIffContained] at a
      symm
      exact a
    have h2 : H RCoset* g = H RCoset* j := by
      rw[RightCosetEqIffContained] at b
      symm
      exact b
    rw [h1] at h2
    exact h2
    done

  --(Rose)
  lemma LeftCosetDisjointMul (g i j : G)
  (h : g ∈ (i LCoset* H) ∧ ¬(g ∈ (j LCoset* H))) :
  (i LCoset* H) ∩ (j LCoset* H) = {} := by
    contrapose h
    refine not_and.mpr ?_
    intro h1
    refine not_not_mem.mpr ?_
    have h2 : ∃ x, x ∈ (i LCoset* H) ∧ x ∈ (j LCoset* H) := by
      refine inter_nonempty.mp ?_
      exact nmem_singleton_empty.mp h
    cases h2 with
    | intro w y =>
      apply LeftCosetEqNotDisjointMul at y
      symm at y
      rw[y]
      exact h1
    done

  lemma RightCosetDisjointMul (g i j : G)
  (h : g ∈ (H RCoset* i) ∧ ¬(g ∈ (H RCoset* j))) :
  (H RCoset* i) ∩ (H RCoset* j) = {} := by
    contrapose h
    refine not_and.mpr ?_
    intro h1
    refine not_not_mem.mpr ?_
    have h2 : ∃ x, x ∈ (H RCoset* i) ∧ x ∈ (H RCoset* j) := by
      refine inter_nonempty.mp ?_
      exact nmem_singleton_empty.mp h
    cases h2 with
    | intro w y =>
      apply RightCosetEqNotDisjointMul at y
      symm at y
      rw[y]
      exact h1
    done


  --Edward
  --we've done most of the immediately relevant stuff for cosets
  --but to define quotient groups we need to show a fact about them and normal subgroups

  theorem CosetsOfNormEq (N : H.Normal) (g : G) : g LCoset* H = H RCoset* g :=
    Set.ext fun a => by --turns = statement into iff
    rw[LeftCosetClosureMul]
    rw[RightCosetClosureMul]
    rw[N.mem_comm_iff] -- statement saying that we have commutativity here due to being normal


  theorem NormalofEqCosets (h : ∀ g : G, g LCoset* H = H RCoset* g) : H.Normal := by
    constructor
    · intro n h1 g
      have e1: g * n  ∈ g LCoset* H := by
        rw[← MemLeftCoset]
        exact h1
      rw[← MulOne (g * n)] at e1
      rw[h] at e1
      rw[← mul_left_inv g] at e1
      rw[← mul_assoc] at e1
      rw[← MemRightCoset] at e1
      exact e1
    done

  theorem NormalIffEqMulCosets: H.Normal ↔ ∀ g : G, g LCoset* H = H RCoset* g := by
    constructor
    · intro h1
      exact fun g ↦ CosetsOfNormEq H h1 g
    · intro h2
      exact NormalofEqCosets H h2
      done

  theorem LeftEqRightQuotientGroup [h: H.Normal]: LeftQuotientGroup G H = RightQuotientGroup G H := by
    unfold RightQuotientGroup
    unfold LeftQuotientGroup
    rw[NormalIffEqMulCosets] at h
    conv =>
      lhs
      congr
      intro G
      rw[h]

      congr
    done

  /-
  variable (c : Set (Set G)) (c := ∀(p : G), p LCoset* H)

  theorem QuotientGroupSetofLeftCosets (g : G) [H.Normal]
  : QuotientGroup G H = c := by
    have e1: g LCoset* H = H RCoset* g := by
      rw[CosetsOfNormEq]

    done
  -/
  --(Rose)(Oh god)

  --variable [H.Normal] [Fintype G] [Fintype H]

  --#check QuotientGroup G H
  --#check Fintype.card (QuotientGroup G H)
  -/

  --(Rose) From here we are at the final strech to proving Lagrange's Theorem. The 2 methods we will try are proving it
  --via the quotient groups as defined about or by using the fact that cosets partition the group

  --(Rose) For the partition method we will start to use Fintypes as the statement of Langrange's Theorem only
  --makes sense for finite groups. Here we quickly show a coset is finite when the group and subgroup are fintypes
  lemma LeftCosetFinTypeMul [Fintype G] [Fintype H] (g : G) :
  (g LCoset* H).Finite := by
    exact toFinite (g LCoset*↑H)
    done

  --(Rose) Next we need to define a set of cosets that we can use to prove partitons.
  --This in particular gave me a lot of trouble for a while as
  def SetOfLeftCosets (H : Set G) : Set (Set G) :=
    Set.image (fun g => g LCoset* H) H

  lemma LeftCosetInSetOfCosets (g : G) : g LCoset* H ∈ SetOfLeftCosets H := by
    unfold SetOfLeftCosets

    done

  lemma LeftCosetsPartitionMul (H : Set G) (c := SetOfLeftCosets H) : Setoid.IsPartition c := by
    unfold Setoid.IsPartition
    constructor
    · let e1 : Set G := 1 LCoset* H
      have he : e1 ∈ c := by
        rw[SetOfLeftCosets] at c
        simp only [mul_right_inj, mul_left_inj, mul_one, self_eq_mul_right, one_mul,
          self_eq_mul_left]

    done


  --(Rose)
  lemma LeftCosetCardEqSubgroupCard [Fintype G] [Fintype H] (g : G) [DecidablePred fun a => a ∈ g LCoset* H]
  [DecidablePred fun b => b ∈ ((fun h => g * h) '' H)]:
  Fintype.card H = Fintype.card (g LCoset* H) := by
    refine (card_image_of_inj_on ?H).symm
    intro x
    intro h1
    intro y
    intro h2
    exact LeftCancelMul g x y
    done


  lemma LeftCosetBijectionMul (g : G) : g LCoset* H ≃ H := by
    rw[LeftCosetMul]



    refine (BijOn.equiv ?f ?h).symm
    · exact fun a ↦ g
    rw [@image_eq_iUnion]

    constructor
    · rw[MapsTo]
      intro x
      intro h
      exact ElemInOwnLeftCosetMul H g
    · constructor
      · refine injOn_iff_injective.mpr ?h.right.left.a

        rw[InjOn]


      · rw[SurjOn]
        rw[LeftCosetMul]


    cases

    done

  --(Rose)Here is one of the main ways I tried and failed to
  /-
  class SetOfLeftCosetsMul ()

  variable {ι : Type*} (s : ι → G) (e : G)

  class SetOfLeftCosetsMul (Q : Set (Set G)) where
    (closure : ∀(g : G), g LCoset* H ∈ Q)

  #check SetOfLeftCosetsMul

  #check IndexedPartition.mk

  instance : IndexedPartition c where

  -/

  lemma LeftCosetsPartitionGroup  : (⨆ g ∈ ↑H, g LCoset* H) = G := by
    sorry
    done

  #check SetOfLeftCosets

  def indexMul [Fintype G] [Fintype H] : ℕ :=
    Fintype.card G / Fintype.card H


  theorem LagrangeMul [Fintype G] [Fintype H] (g : G) :
  Fintype.card H ∣ Fintype.card G := by
    rw [dvd_iff_exists_eq_mul_left]
    let p : Set (Set G) := SetOfLeftCosets H




    --rw [← @iSup_Prop_eq]
    --rw [← @iSup_range']

    done

  --(Rose) This is the most important corollory of Lagrange to prove as it is the one used by the number theory
  --side of the project.
  theorem PowOfCardEqOne [Fintype G] (g : G) :
  g ^ (Fintype.card G) = 1 := by
    let o : ℕ := orderOf g
    let K : Subgroup G := Subgroup.zpowers g
    have h1 : Fintype.card K = o := by
      exact orderOf_eq_card_zpowers.symm
    have h2 : g ^ (Fintype.card K) = 1 := by
      rw[h1]
      exact pow_orderOf_eq_one g
    have h3 : ∃(c : ℕ), Fintype.card G = c*(Fintype.card K) :=by
      rw[← dvd_iff_exists_eq_mul_left]
      exact LagrangeMul K
    cases h3 with
    | intro w h4 =>
      rw[h4]
      rw[mul_comm]
      rw[pow_mul]
      rw[h2]
      exact one_pow w
    done


end CosetsMul

end cosetsMul
/-
section cosetsAdd

  def LeftCosetAdd [AddGroup G] (g : G) (H : Set G) : Set G :=
    Set.image (fun h => g + h) H

  def RightCosetAdd [AddGroup G] (H : Set G) (g : G) : Set G :=
    Set.image (fun h => h + g) H

  notation:65 i:65 "LCoset+" H:65 => LeftCosetAdd i H
  notation:65 H:65 "RCoset+" i:65 => RightCosetAdd H i

  /-
  def LeftCosetEqAdd [AddGroup G] (g h : Set G) (i j : G):=
    i LCoset+ g = j LCoset+ h

  def RightCosetEqAdd [AddGroup G] (i j : G) (g h : Set G) :=
    g RCoset+ i = h RCoset+ j

  -/
  namespace CosetsAdd

  variable (G : Type) [AddGroup G] (H : AddSubgroup G)

  lemma AssocLeftCosetAdd (a b : G) (H : AddSubgroup G) :
  a LCoset+ b LCoset+ H = (a+b) LCoset+ H := by
    sorry
    done

  lemma AssocRightCosetAdd (a b : G) (H : AddSubgroup G) :
  (H RCoset+ a) RCoset+ b = H RCoset+ (a+b) := by
    sorry
    done

  lemma LeftCosetElemImpEqAdd (a b : G) (H : AddSubgroup G) :
  a = b ↔ a LCoset+ H = b LCoset+ H := by
    sorry
    done

  lemma RightCosetElemImpEqAdd (a b : G) (H : AddSubgroup G) :
  a = b ↔ H RCoset+ a = H RCoset+ b := by
    sorry
    done

    --May be more lemmas needed

  -- if h ∈ iH and jH then iH = jH
  lemma LeftCosetEqOrDisjointAdd (g i j : G) (H : AddSubgroup G)
  (h : g ∈ (i LCoset+ H) ∧ g ∈ (j LCoset+ H)) :
  i LCoset+ H = j LCoset+ H := by
    sorry
    done

  lemma RightCosetEqOrDisjointAdd (g i j : G) (H : AddSubgroup G)
  (h : g ∈ (H RCoset+ i) ∧ g ∈ (H RCoset+ j)) :
  H RCoset+ i = H RCoset+ j := by
    sorry
    done

  def indexAdd : ℕ :=
    sorry
    -- number of cosets iH, jH ... that makes up G

  --Langrange's Theorem

end CosetsAdd

end cosetsAdd
-/
--Beginning of Number Theory Side


--Initial very naive/ not lean-optimised/ bad definition trying to make a
--Bézout algorithm, skip to my 24/11/23 timestamp about 80 lines down to
--see the one we actually used, just thought I'd keep this in for the
--sake of showing how far we've come.

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

--Jakub
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

--Jakub
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

--Jakub
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
#eval (gcd_bezout 20 9).2

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

--Jakub
def bez_a (x y : ℕ): ℤ := (gcd_bezout x y).2.1
def bez_b (x y : ℕ): ℤ := (gcd_bezout x y).2.2
def my_gcd (x y : ℕ) : ℕ := (gcd_bezout x y).1

--Jakub
@[simp] lemma gcd_bez_expand (x y : ℕ) : gcd_bezout x y = (my_gcd x y, bez_a x y, bez_b x y) := by
  unfold my_gcd bez_a bez_b
  rfl
  done

--Jakub
@[simp] lemma gcd_bez_zero_left {y : ℕ} : gcd_bezout Nat.zero y = (y, 0, 1) := by
  unfold gcd_bezout
  rfl
  done

--Jakub
@[simp] lemma bez_a_zero_left {y : ℕ} : bez_a Nat.zero y = 0 := by
  unfold bez_a
  simp? says simp only [Nat.zero_eq, gcd_bez_zero_left]
  done

--Jakub
@[simp] lemma bez_b_zero_left {y : ℕ} : bez_b Nat.zero y = 1 := by
  unfold bez_b
  simp? says simp only [Nat.zero_eq, gcd_bez_zero_left]
  done

--Jakub
@[simp] lemma my_gcd_zero_left {y : ℕ} : my_gcd Nat.zero y = y := by
  unfold my_gcd
  simp? says simp only [Nat.zero_eq, gcd_bez_zero_left]
  done

--Jakub
@[simp] lemma bez_a_zero_right {x : ℕ} (h : x ≠ 0) : bez_a x Nat.zero = 1 := by
  unfold bez_a gcd_bezout
  induction x with
  | zero => exact absurd rfl h
  | succ x => simp? says simp only [Nat.zero_eq, Nat.zero_mod, gcd_bez_zero_left, CharP.cast_eq_zero,
    EuclideanDomain.zero_div, mul_zero, sub_zero]
  done

--Jakub
@[simp] lemma bez_b_zero_right {x : ℕ} (h : x ≠ 0) : bez_b x Nat.zero = 0 := by
  unfold bez_b gcd_bezout
  induction x with
  | zero => exact absurd rfl h
  | succ x => simp? says simp only [Nat.zero_eq, Nat.zero_mod, gcd_bez_zero_left]
  done

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

--Jakub
@[simp] lemma my_gcd_self {x : ℕ} : my_gcd x x = x := by
  induction x with
  | zero => apply my_gcd_zero_left
  | succ =>
    unfold my_gcd gcd_bezout
    simp only [Nat.mod_self, gcd_bez_expand, my_gcd_zero_left, bez_a_zero_left, bez_b_zero_left]
  done

--Jakub
@[simp] lemma my_gcd_succ (x y : ℕ) : my_gcd (Nat.succ x) y = my_gcd (y%(Nat.succ x)) (Nat.succ x) := by
  unfold my_gcd
  rfl
  done

--Jakub
@[simp] lemma my_gcd_zero_right {x : ℕ} : my_gcd x Nat.zero = x := by
  unfold my_gcd gcd_bezout
  induction x with
  | zero => rfl
  | succ x => simp? says simp only [Nat.zero_eq, Nat.zero_mod, gcd_bez_zero_left]
  done

--Jakub
@[simp] lemma gcd_bez_zero_right {x : ℕ} (h : x ≠ 0) : gcd_bezout x Nat.zero = (x, 1, 0) := by
  rw[gcd_bez_expand x Nat.zero]
  induction x with
  | zero => exact absurd rfl h
  | succ => simp? says simp only [Nat.zero_eq, ne_eq, Nat.succ_ne_zero, not_false_eq_true, my_gcd_zero_right,
    bez_a_zero_right, bez_b_zero_right]
  done

--28/11/23 - Jakub

--I have discovered the `Nat.gcd.induction` tactic and will apply it to prove that `my_gcd` is equivalent
--to `Nat.gcd` in mathlib, which I will then use to help my proof of Bézout's lemma. I will try also
--using `Nat.gcd.induction` in my proof of Bézout's lemma, since I think it will be helpful. The equality
--of `my_gcd` and `Nat.gcd` gives us all the lemmas in `Mathlib,Data.Nat.GCD.Basic` for free now to apply
--in this proof, so I hope that it will now be feasible for me. I think it will also be useful to prove
--some smaller lemmas like `my_gcd_succ` and `my_gcd_rec` for the `bez_a` and `bez_b` functions.

--Jakub
@[simp] theorem my_gcd_rec (x y : Nat) : my_gcd x y = my_gcd (y % x) x :=
  match x with
  | 0 => by
    have := (Nat.mod_zero y).symm
    simp only [my_gcd_zero_left, Nat.mod_zero, my_gcd_zero_right]
  | x + 1 => by exact (my_gcd_succ x y).symm

--Jakub
@[simp] theorem dvd_my_gcd : k ∣ x → k ∣ y → k ∣ my_gcd x y := by
  induction x, y using Nat.gcd.induction with intro kx ky
  | H0 y => rw [my_gcd_zero_left]; exact ky
  | H1 y x _ IH => rw [my_gcd_rec]; exact IH ((Nat.dvd_mod_iff kx).2 ky) kx
  done

--Jakub
theorem my_gcd_eq_gcd (x y : ℕ) : Nat.gcd x y = my_gcd x y := by
  induction x, y using Nat.gcd.induction with
  | H0 y =>
    rw [my_gcd_zero_left, Nat.gcd_zero_left]
  | H1 x y _ ih =>
    rw [Nat.gcd_rec, my_gcd_rec]
    exact ih
  done

--Jakub
@[simp] lemma bez_a_succ (x y : ℕ) : bez_a (Nat.succ x) y = bez_b (y%(Nat.succ x)) (Nat.succ x) - y/(Nat.succ x) * bez_a (y%(Nat.succ x)) (Nat.succ x) := by
  unfold bez_a bez_b
  rfl
  done

--Jakub
@[simp] lemma bez_b_succ (x y : ℕ) : bez_b (Nat.succ x) y = bez_a (y%(Nat.succ x)) (Nat.succ x) := by
  unfold bez_a bez_b
  rfl
  done

--Jakub
@[simp] lemma bez_a_rec (x y : ℕ) (h : 0 < x) : bez_a x y = bez_b (y%x) x - y/x * bez_a (y%x) x := by
  match x with
  | 0 => contradiction
  | x + 1 => exact bez_a_succ x y
  done

--Jakub
@[simp] lemma bez_b_rec (x y : ℕ) (h : 0 < x): bez_b x y = bez_a (y%x) x := by
  match x with
  | 0 => contradiction
  | x + 1 => exact bez_b_succ x y
  done

--29/11/23 - Jakub

--I have managed to reduce the proof of Bézout's lemma to now simply rearranging the following theorem
--from mathlib, I have proved the rest of `bez_rec` now excluding this, which was previously entirely
--`sorry`-d out and is necessary for my proof of Bézout's lemma
#check Int.ediv_add_emod

--Jakub
@[simp] lemma my_ediv_add_emod (x y : ℤ) : y-x*(y/x) = (y%x) := by
  nth_rewrite 1 [← Int.ediv_add_emod y x]
  simp only [add_sub_cancel']
  done

--Jakub
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
  done

--Jakub
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
    done

--Jakub
--Statement of Bézout's lemma using `Nat.gcd`
theorem bezout (x y : ℕ) : (bez_a x y)*x+(bez_b x y)*y=(Nat.gcd x y) := by
  rw [my_gcd_eq_gcd]
  apply bez_a_left_mul_bez_b_right_eq_my_gcd
  done

--30/11/23 - Jakub

--I have now finally managed to fully prove Bézout's lemma without any remaining `sorry`s. Next I will
--begin work on defining `ℤ/nℤ` as a ring and use this to prove the Chinese remainder theorem
--(Sun Tzu's theorem). The proof of Bézout's lemma proved to be far more difficult than I had anticipated,
--and I now see that I need to be very careful defining things in such a way to make the proofs as
--simple as possible.

--Sun Tzu's Theorem/Classical Chinese Remainder Theorem

--11/12/23 - Jakub

--Unfortunately, the modulo notation from mathlib comes from a file where the CRT is already proven, so I will define
--it and prove basic features about it myself, as we had initially planned

--The following two lines of LEAN code are almost identical to mathlib, but I will prove the basic lemmas myself.
--Note the use of different syntax to mathlib to avoid accidentally using their proofs.

--Jakub
def Mod_eq (n a b : ℕ) := a%n = b%n
notation:50 a "≡" b " [mod " n "]" => Mod_eq n a b

--It turned out that most of the lemmas follow trivially from the properties of `=`, though I had to do a fair
--amount of adjusting the statements slightly to get them in the same form to simply exact these properties.

--Jakub
@[simp] lemma Mod_eq_rfl {n a: ℕ} : a ≡ a [mod n] := by
  rfl
  done

--Jakub
@[simp] lemma Mod_eq_symm {n a b: ℕ} : a ≡ b [mod n] → b ≡ a [mod n] := by
  exact Eq.symm
  done

--Jakub
@[simp] lemma Mod_eq_trans {n a b c : ℕ} : a ≡ b [mod n] → b ≡ c [mod n] → a ≡ c [mod n] := by
  exact Eq.trans
  done

--Jakub
@[simp] lemma Mod_eq_self {n : ℕ} : n ≡ 0 [mod n] := by
  rw [Mod_eq]
  rw [Nat.zero_mod]
  rw [Nat.mod_self]
  done

--Jakub
@[simp] lemma Mod_eq_zero_iff_dvd {n a : ℕ} : a ≡ 0 [mod n] ↔ n ∣ a := by
  rw [Mod_eq]
  rw [Nat.zero_mod]
  rw [Nat.dvd_iff_mod_eq_zero]
  done

--Jakub
@[simp] lemma Mod_eq_add_mul (n a b: ℕ) : a + b*n ≡ a [mod n] := by
  rw [Mod_eq]
  rw [Nat.add_mod]
  simp? says simp only [Nat.mul_mod_left, add_zero, Nat.mod_mod]
  done

--Unfortunately the above results proved less useful than I had foreseen, but I will keep them here in case they
--are required further down the line.

--Below I have defined a function `classical_crt` to give a `x` such that, given `m,n,a,b ∈ ℕ`, we have
--`x ≡ a [mod m], x ≡ b [mod n]`, it  remains to prove this property of the construction.
--I have used the syntax of a set with a condition like Mathlib uses for the chinese remainder theorem.
--I initially experimented with defining `x` then separately proving that it satisfied the required condition
--imposed here, but navigating the if statements proved cumbersome, so I opted to  arrange it like so.
--I believe that understanding how to use this syntax will prove useful in the future, and the proof is my own.
--So far I have completed both the zero cases and am currently working on the non-trivial cases.

--13/12/23 - Jakub

--I have succesfully reduced the proof of the Classical Chinese Remainder Theorem to the lemmas `my_mod_mod_lcm`,
--`bez_a_mod` and `bez_b_mod`, which I will now work on proving.

--We'll need these ones!!
#check Nat.mul_mod
#check Nat.add_mul_mod_self_right
#check Int.toNat
#check Int.add_mul_emod_self

--14/12/23 - Jakub

--Today I have completed the proof of the Classical Chinese Remainder Theorem. It proved tricky to work around
--the interactions between integers and natural numbers here; fortunately, most of the results I needed were small
--and either contained in mathlib already or (as below) the proofs for similar lemmas in mathlib worked to help
--in the cases I required. The proofs for `int_to_nat_mul_nat` and `int_to_nat_mod_nat` are not my own so when
--marking please ignore those. I do not understand why these results are not already in mathlib, since there
--is a corresponding lemma `Int.toNat_add_nat` for addition already in mathlib, from which I have taken the proof
--almost verbatim and it works perfectly here. I have treated these results as though they were any other basic
--result from mathlib I would use.

lemma int_to_nat_mul_nat (x : ℤ) (y : ℕ) (h : 0 ≤ x): (Int.toNat x) * y = Int.toNat (x * y) := by
  match x, Int.eq_ofNat_of_zero_le h with | _, ⟨_, rfl⟩ => rfl
  done

lemma int_to_nat_mod_nat (x : ℤ) (y : ℕ) (h : 0 ≤ x): (Int.toNat x) % y = Int.toNat (x % y) := by
  match x, Int.eq_ofNat_of_zero_le h with | _, ⟨_, rfl⟩ => rfl
  done

--Below is again original work.
--It proved necessary to prove these smaller auxiliary lemmas for the `bez_a_mod` and `bez_b_mod` theorems, since
--I found it difficult working around the restrictions of naturals and integers in lean, as the differences
--between the two are far clearer then they are on pen-and-paper proofs. Despite `bez_a m n % n` being a natural
--number, I was required to use the `Int.toNat` function to cast them back into the naturals, which made what should
--have been simple statements become non-trivial to prove, which is why I had to write the two lemmas above.

--Jakub
@[simp] lemma my_mod_mod_of_lcm (x m n : ℕ) : (x % (Nat.lcm m n)) % m = x % m := by
  have h : m ∣ (Nat.lcm m n) := by
    apply Nat.dvd_lcm_left
  rw [Nat.mod_mod_of_dvd]
  exact h
  done

--Jakub
--very useful simple statement.
@[simp] theorem bez_of_coprime (m n : ℕ) (h : Nat.Coprime m n) : bez_a m n * m + bez_b m n * n = 1 := by
  rw [bezout]
  rw [Nat.coprime_iff_gcd_eq_one.1]
  rfl
  exact h
  done

--Jakub
--slightly simpler statements of `bez_a_mod` and `bez_b_mod`, useful for the full proofs.
lemma bez_a_mod_aux (m n : ℕ) (h : Nat.Coprime m n): ((bez_a m n % n) * m) % n = 1 % n := by
  rw [← bez_of_coprime m n]
  · rw [Int.mul_emod]
    rw [Int.emod_emod]
    rw [← Int.mul_emod]
    rw [Int.add_mul_emod_self]
  exact h
  done

--Jakub
lemma bez_b_mod_aux (m n : ℕ) (h : Nat.Coprime m n): ((bez_b m n % m) * n) % m = 1 % m := by
  rw [← bez_of_coprime m n]
  · rw [Int.mul_emod]
    rw [Int.emod_emod]
    rw [← Int.mul_emod]
    rw [add_comm]
    rw [Int.add_mul_emod_self]
  exact h
  done

--Jakub
theorem bez_a_mod (m n : ℕ) (h : Nat.Coprime m n) (hn : ¬n=0) : (Int.toNat (bez_a m n % n)) * m ≡ 1 [mod n] := by
  rw [Mod_eq]
  have h1 : 0 ≤ bez_a m n % n := by
    apply Int.emod_nonneg
    rw [← ne_eq] at hn
    rw [Nat.cast_ne_zero]
    exact hn
  rw [int_to_nat_mul_nat]
  · rw [int_to_nat_mod_nat]
    rw [bez_a_mod_aux]
    · rw [← int_to_nat_mod_nat]
      rw [Int.toNat_one]
      norm_num
    exact h
    have h2 : 0 ≤ (m : ℤ) := by
      apply Nat.cast_nonneg
    have h3 : 0 ≤ bez_a m n % ↑n * ↑m := by
      apply mul_nonneg
      exact h1
      exact h2
    exact h3
  exact h1
  done

--Jakub
theorem bez_b_mod (m n : ℕ) (h : Nat.Coprime m n) (hm : ¬m=0) : (Int.toNat (bez_b m n % m)) * n ≡ 1 [mod m] := by
  rw [Mod_eq]
  have h1 : 0 ≤ bez_b m n % m := by
    apply Int.emod_nonneg
    rw [← ne_eq] at hm
    rw [Nat.cast_ne_zero]
    exact hm
  rw [int_to_nat_mul_nat]
  · rw [int_to_nat_mod_nat]
    rw [bez_b_mod_aux]
    · rw [← int_to_nat_mod_nat]
      rw [Int.toNat_one]
      norm_num
    exact h
    have h2 : 0 ≤ (n : ℤ) := by
      apply Nat.cast_nonneg
    have h3 : 0 ≤ bez_b m n % ↑m * ↑n := by
      apply mul_nonneg
      exact h1
      exact h2
    exact h3
  exact h1
  done

--Jakub
def classical_crt (m n a b : ℕ) (h : Nat.Coprime m n) : {x // x ≡ a [mod m] ∧ x ≡ b [mod n]} :=
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
      ⟨(a*(Int.toNat (bez_b m n % m))*n+b*(Int.toNat (bez_a m n % n))*m) % (Nat.lcm m n), by
        --At this point in the proof, there are just a few tricky aspects to prove. I have created individual
        --lemmas for these steps above, and highlighted where they are used, each other step uses basic results.
        constructor
        · rw [Mod_eq]
          rw [my_mod_mod_of_lcm] --Here my lemma is used
          rw [Nat.add_mul_mod_self_right]
          rw [mul_assoc, Nat.mul_mod]
          rw [bez_b_mod] --Here my lemma is used
          rw [← Nat.mul_mod]
          rw [mul_one]
          exact h
          exact hm
        rw [Mod_eq]
        rw [Nat.lcm_comm]
        rw [my_mod_mod_of_lcm] --Here my lemma is used
        rw [add_comm]
        rw [Nat.add_mul_mod_self_right]
        rw [mul_assoc, Nat.mul_mod]
        rw [bez_a_mod] --Here my lemma is used
        rw [← Nat.mul_mod]
        rw [mul_one]
        exact h
        exact hn
        ⟩

--With these we can prove the `Algebraic Chinese Remainder theorem` for coprime m,n, i.e. `ℤ/mnℤ = ℤ/mℤ × ℤ/nℤ`
--But for this we will first need the group theory side of the project to define such an object as `ZMod n`

--With this statement we can prove the `multiplicity` of the Euler Totient function for coprime m n, i.e. phi(mn)=phi(m)*phi(n)

--After we prove these we will have all the tools from number theory to collaborate with the group theory side to prove
--Euler's theorem and Fermat's little theorem.

-- Katie

-- Now to utilise Bezout's lemma in some smaller lemmas building our number theory library.
-- After trying to rephrase Euclid's lemma many different ways, I came to the conclusion that
-- it would be easier to separate the cases of which variable was coprime to p into their own
-- respective theorems. Following this, I needed even more preceding results regarding prime divisors.
-- Structuring the proof of Euclid's lemma was fairly difficult;

@[simp] lemma bezout_one {p n : ℕ}(h_1 : (Nat.gcd p n) = (1 : ℕ)) : (bez_a p n)*(p : ℕ)+(bez_b p n)*n= (1 : ℕ)  := by
  rw[bezout]
  rw[h_1]
  done

@[simp] lemma bezout_one_nat {p n : ℕ}(h_1 : (Nat.gcd p n) = (1 : ℕ)) : Int.toNat ((bez_a p n)*p+(bez_b p n)*n)= (1 : ℕ) := by
  rw[bezout_one]
  rw[Nat.cast_one]
  rw[Int.toNat_one]
  · exact h_1
  done

@[simp] lemma one_bezout {p n : ℕ}(h_1 : (Nat.gcd p n) = 1) : (1 : ℕ) = (bez_a (p : ℕ) n)*(p : ℕ)+(bez_b (p : ℕ) n)*n  := by
  rw[bezout]
  rw[← h_1]
  done

@[simp] lemma bezout_prime {p n : ℕ}(h_1 : (Nat.gcd (p : ℕ) n) = p) : (bez_a (p : ℕ) n)*(p : ℕ)+(bez_b (p : ℕ) n)*n= p  := by
  rw[bezout]
  rw[h_1]
  done

@[simp] lemma prime_bezout {p n : ℕ}(h_1 : (Nat.gcd (p : ℕ) n) = p) : (p : ℕ) = (bez_a (p : ℕ) n)*(p : ℕ)+(bez_b (p : ℕ) n)*n  := by
  rw[bezout]
  norm_cast
  rw[h_1]
  done

@[simp] lemma gen_bezout {p n : ℕ} : (Nat.gcd  (n : ℕ) (p : ℕ)) = (bez_a (n : ℕ) (p : ℕ))*(n : ℕ)+(bez_b (n : ℕ) (p : ℕ)) *(p : ℕ) := by
  rw[bezout]
  done

@[simp] lemma gcd_nat_prime {p m : ℕ}(h: Nat.Prime p) : (Nat.gcd p m = 1) ∨ (Nat.gcd p m  = p):= by
  intros
  refine (Nat.dvd_prime ?pp).mp ?_
  exact h
  exact Nat.gcd_dvd_left p m
  done

@[simp] lemma gcd_nat_prime_comm {p m : ℕ}(h: Nat.Prime p): (Nat.gcd p m = p) ∨ (Nat.gcd p m  = 1):= by
  rw[← or_comm]
  apply gcd_nat_prime
  exact h
  done

@[simp] lemma gcd_nat_prime_elt {p m : ℕ}(h: Nat.Prime p) : (Nat.gcd p m ∈ [1,p]) := by
  refine List.mem_pair.mpr ?_
  apply gcd_nat_prime
  exact h
  done

-- I struggled a great deal with many of these lemmas due to Lean "nat-casting" my prime variable so that, instead
-- of working with a Nat.Prime, I had to show that the prime casted to the naturals was a nat.prime itself, which
-- had no clear work-around. Someone advised me to phrase my theorems such that p was a variable in the naturals,
-- but, by hypothesis it was a Nat.Prime. This simple solution hadn't occured to me, despite having attempted many
-- different ways to phrase that {p : Nat.Primes}{p : Nat}.

-- Looking back at these whilst adding comments just before submission, it is quite humorous the extent to which LEAN
-- can stump you despite the simplest of work-arounds. I apologise for there being so many lemmas that are equivalent:
-- I simply didn't know any better at the time, and felt more comfortable applying lemmas directly, than fiddling with them
-- within a proof.

@[simp] lemma gcd_one_true {p m : ℕ}(h: Nat.Prime p) : (Nat.gcd p m = 1) → ¬(Nat.gcd p m = p):= by
  intro h1
  rw[h1]
  rw[← ne_eq]
  apply Ne.symm
  apply Nat.Prime.ne_one
  exact h
  done

@[simp] lemma gcd_one_false {p m : ℕ}(h: Nat.Prime p) : ¬(Nat.gcd p m = 1) → (Nat.gcd p m = p):= by
  rw[← or_iff_not_imp_left]
  apply gcd_nat_prime
  · exact h
  done

@[simp] lemma gcd_prime_true {p m : ℕ}(h: Nat.Prime p) : (Nat.gcd p m = p) → ¬(Nat.gcd p m = 1):= by
  intro h1
  rw[h1]
  rw[← ne_eq]
  apply Nat.Prime.ne_one
  exact h
  done

@[simp] lemma gcd_prime_false {p m : ℕ}(h: Nat.Prime p): ¬(Nat.gcd p m = p) → (Nat.gcd p m = 1):= by
  rw[← or_iff_not_imp_left]
  apply gcd_nat_prime_comm
  exact h
  done

@[simp] lemma gcd_eq_p {p x : ℕ} : (Nat.gcd p x = p) ↔ ((p : ℕ)∣ x) := by
  constructor
  · intro h1
    rw[← h1]
    exact Nat.gcd_dvd_right (↑p) x
  · intro h2
    exact Nat.gcd_eq_left h2
  done

@[simp] lemma gcd_eq_1 {p x : ℕ}(h: Nat.Prime p) : (Nat.gcd p x = 1) ↔ ¬((p : ℕ) ∣ x) := by
  constructor
  · intro h1
    refine imp_false.mp ?mp.a
    apply gcd_one_true at h1
    intro h2
    apply gcd_prime_false at h1
    rw[← gcd_eq_p] at h2
    apply gcd_prime_true at h2
    rw[h1] at h2
    rw[← ne_eq] at h2
    exact h2 rfl
    exact h
    exact h
    exact h
  · intro h3
    contrapose h3
    simp
    apply gcd_one_false at h3
    rw[gcd_eq_p] at h3
    · exact h3
    · exact h
  done

#check int_to_nat_mul_nat
#check Int.toNat_add_nat
#check Nat.dvd_add

theorem euclid_l1_coprime {p m n : ℕ}(h: Nat.Prime p)(h1 : p ∣ m*n)(h2 : ¬(p ∣ m)) : (p ∣ n) := by
  rw[← gcd_eq_1] at h2
  rw[← mul_one n]

  rw[Nat.gcd_eq_gcd_ab]

  rw[← Int.coe_nat_gcd] at h2

  rw[Int.gcd_eq_gcd_ab] at h2

Int.gcd_eq_gcd_ab
Int.coe_nat_gcd
Int.gcd_eq_natAbs
/-
theorem euclid_l1_coprime {p m n : ℕ}(h: Nat.Prime p)(h_n : p < n)(h_m : p < m)(h_1 : p ∣ m*n)(h_2 : ¬(p ∣ m)) : (p ∣ n):= by
 -- a*p + b*m = 1
 -- a*p*n + b*m*n = n
 -- p ∣ a*p*n, p ∣ b*m*n => p ∣ n
  intros
  rw[← gcd_eq_1] at h_2
  rw[← mul_one n]
  apply bezout_one_nat at h_2
  rw[← h_2]
  rw [mul_comm, int_to_nat_mul_nat, mul_comm]
  rw [mul_add]
  apply dvd_int_to_nat_add
  exact h
  apply dvd_add_1
  exact h
  apply And.intro
  · rw[mul_comm]
    rw[mul_assoc]
    rw[mul_comm]
    rw[mul_assoc]
    rw[← int_to_nat_mul]
  -- rewrite gcd p m as its bezout identity: ∃ x,y s.t. mx + py =1
  -- n = n(1) = n(mx + py)
  sorry
-/

--21/01/21 - Jakub

--Filling out sorry's left earlier while waiting for ZMod lemmas to complete proof of Euler Totient theorem.
--Unfortunately my idea for a proof of this did not line up with Katie's so I did not end up using the helpful lemmas
--that she proved before. It also turned out that some of the assumptions she was working with were not required for
--my proof, so they have been removed from the statement of Euclid's theorem, in order for it to apply more generally.
--Katie wanted me to leave in her unfinished proof (above) to complete later once we have finished our initial goal.

--Jakub
theorem euclid_left_coprime {p m n : ℕ}(h: Nat.Prime p)(h1 : p ∣ m*n)(h2 : ¬(p ∣ m)) : (p ∣ n):= by
  rw [Nat.dvd_mul] at h1
  let ⟨x, y, h'⟩ := h1
  let ⟨mario, ⟨luigi, bowser⟩⟩ := h'
  have new_super_mario_bros_wii : Irreducible p := by
    rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
    exact h
  have super_mario_galaxy : IsUnit x ∨ IsUnit y := by
    apply Irreducible.isUnit_or_isUnit
    exact new_super_mario_bros_wii
    apply Eq.symm
    exact bowser
  have super_mario_galaxy_2 : x = 1 ∨ y = 1 := by
    rw [← Nat.isUnit_iff, ← Nat.isUnit_iff]
    exact super_mario_galaxy
  cases super_mario_galaxy_2
  · have : x=1 := by assumption
    rw [this] at bowser
    rw [one_mul] at bowser
    rw [bowser] at luigi
    exact luigi
  · have : y=1 := by assumption
    rw [this] at bowser
    rw [mul_one] at bowser
    rw [bowser] at mario
    contradiction
  done

--Now we have everything to prove Euclid's lemma: if p divides a composite number m*n, then it must divide one of m or n.
--After exploring different ways to phrase this, coming across the "or_iff_not_imp_right" lemma saved the day, and - after
--learning how to apply it, which was a task in of itself - simplified the theorem so that I could simply apply the above lemma
--for the result.

-- Katie
theorem euclid {p m n : ℕ}(h: Nat.Prime p): ((p : ℕ) ∣ m*n) → ((p : ℕ) ∣ n) ∨ ((p : ℕ) ∣ m) := by
  intro h1
  refine or_iff_not_imp_right.mpr ?_
  apply euclid_left_coprime
  · exact h
  · exact h1
  done

-- Katie

-- Structuring the proof of Euclid's lemma was fairly difficult; I knew how to prove it easily
-- by hand with the theorems listed above in just a couple lines, but constructing a sort of contradiction
-- (i.e. either gcd p n = 1 or gcd p m = 1, but can't have both occur simultaneously and wanting to structure
-- the proof like suppose p ∣ m, and then supose p ∣ n) was very new to me.

/-
theorem gen_euclid {d m n : ℕ} (h1 : d ∣ m * n) (h2 : Nat.gcd m d = 1) : d ∣ n := by
  -- a*m + b*d = 1
  -- a*m*n + b*d*n = n
  -- d∣ m*n, d ∣ d => d ∣ n
  rw[← mul_one n]
  rw[← bezout_one_nat]
-/

--04/02/24 - Jakub
--Filled out Katie's sorry'd out `gen_euclid`, her unfinished proof is commented out above.
theorem gen_euclid {d m n : ℕ} (h1 : d ∣ m * n) (h2 : Nat.gcd m d = 1) : d ∣ n := by
  cases d with
  | zero =>
    rw [Nat.zero_eq, zero_dvd_iff]
    rw [Nat.gcd_zero_right] at h2
    rw [h2] at h1
    rw [Nat.zero_eq, zero_dvd_iff, Nat.one_mul] at h1
    exact h1
  | succ d =>
    rw [Nat.dvd_mul] at h1
    let ⟨y,⟨z,h'⟩⟩ := h1
    let ⟨hy,⟨ hz,hyz⟩⟩ := h'
    have : y ∣ d.succ := by
      apply dvd_of_mul_right_eq z; exact hyz
    have hy' : y = 1 := by
      rw [← Nat.eq_one_of_dvd_coprimes]
      · rw [Nat.coprime_iff_gcd_eq_one]
        exact h2
      · exact hy
      · exact this
    rw [hy', one_mul] at hyz
    rw [hyz] at hz
    exact hz
  done

-- Katie: laying out the land

-- 11/01/24 - Jakub filled out the sorry here
theorem coprime_mult {a b : ℕ}(ha: (Nat.gcd a m)=1) : ((Nat.gcd b m)=1) → ((Nat.gcd (a*b) m)=1) := by
  intro hb
  have h : Nat.gcd (a*b) m ∣ Nat.gcd a m * Nat.gcd b m := by
    rw [Nat.gcd_comm (a*b) m, Nat.gcd_comm a m, Nat.gcd_comm b m]
    apply Nat.gcd_mul_dvd_mul_gcd
  rw [ha, hb] at h
  rw [mul_one] at h
  rw [Nat.dvd_one] at h
  exact h
  done
-- Katie

open BigOperators
def fun_sum_of_divisors_1 (n : ℕ) : ℕ := ∑ d in Nat.divisors n, d
-- Defining the sum of divisors function took a lot of trial and erroe/tweaking in the syntax, but with the help of the
-- module leader it became clear that, for the sum function to work, I needed to "open BigOperators" - it is a relief to
-- see that the finite sets are not an issue as of yet.

#eval fun_sum_of_divisors_1 4


-- We want to demonstrate the multiplicity of the totient function. I have essentially used the totient
-- function definition from Mathlib, due to it being uncooperative when written in alternative forms
-- which would coincide with our preexisting lemmas better.

def my_totient (n : ℕ) : ℕ :=
  ((Finset.range n).filter n.Coprime).card

#eval my_totient (7)

--notation:69 "φ(n")  => my_totient (n)

--#eval φ (7)

/-
--We were not able to prove the algebraic version of the chinese remainder theorem (see `ZMod.chineseRemainder`)
--of which the following is a corollary. Fortunately, it is not required below.

theorem my_tot_mul (m n : ℕ) : (my_totient (m))*(my_totient (n)) = (my_totient (m*n)) := by
  --need : algebraic CRT for 2 variables
  sorry
-/

-- To prove my_totient(p)=p-1, we will need specfific results about the Finset.range intersected with coprimes of p;
-- specifically that 0 is the only element to be removed from the filter when p is prime.

--Katie & Jakub
lemma dvd_less_than_nat (m n : ℕ) (h : m ∣ n) (h_n : n < m) : n = 0 := by
  rw[dvd_def] at h
  let ⟨a,b⟩ := h
  have : ¬(a=0) → m ≤ m*a  := by
    intro h_1
    conv at h_1 => rw[← ne_eq] ; rw[Nat.ne_zero_iff_zero_lt]
    apply Nat.le_mul_of_pos_right
    exact h_1
  --25/01/24 - Katie's proof finished by Jakub
  --Trying to show that `a` has to be zero, will use cases to get a contradiction when `a≠0`
  cases' a with x
  · have : m * Nat.zero = 0 := by rw [Nat.zero_eq, mul_zero]
    rw [this] at b
    exact b
  · have hsucc : ¬(Nat.succ x = 0) := by
      rw [← ne_eq]
      apply Nat.succ_ne_zero
    have : m ≤ m * Nat.succ x := by
      apply this
      exact hsucc
    have : n < m * Nat.succ x := by
      calc
        n < m := by exact h_n
        m ≤ m * Nat.succ x := by exact this
    have : n < n := by
      rw [← b] at this
      exact this
    have : ¬n=n := by
      apply ne_of_lt
      exact this
    exact absurd rfl this
  --end of Jakub work
  --I would imagine that this proof was not particularly efficient but I wanted practice using the `calc` tactic
  --as it seems useful in mathlib for some proofs later on.
  done

-- Katie
theorem nat_gcd_prime_prime (p a : ℕ)(h_a : a < p) (h : Nat.gcd p a = p) : a = 0 := by
  rw[gcd_eq_p] at h
  apply dvd_less_than_nat at h
  rw[h]
  exact h_a
  done

--Katie
theorem prime_coprime (p : ℕ) (h_p : Nat.Prime p) : ((Finset.range p).filter p.Coprime) = (Finset.range p) \ {0} := by
  refine Finset.ext ?_
  intro a
  constructor
  · intro h
    simp only [Finset.mem_range, not_lt, nonpos_iff_eq_zero, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rw [←Finset.mem_range]
      exact Finset.mem_of_mem_filter a h
    · rw[Finset.mem_filter] at h
      intro h_1
      conv at h => unfold Nat.Coprime; rw[h_1]; rw[Nat.gcd_zero_right]
      let ⟨_,b⟩ := h
      apply Nat.Prime.ne_one at b
      apply b
      exact h_p
  · intro h
    simp only [Finset.mem_range, not_lt, nonpos_iff_eq_zero, Finset.mem_sdiff, Finset.mem_singleton] at h
    simp only [Finset.mem_range, ne_eq, Finset.mem_filter]
    unfold Nat.Coprime
    let ⟨c,d⟩:=h
    constructor
    · exact c
    · apply gcd_prime_false
      · exact h_p
      · intro h_1
        apply nat_gcd_prime_prime at h_1
        conv at d => rw[←h_1]; simp
        apply d
        exact c
  done

--Katie
@[simp] lemma finset_one : Finset.range 1 = {0} := by
  rfl; done

--Katie
theorem my_tot_prime (p : ℕ) (h : Nat.Prime p): (my_totient (p)) = (p-1) := by
  unfold my_totient
  rw[prime_coprime]
  rw[← finset_one]
  rw[Finset.card_sdiff]
  rw[Finset.card_range]
  rw[Finset.card_range]
  simp only [Finset.range_one, Finset.singleton_subset_iff, Finset.mem_range]
  exact Nat.Prime.pos h
  exact h
  done

--16/01/24 - Jakub

--While waiting on the completion of the required definitions and properties of `ZMod`, and
--the statement and proof of `Lagrange's theorem` from the group theory side of the project, Katie stated and sorry'd
--Euler's totient theorem in order for me to be able to complete Fermat's Little Theorem as a corollary. We will be
--working to complete the Number Theory side of theproject from both ends now, I will be working backwards from
--Fermat's little theorem and Katie will be working forwards from what has already been proven by us.

--18/01/24 - Jakub

--The required parts of `ZMod` are proving very difficult for the group theory side of the project, so we will be
--helping as best we can with our limited experience working with groups in LEAN. If we have not got close enough
--to what we need as we approach the final project deadline, we will be forced to use the `ZMod` that is already
--contained withing mathlib, which we originally tried to avoid since it contained a proof of the algebraic CRT early
--on, which we wanted to prove ourselves, and was a significant motivation for many theorems earlier in this file.

--19/01/24 - Jakub

--Due to being unable to import the incomplete `Grps.lean` file into `NumTheory.lean`, we were forced to concatenate
--our two files into one, titled `LagrangeProject.lean` in order to use theorems from the Group theory file in the
--number theory file before the group theory team removed all the errors from their file.

--One such lemma we have taken is
#check CosetsMul.PowOfCardEqOne
--which is vital to the completion of Euler's Totient Theorem.

--Jakub
--This lemma is a modified version of one from ZMod.Basic to work with our definition of `mod`
lemma zmod_eq_iff_Mod_eq_nat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [mod n] := by
  cases n
  · rw [Mod_eq]
    rw [Int.coe_nat_inj']
    simp only [Nat.zero_eq, Nat.mod_zero]
  · rw [Fin.ext_iff, Mod_eq, ← ZMod.val_nat_cast, ← ZMod.val_nat_cast]
    exact Iff.rfl
  done

lemma my_tot_zero : my_totient (0) = 0 := by
  rfl; done

-- Katie
-- Trying to tie Zmod units to the totient function (the main bridge to being able to apply Lagrange) seems
-- to mostly be working around equating Fintypes and Finsets. For example, in the zmod_units_equiv theorem, the
-- finset was changed into { x // x ∈ Finset.filter (Nat.Coprime n) (Finset.range n) }, which is now marked as a
-- subtype. I am hoping it won't be too difficult to work around this!
-- Reading through ZMod.Basic, it's clear that some of our goals are in line with the use of .val
-- and results about units; not sure what is appropriate to use just yet.

#eval (6 : ZMod 10).val
#eval (13 : ZMod 10).val
#eval (-26 : ZMod 10).val
#eval (8 : ZMod 10).inv
#eval (33 : ZMod 10).inv
-- It took some time to understand the ZMod Mathlib functions, and matching everything with my own knowledge of how the ZMod n ring works.
-- Would like to create an isomorphism between units of ZMod n and {x : ZMod n // Nat.Coprime x.val n} so that we can
-- say the cardinalities are the same. For this, we need to construct our own isomorphism (heavily inspired by the Mathlib version)
-- using zmod_unit_val_coprime and zmod_unit_of_coprime.
-- After lots of deliberation, we decided to utilise mathlib's definition of .val, but construct our own inverse function (using Jakub's
-- results for Bezout's lemma) and hopefully create original proofs for ZMod.Basic results that we will need. Hopefully it isn't too confusing
-- for us to pick and choose results to use from the imported ZMod.Basic file.

--23/01/24 - Jakub

--We want to use parts of `ZMod` in our proof of the Euler Totient function, one such aspect is the use of the inverse
--as defined in `ZMod.Basic`. We have seen that in the proofs and definitions there is significant use of the xgcd
--algorithm in mathlib, analagous to my own `gcd_bezout` function, so we have decided to rewrite some key results.

--Using my `bez_a_mod_aux` and mathlib's definition as a base, we will define our own inverse function for elements
--of ZMod. The definition is the same as mathlib's, but using my own `bez_a` instead of mathlib's `Nat.gcdA`.
--The proof required some tweaks due to casting errors and the statement of my `bezout` theorem not being exactly
--the same as the one in mathlib. The simple lemma `bez_is_zmod_inv` was necessary for part of `my_mul_zmod_inv_eq_gcd`
--which is the main original contribution to this section, as well as the complete dependence on `gcd_bezout` and its
--following results as defined and proven above.

def my_zmod_inv : ∀ n : ℕ, ZMod n → ZMod n
  | 0, i => Int.sign i
  | n+1, i => bez_a i.val (n+1)

lemma bez_is_zmod_inv (n : ℕ) (a : ZMod n) (h : 0 < n) : my_zmod_inv n a = bez_a a.val n := by
  match n with
  | 0 => contradiction
  | n+1 => rfl
  done

theorem my_zmod_inv_zero : ∀ n : ℕ, my_zmod_inv n (0 : ZMod n) = 0
  | 0 => Int.sign_zero
  | n+1 =>
    show (bez_a _ (n+1) : ZMod (n+1)) = 0 by
      rw [ZMod.val_zero]
      rw [bez_a_zero_left]
      rfl
      done

theorem my_mul_zmod_inv_eq_gcd {n : ℕ} (a : ZMod n) : a * (my_zmod_inv n a) = Nat.gcd a.val n := by
  cases' n with n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * (my_zmod_inv n.succ a) = a * (my_zmod_inv n.succ a) + n.succ * bez_b (ZMod.val a) n.succ := by
        rw [ZMod.nat_cast_self, zero_mul, add_zero]
      _ = ↑(↑a.val * bez_a (ZMod.val a) n.succ + n.succ * bez_b (ZMod.val a) n.succ) := by
        push_cast
        rw [ZMod.nat_cast_zmod_val]
        have h : 0 < Nat.succ n := by apply Nat.zero_lt_succ
        rw [bez_is_zmod_inv]
        exact h
      _ = (Nat.gcd a.val n.succ : ℤ) := by
        rw [mul_comm, mul_comm (↑(Nat.succ n)) (bez_b (ZMod.val a) (Nat.succ n))]
        rw [← bezout a.val n.succ]
  done

--end of proofs based heavily on mathlib ------------------------------------------

--24/01/24 - Jakub

--I have edited some of Katie's lemmas to work with `my_zmod_inv` instead of mathlib's built-in inverse function.
--I have also unsorry'd `zmod_inv_eq_one` which followed as a corollary from the above theorem, and modified
--`zmod_unit_of_coprime` so that it now causes no errors, and works with our new inverse definition.

--Jakub
theorem zmod_mul_inv_eq_one {n : ℕ} (x : ZMod n) (h : Nat.Coprime x.val n) : x * (my_zmod_inv n x) = 1 := by
  rw [Nat.coprime_iff_gcd_eq_one] at h
  rw [← Nat.cast_one]
  rw [← h]
  rw [my_mul_zmod_inv_eq_gcd]
  done

lemma zmod_zero_eq_z : ZMod Nat.zero = ℤ := by rfl; done

--Jakub
lemma gcd_of_val_lt_non_zero (n : ℕ) (x : ZMod n) (h : 0 < x.val) (hn : 0 < n) : Nat.gcd x.val n < n := by
  have h1 : Nat.gcd x.val n ≤ x.val := by
    apply Nat.gcd_le_left
    exact h
  have : NeZero n := by
    rw [neZero_iff, ne_comm]
    apply ne_of_lt at hn
    exact hn
  have : Nat.gcd x.val n < n := by
      calc
        Nat.gcd x.val n ≤ x.val := by exact h1
        x.val < n := by
          exact ZMod.val_lt x
  exact this
  done

--Jakub
lemma my_cases_2_aaa (n : ℕ) (h : 0 < n): n=1 ∨ 1<n := by
  have : n ≤ 1 ∨ 1 < n := by
    rw [← Nat.not_le]
    apply or_not
  conv at this =>
    rw [Nat.le_one_iff_eq_zero_or_eq_one]
  have n_ne_zero : ¬n=0 := by
    rw [← Nat.ne_zero_iff_zero_lt] at h
    rw [← ne_eq]
    exact h
  cases this
  · have h' : n = 0 ∨ n = 1 := by assumption
    cases h'
    · have h'' : n = 0 := by assumption
      contradiction
    · have h'' : n = 1 := by assumption
      rw [h'']; simp
  · have h' : 1 < n := by assumption
    apply Or.intro_right
    exact h'
  done

--26/01/24 - Jakub

--I have spent a whole day on the following proof, in order to complete it I had to learn new tactics such as
--`simp_rw`, `apply_fun`, understanding `calc`, applying custom case separation and the `NeZero` and `Fact` instances!
--Overall I'm sure it's an extremely inefficient proof but a very informative one, perhaps the most instructive I
--have completed so far

--Jakub
lemma zmod_mul_inv_eq_one_iff_coprime_n {n : ℕ} (x : ZMod n) (h : 0 < n) : (Nat.Coprime x.val n) ↔  x * (my_zmod_inv n x) = 1 := by
  constructor
  · intro h1
    rw[← zmod_mul_inv_eq_one]
    exact h1
  · intro h2
    conv at h2 =>
      rw[my_mul_zmod_inv_eq_gcd]
      --want to use ZMod.val_nat_cast_of_lt
      --need `Nat.gcd x.val n < n`
      --this is true when `x.val ≠ 0`
      --this is true when `x ≠ 0` in ZMod n
      --I'll need to split cases:
    have n_ne_zero : NeZero n := by
        rw [neZero_iff, ne_comm]
        apply ne_of_lt at h
        exact h
    have my_cases : x = 0 ∨ ¬x=0 := by exact or_not
    cases my_cases
    · have h3 : x=0 := by assumption
      have : x.val = 0 := by
        rw [h3]
        rw [ZMod.val_zero]
      rw [this]
      conv at h2 =>
        rw [this]
        rw [Nat.gcd_zero_left]
        rw [ZMod.nat_cast_self]
      --have 1=0, should be able to contradict somewhere.
      have my_cases_2 : n = 1 ∨ 1 < n := by apply my_cases_2_aaa; exact h
      cases my_cases_2
      · have hn : n=1 := by assumption
        rw [hn]
        unfold Nat.Coprime
        rw [Nat.gcd_zero_left]
      · have hn : 1 < n := by assumption
        have : Fact (1 < n) := by rw [fact_iff]; exact hn
        apply_fun ((fun (x : ZMod n) => (x.val : ℕ)) : ZMod n → ℕ) at h2
        conv at h2 => rw [ZMod.val_zero]; rw [ZMod.val_one]
        contradiction
    · have h4 : ¬x=0 := by assumption
      have h5 : x.val ≠ 0 := by
        rw [← ne_eq] at h4
        rw [ZMod.val_ne_zero]
        exact h4
      have h6 : 0 < x.val := by
        apply Nat.zero_lt_of_ne_zero
        exact h5
      have H : Nat.gcd x.val n < n := by
        apply gcd_of_val_lt_non_zero
        <;> assumption
      have my_cases_2 : n = 1 ∨ 1 < n := by apply my_cases_2_aaa; exact h
      cases my_cases_2
      · have hn : n=1 := by assumption
        simp_rw [hn]
        apply Nat.coprime_one_right
      · have hn : 1<n := by assumption
        unfold Nat.Coprime
        apply_fun ((fun (x : ZMod n) => (x.val : ℕ)) : ZMod n → ℕ) at h2
        rw [ZMod.val_nat_cast_of_lt] at h2
        have : Fact (1 < n) := by rw [fact_iff]; exact hn
        rw [ZMod.val_one] at h2
        exact h2
        exact H
  done

-- Katie
instance (n : ℕ) : Inv (ZMod n) :=
  ⟨my_zmod_inv n⟩

#eval (15 : ZMod 10).inv

--01/02/24 - Jakub

--Attempted to prove `my_zmod_eq_zmod_inv`, my proof was affected when Katie defined our own instance of an inverse on
--`ZMod` using `my_zmod_inv`, so the proof was reduced to just a `rfl`. In the previous version of the proof I struggled
--to show that `bez_a` was the same as `Nat.gcdA`, which they are and have been defined similarly. Unfortunately the
--mathlib definition uses the function `Nat.xgcdAux` which is a more complex version of my own `gcd_bezout` function,
--using 6 variables instead of my 3 in the recursion for some sort of counting purpose. This proved too difficult for
--me to work around and prove what should have been a simple equality of definition. It is key to the completion of this
--project that Katie and I work together to understand what we do and do not need for the formalisation of
--`totient_eq_zmod_units_card`, which is currently reduced to `my_zmod_unitsEquivCoprime`. I believe we are close and
--are capable of completing our initial goal on schedule, provided the group theory side also finish `Lagrange`.

--Jakub
theorem my_zmod_inv_eq_zmod_inv {n : ℕ} (y : ZMod n) : my_zmod_inv n y = (y : ZMod n)⁻¹ := by
  rfl
/- Old proof from before we declared our own instance inverse
  unfold my_zmod_inv
  unfold Inv.inv
  unfold ZMod.instInvZMod
  unfold ZMod.inv
  conv =>
    lhs
    congr
    · rfl
    intro n i
    rw [←bez_a_is_gcdA] -- failed to prove this step, though it is true.
    rfl
-/
  done

--Katie
lemma zmod_inv_mul_eq_one_imp_unit {n : ℕ} (y : Units (ZMod n)) : y * y⁻¹ = 1 := by
  rw [mul_right_inv]
  done

--Katie
theorem coe_zmod_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (x : ZMod n) * (my_zmod_inv n x) = 1 := by
  rw [Nat.coprime_iff_gcd_eq_one] at h
  rw [← Nat.cast_one]
  rw [← h]
  rw [my_mul_zmod_inv_eq_gcd]
  rw [ZMod.val_nat_cast]
  rw [← Nat.gcd_rec, Nat.gcd_comm]
  done

--Katie
def my_unit_of_coprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (ZMod n)ˣ :=
  ⟨x, my_zmod_inv n x, coe_zmod_mul_inv_eq_one x h, by rw [mul_comm, coe_zmod_mul_inv_eq_one x h]⟩

--Katie
theorem coe_my_unit_of_coprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (my_unit_of_coprime x h : ZMod n) = x := by
  rfl; done

--Jakub
lemma nat_gcd_zero_eq_one {n : ℕ} (y : ZMod n) (h : n = 0) : (y = 1 ∨ y = -1) → (Nat.gcd (ZMod.val y) (Nat.zero) = 1) := by
  intro h1
  cases' h1 with h1
  · rw [h1, Nat.gcd_zero_right]
    aesop_subst [h1, h]
    exact ZMod.val_one'
  · rename_i h_1
    aesop_subst [h_1, h]
    rfl
  done

#check Units.isUnit

--27/01/24 - Jakub

--Proved `nat_gcd_zero_eq_one`. I was struggling associating `ZMod 0` to `ZMod n` even with the assumption that `n=0` but
--thankfully the `aesop` tactic had no trouble sorting that issue for me. It is the first time I have used this tactic
--and I wish I knew about it sooner! I also helped Katie proving the zero case of `zmod_unit_val_coprime` since the
--statement had been slightly modified from `(y : Units (ZMod n))` to `(y : ZMod n) (h : IsUnit y)` which unfortunately
--broke my previous proof of the statement, but that is now fixed. Applying the fact that `ZMod 0` is defined as the
--integers proves finnicky, as applying `Int.isUnit_iff` in the forwards direction at the assumption `h` did not work,
--which was what Katie tried, but applying it in the reverse direction at the goal, then `rfl`ing worked perfectly.
--I will be looking more into the `ZMod.Basic.lean` file in order to better understand this strange property. Hopefully
--a better understanding of mathlib will be beneficial in proving our main goal of ZMod

--adapting a mathlib theorem to work with our own Mod
lemma coprime_of_mul_Mod_eq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [mod n]) : a.Coprime n := by
  conv at h =>
    rw [Mod_eq]
    rw [← Nat.ModEq]
  apply Nat.coprime_of_mul_modEq_one b
  exact h

theorem zmod_unit_val_coprime {n : ℕ} (y : Units (ZMod n)) : Nat.Coprime (y : ZMod n).val n := by
--Jakub
  cases' n with n
  · unfold Nat.Coprime
    rw[← nat_gcd_zero_eq_one]
    · rfl
    rw [← Int.isUnit_iff]
    apply Units.isUnit
--Katie & Jakub - old proof had an error in that we didn't find until 03/02/24 - new one needed the above lemma to work.
  · apply coprime_of_mul_Mod_eq_one ((y⁻¹ : Units (ZMod n.succ)) : ZMod n.succ).val
    have : y * y⁻¹ = 1 := by apply zmod_inv_mul_eq_one_imp_unit
    rw [Units.ext_iff, Units.val_one] at this
    rw [← zmod_eq_iff_Mod_eq_nat]
    norm_cast
  done

--Katie
def zmod_unit_of_coprime {n : ℕ} (x : ZMod n) (h : Nat.Coprime x.val n) : (Units (ZMod n)) :=
  ⟨x, my_zmod_inv n x, zmod_mul_inv_eq_one x h, by rw [mul_comm, zmod_mul_inv_eq_one x h]⟩

--Jakub - Just going off Katie's above definition with a simple nat casting, LEAN a pain about types and needs this `have`
def nat_to_zmod_unit_of_coprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (Units (ZMod n)) :=
  have h1 : Nat.Coprime (x : ZMod n).val n := by
    rw [ZMod.val_nat_cast]
    unfold Nat.Coprime
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact h
  zmod_unit_of_coprime (x : ZMod n) h1

theorem coe_zmod_unit_of_coprime {n : ℕ} (x : ZMod n) (h : Nat.Coprime x.val n) : (zmod_unit_of_coprime x h : ZMod n) = x := by
  rfl; done

--02/02/2024 - Jakub & Katie

--Katie and I worked together to complete the following theorem. Katie was responsible for `toFun` and most of `invFun`,
--where I offered little more than reversing the order of `a` and `n` in the have statement after she was stuck on it.
--The proof for `left_inv` is simple and near-identical to mathlib's version of the same thing but `right_inv` is where
--we came into our own. The sequential `have` statments we me trying to get closer to applying `this` directly into the
--function using the `conv` tactic, each step making the next possible. The `simpa only` in the final `have` statement
--was suggested by `aesop`, after I had been struggling to apply my lemmas in the correct places, but all are used and
--required for this proof. This proof marks the end of what was essential for completing the number theory side of our
--initial goal of proving `Fermat's little theorem`, the rest of which was completed long ago using a sorry'd out form
--of this isomorphism laid out by Katie.

def my_zmod_unitsEquivCoprime {n : ℕ} [NeZero n] : (Units (ZMod n)) ≃ {x // x ∈ (Finset.range n).filter n.Coprime} where
--Katie
  toFun x := ⟨(ZMod.val (x : ZMod n)), by
    refine Finset.mem_filter.mpr ?_
    constructor
    · rw[Finset.mem_range]
      exact ZMod.val_lt (x : ZMod n)
    · rw [Nat.coprime_comm]
      apply zmod_unit_val_coprime⟩
--Katie & Jakub
  invFun x :=
    let ⟨a,b⟩ := x
    have : a.Coprime n := by
      simp_all only[Finset.mem_filter]
      let ⟨_,d⟩ := b
      rw [Nat.coprime_comm]
      exact d
    nat_to_zmod_unit_of_coprime a this
  left_inv := fun ⟨_, _, _, _⟩ => by
    apply Units.ext (ZMod.nat_cast_zmod_val _)
    done
--Jakub
  right_inv := fun ⟨a, b⟩ => by
    simp_all only [Finset.mem_filter]
    have h : a.Coprime n := by
      simp_all only[Finset.mem_filter]
      let ⟨_,d⟩ := b
      rw [Nat.coprime_comm]
      exact d
    have h1 : a < n := by
      simp_all only[Finset.mem_filter]
      let ⟨c,_⟩ := b
      rw [Finset.mem_range] at c
      exact c
    have h2 : (a : ZMod n).val = a := by
      exact ZMod.val_cast_of_lt h1
    have h3 : nat_to_zmod_unit_of_coprime a h = zmod_unit_of_coprime a _ := by
      unfold nat_to_zmod_unit_of_coprime
      rfl
    have : ZMod.val (nat_to_zmod_unit_of_coprime a h : ZMod n) = a := by
      rw [h3]
      unfold zmod_unit_of_coprime
      simpa only
    conv =>
      lhs
      congr
      rw [this]
    done

-- Getting the following lemmas to synthesize was a pain in of itself; type errors everywhere, in spite of my level of understanding. The main issue was
-- zmod_units_equiv_card, which did not allow me to apply/rw Fintype.card_congr no matter what I tried, or what extra lemmas I created. Eventually, I found that
-- using refine somehow made it successful. Now the main issue is finishing constructing the isomorphism above.

--Katie
lemma totient_subtype {n : ℕ} : Finset.card ((Finset.range n).filter n.Coprime) = Fintype.card { x // x ∈ (Finset.range n).filter n.Coprime} := by
  rw[Fintype.subtype_card]
  exact fun x ↦ Iff.rfl
  done

--Katie
theorem zmod_units_equiv_card (n : ℕ) [NeZero n] [inst : Fintype (Units (ZMod n))] [inst : Fintype ({x // x ∈ (Finset.range n).filter n.Coprime}) ] : Fintype.card (Units ((ZMod n))) = Fintype.card { x // x ∈ (Finset.range n).filter n.Coprime } := by
  refine Fintype.card_congr ?f
  exact my_zmod_unitsEquivCoprime
  done

--Katie
theorem totient_eq_zmod_units_card (n : ℕ) [NeZero n] [inst : Fintype (Units (ZMod n))]: my_totient (n) = Fintype.card (Units (ZMod n)) := by
  unfold my_totient
  rw[totient_subtype]
  rw[zmod_units_equiv_card]
  done

--25/01/24 - Jakub

--I have now completed the proof of Euler's Totient theorem, but it still relies on unproven theorems
--earlier in the document, both on the Number theory and Group theory sides. As of writing, all that remains is to
--prove `totient_eq_zmod_units_card` and `CosetsMul.PowOfCardEqOne`

--Katie
theorem euler_totient (a m : ℕ) (ha : m.Coprime a) : a^(my_totient (m)) ≡ 1 [mod m] := by
  rw [← zmod_eq_iff_Mod_eq_nat]
  rw [Nat.coprime_comm] at ha
  let a' : Units (ZMod m) := ZMod.unitOfCoprime a ha
--Jakub
  cases' m with m
  · rw [my_tot_zero]
    rw [pow_zero]
  · have h1 : a' ^ (my_totient (m.succ)) = 1 := by
      rw [totient_eq_zmod_units_card, CosetsMul.PowOfCardEqOne]
    have h2 : (a' ^ (my_totient (m.succ)) : ZMod m.succ) = 1 := by
      rw [h1]; norm_cast
    have zmod_a'_eq_a : (a' : ZMod m.succ) = a := by rfl
    norm_cast
    rw [← h2]
    rw [Nat.cast_pow]
    rw [← zmod_a'_eq_a]
    norm_cast
  done

--17/01/24 - Jakub

--Relying on the sorry'd out version of Euler's Totient theorem, I have completed a proof of Fermat's Little Theorem.
--By working from both ends of the project at once we aim to spread the workload so that we can work individually on
--separate proofs while working toward the same goal. As of writing it remains to prove `euler_totient`, for which we
--will be needing many results regarding `ZMod`.

--Jakub
theorem little_fermat_1 (a p : ℕ) (h : Nat.Prime p) (h1 : ¬ p ∣ a) : a ^ (p-1) ≡ 1 [mod p] := by
  rw [← my_tot_prime]
  have ha : p.Coprime a := by
    rw [Nat.Prime.coprime_iff_not_dvd]
    exact h1
    exact h
  apply euler_totient
  exact ha
  exact h
  done

--Jakub
theorem little_fermat_2 (a p : ℕ) (h : Nat.Prime p) (h1 : p ∣ a ∨ ¬(p ∣ a)): a^p ≡ a [mod p] := by
  have : p = 1 + (p-1) := by
    rw [← Nat.add_sub_assoc]
    rw [Nat.add_sub_cancel_left]
    have : 1 < p := by
      apply Nat.Prime.one_lt
      exact h
    apply Nat.le_of_lt this
  rw [this]
  nth_rewrite 1 [← this]
  rw [Nat.pow_add]
  rw [Nat.pow_one]
  rw [Mod_eq]
  --want to split cases with `p | a`, then rw in `little_fermat_1` to finish this proof
  cases h1 with
  | inl hp =>
    have hhp : p ∣ a * a ^ (p-1) := by
      have : a ∣ a * a ^ (p-1) := by
        simp only [dvd_mul_right]
      apply Nat.dvd_trans hp this
    rw [Nat.mod_eq_zero_of_dvd, Nat.mod_eq_zero_of_dvd]
    exact hp
    exact hhp
  | inr hp =>
    have hh : a ^ (p-1) % p = 1 % p := by
      rw [← Mod_eq]
      apply little_fermat_1
      exact h
      exact hp
    rw [Nat.mul_mod, hh, ← Nat.mul_mod, mul_one]
  done

--Katie
-- I planned for this to be a fun little extra project to have a crack at after FLT was completed, since it involved a great deal of
-- overlap with theorems we have already proven. The order lemmas weren't necessary in the end.

theorem order_lemma_1 {m k : ℕ} (a : Units (ZMod m)) : (a^k = (1 : Units (ZMod m))) ↔ ((orderOf (a : Units (ZMod m))) ∣ k) := by
  constructor
  · intro h1
    apply orderOf_dvd_of_pow_eq_one
    exact h1
  · intro h2
    rw[dvd_def] at h2
    cases h2 with
    | intro c h3 =>
      rw[h3]
      rw[pow_mul]
      rw[pow_orderOf_eq_one]
      rw[one_pow]
  done

theorem order_lemma_2 {n : ℕ} (a : Units (ZMod n)) : ((orderOf (a : Units (ZMod n))) ∣ my_totient (n)) := by
  rw[← order_lemma_1]
  rw[Units.ext_iff]
  apply ZMod.eq_iff_modEq_nat
  sorry

def prim_roots_mod_n {n : ℕ} := {a // (orderOf (a : Units (ZMod n))) = my_totient (n)}

-- Initially, I set out to utilise primitive roots to approach Wilson's theorem, but I think combining many previous lemmas
-- is preferable.

-- Whilst I do know the proof for showing (Units(ZModp)) is cyclic, and we have a lot of the tools for it (i.e. we have sum of divisors
-- and totient function but not FTA), it would take up too much time for something that is not the main focus here. If we did have more
-- time, this would have been a fun and satisfying side-goal, since it involves a lot of manipulation that would feel quite unnatural
-- to LEAN. I have imported all of RingTheory.IntegralDomain for the one instance used below:

theorem zmodp_units_cyclic {p : Nat.Primes} [CommRing (ZMod p)] [IsDomain (ZMod p)] [Finite (Units (ZMod p))]: IsCyclic (Units (ZMod p)) := by
 exact instIsCyclicUnitsToMonoidToMonoidWithZeroToSemiringToCommSemiringInstGroupUnits

-- Now, utilising a method of writing each member of (Units(ZMod p)) as a power of the generator of the cyclic group, we can prove Wilson's Theorem.

lemma prod_finset_range_eq : ∏ x in Finset.range (p - 1), (x + 1) = ∏ x in (Finset.range p) \ {0}, x := by
  sorry

@[simp] lemma finset_range_eq_fintype : ∏ x in (Finset.range p \ {0}), x = ∏ x in {x // x ∈ Finset.range p \ {0}}, x := by
  rfl

@[simp] lemma zmodp_units_elts {p : Nat.Primes} : Units (ZMod p) = Finset.Ico 1 (p : ℕ) := by
  sorry

theorem zmodp_unitsEquivCoprime [NeZero p] : (Units (ZMod p)) ≃ {x // x ∈ (Finset.range p).filter p.Coprime}:= by
  apply my_zmod_unitsEquivCoprime

--theorem prime_coprime (p : ℕ) (h_p : Nat.Prime p) : ((Finset.range p).filter p.Coprime) = (Finset.range p) \ {0}

-- Yet again, the bane of my existence - type classes - crops up. Hoping this work around could secure the win (i.e. instead of claiming the finset range is the same
-- as Units(ZMod p), and therefore claim the set is cyclic with applications to rewriting each component of (p-1)! as a generated element, we can use the isomorphism
-- constructed previously to claim the set is cyclic by its isomorphism with (Units(ZMod p)).

theorem isom_cyclic_finset_range_p {p : Nat.Primes} [inst: Group ({x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})] [inst : Fintype ({x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime}) ] : IsCyclic ({x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime}) := by
  apply isCyclic_of_surjective
  sorry

-- I'm not sure how presumptuous it is to [inst:...] and call {x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime} a group without even noting an operation, but I feel
-- there are more important/interesting things to focus on with this proof. If I could go back in time, I might have been more insistent on trying to come up with a better way
-- to equate ZMod units with a simple Finset range set that has its own group operation (if that were even possible), and include Wilson's theorem more prominently in the end goal.
-- But alas, we will have to brush over it for now.

lemma finset_range_generated {p : Nat.Primes} [inst: Group ({y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})] (h : IsCyclic ({x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})): ∃ (g : ({y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})), ∀ (x : {y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime}), x ∈ Subgroup.zpowers g := by
  refine IsCyclic.exists_generator

lemma finset_equate_fintype {p : Nat.Primes} [inst : Fintype ({x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})] : Finset.univ ({y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime}) = Finset.filter (Nat.Coprime p) (Finset.range p) := by
  sorry

lemma idk_bro_generators_or_something {p : Nat.Primes} [inst: Group ({y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})] (h : IsCyclic ({x // x ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})) (g : ({y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime})) (hg : ∀ (x : {y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime}), x ∈ Subgroup.zpowers g) : Subgroup.zpowers g = {y // y ∈ (Finset.range (p : ℕ)).filter (p : ℕ).Coprime} := by
  sorry

--lemma aaaaaa {p : Nat.Primes} : (x ∈ Finset.filter (Nat.Coprime p) (Finset.range p)) ↔ ∃ (g : x = g^k
  --sorry

-- After a very long day of LEANing, I am finding it difficult to think of a way to formalise that each component of (p-1)! can be written as a power of the chosen generator element,
-- but at the same time they are all (unordered) distinct/successive powers; i.e. (p-1)! = 1*g*g^(2)*g^(3)*...*g^(p-2) = g^(sum of integers from 1 to (p-2)).

theorem wilson (hp : Nat.Prime p) (h : Odd p) : ((p-1) : ℕ).factorial = (-1 : ZMod n) := by
  rw[← Finset.prod_range_add_one_eq_factorial]
  rw[prod_finset_range_eq]
  rw[← prime_coprime]



  rw[← Finset.prod_Ico_id_eq_factorial]
  rw[← zmodp_units_elts]

--04/02/24 - Jakub

--Proved `sum_nat` for Katie to use to prove Wilson's theorem, too close to the deadline now to make this proof more concise,
--so this will have to do. We are not sure if there will be time to get the the point even of applying this theorem. It would
--be nice if it got used but it was fun to prove anyway, interesting to learn about even and odd numbers and trying to get
--around the painful object that is division in the naturals.

--Jakub
theorem sum_nat {n : ℕ} : ∑ k in Finset.range (n+1), k = n * (n+1) / 2 := by
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    rw [Nat.zero_div]
    rfl
  | succ n ih =>
    rw [← Nat.succ_eq_add_one]
    rw [Finset.sum_range_succ]
    rw [ih]
    have : Even n ∨ Odd n := by apply Nat.even_or_odd
    have h : Even (n*(n+1)) := by
      cases this with
      | inl hn =>
        have : Even (n*(n+1)) := by
          rw [Nat.even_mul]
          exact Or.inl hn
        exact this
      | inr hn =>
        rw [Nat.odd_iff_not_even] at hn
        have hn' : Even (n+1) := by
          rw [Nat.even_add_one]
          exact hn
        have : Even (n*(n+1)) := by
          rw [Nat.even_mul]
          exact Or.inr hn'
        exact this
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
    cases this with
    | inl hn =>
      have h' : n*(n+1)/2 = n/2 * (n+1) := by
        have : 2*(n/2) = n := by
          apply Nat.two_mul_div_two_of_even; exact hn
        nth_rewrite 1 [← this]
        rw [mul_assoc]
        rw [Nat.mul_div_right]
        apply Nat.zero_lt_two
      have h'' : (n+1)*(n+1+1)/2 = (n+1)*((n+1+1)/2) := by
        have : Even (n+1+1) := by
          rw [Nat.even_add_one, Nat.even_add_one, not_not]
          exact hn
        have : 2*((n+1+1)/2) = (n+1+1) := by
          apply Nat.two_mul_div_two_of_even; exact this
        rw [mul_comm]
        nth_rewrite 1 [← this]
        rw [mul_assoc]
        rw [Nat.mul_div_right]
        rw [mul_comm]
        apply Nat.zero_lt_two
      rw [h']
      rw [h'']
      rw [← Nat.succ_mul]
      rw [Nat.succ_eq_add_one]
      have : (n/2 + 1) = ((n+1+1)/2) := by
        have : n+ 1+1 = n+ 2 := by rfl
        rw [this]
        rw [Nat.add_div_right]
        apply Nat.zero_lt_two
      rw [this]
      rw [mul_comm]
    | inr hn =>
      rw [Nat.odd_iff_not_even] at hn
      have hn' : Even (n+1) := by
          rw [Nat.even_add_one]
          exact hn
      have h' : n*(n+1)/2 = n * ((n+1)/2) := by
        have : 2*((n+1)/2) = (n+1) := by
          apply Nat.two_mul_div_two_of_even; exact hn'
        rw [mul_comm]
        nth_rewrite 1 [← this]
        rw [mul_assoc]
        rw [Nat.mul_div_right]
        rw [mul_comm]
        apply Nat.zero_lt_two
      have h'' : 2*((n+1)/2) = (n+1) := by
          apply Nat.two_mul_div_two_of_even; exact hn'
      have h''' : (n+1)*(n+1+1)/2 = ((n+1)/2)*(n+1+1) := by
        nth_rewrite 1 [← h'']
        rw [mul_assoc]
        rw [Nat.mul_div_right]
        apply Nat.zero_lt_two
      rw [h']
      rw [h''']
      rw [← add_assoc]
      rw [mul_comm]
      have : n+ 1+1 = (n+1).succ := by rfl
      rw [this]
      rw [Nat.mul_succ]
      have : n+1 = n.succ := by rfl
      nth_rewrite 3 [this]
      rw [Nat.mul_succ]
      conv =>
        rhs
        rw [add_assoc]
      rw [← Nat.two_mul]
      rw [h'']
      rw [add_assoc]
  done
