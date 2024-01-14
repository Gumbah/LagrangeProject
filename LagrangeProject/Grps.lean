import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
--import Mathlib.Data.Finite.Card

import Mathlib.Tactic

--In this file we will use the basic definitions of Groups to
--prove basic things about them only using the axioms of acossiativity,
--inverses and the identity

--Specifically we are using
--one_mul
--mul_left_inv
--mul_assoc
--which are used to define the Group.ofLeftAxioms in Mathlib

section group

namespace groupsMul

  variable {G : Type} [Group G]

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
    intro h1
    rw[h1]
    rw[← mul_assoc]
    rw[MulInv]
    rw[one_mul]
    intro h2
    rw[← h2]
    rw[← mul_assoc]
    rw[mul_left_inv]
    rw[one_mul]
    done

  @[simp]lemma RightInvEqMul (a b c : G) : a = b * c⁻¹ ↔ a * c = b := by
    constructor
    intro h1
    rw[h1]
    rw[mul_assoc]
    rw[mul_left_inv]
    rw[MulOne]
    intro h2
    rw[← h2]
    rw[mul_assoc]
    rw[MulInv]
    rw[MulOne]
    done

  @[simp]lemma IdUniqueMul (a b : G) : a * b = b ↔ a = 1 := by
    constructor
    intro h1
    rw[← MulOne a]
    rw[← MulInv b]
    rw[← mul_assoc]
    rw[h1]
    intro h2
    rw[h2]
    rw[one_mul]
    done

  @[simp]lemma InvUniqueRightMul (a b : G) (h : a * b = 1) : a = b⁻¹ := by
    rw[← MulOne a]
    rw[← MulInv b]
    rw[← mul_assoc]
    rw[h]
    rw[one_mul]
    done

  @[simp]lemma InvUniqueLeftMul (a b : G) (h : a * b = 1) : b = a⁻¹ := by
    rw[← one_mul b]
    rw[← mul_left_inv a]
    rw[mul_assoc]
    rw[h]
    rw[MulOne]
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
    intro h1
    rw[h1]
    rw[← add_assoc]
    rw[AddNeg]
    rw[zero_add]
    intro h2
    rw[← h2]
    rw[← add_assoc]
    rw[add_left_neg]
    rw[zero_add]
    done

  @[simp]lemma RightNegEqAdd (a b c : G) : a = b + -c ↔ a + c = b := by
    constructor
    intro h1
    rw[h1]
    rw[add_assoc]
    rw[add_left_neg]
    rw[AddZero]
    intro h2
    rw[← h2]
    rw[add_assoc]
    rw[AddNeg]
    rw[AddZero]
    done

  @[simp]lemma IdUniqueAdd (a b : G) : a + b = b ↔ a = 0 := by
    constructor
    intro h1
    rw[← AddZero a]
    rw[← AddNeg b]
    rw[← add_assoc]
    rw[h1]
    intro h2
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
    intro h1
    rw[h1]
    rw[← add_assoc]
    rw[AddNeg]
    rw[zero_add]
    intro h2
    rw[← h2]
    rw[← add_assoc]
    rw[add_left_neg]
    rw[zero_add]
    done

  @[simp]lemma RightNegEqAdd (a b c : R) : a = b + -c ↔ a + c = b := by
    constructor
    intro h1
    rw[h1]
    rw[add_assoc]
    rw[add_left_neg]
    rw[AddZero]
    intro h2
    rw[← h2]
    rw[add_assoc]
    rw[AddNeg]
    rw[AddZero]
    done

  @[simp]lemma IdUniqueAdd (a b : R) : a + b = b ↔ a = 0 := by
    constructor
    intro h1
    rw[← AddZero a]
    rw[← AddNeg b]
    rw[← add_assoc]
    rw[h1]
    intro h2
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

  def DirectRingProd [Ring R, S] (g : G) (H : Set G) : Set G :=
    Set.image (fun h => g * h) H

  @[simp]lemma IdUniqueMul (a b : R) : a * b = b ↔ a = 1 := by
    constructor
    intro h1
    rw[← mul_one a]
    rw[← MulInv b]
    rw[← mul_assoc]
    rw[h1]
    intro h2
    rw[h2]
    rw[one_mul]
    sorry
    -- this one might not be super necessary
    done

end rings

section cosetsMul

--variable {G : Type} [Group G] (H : Subgroup G)

  def LeftCosetMul [Group G] (g : G) (H : Set G) : Set G :=
    Set.image (fun h => g * h) H

  def RightCosetMul [Group G] (H : Set G) (g : G) : Set G :=
    Set.image (fun h => h * g) H

  notation:70 i:70 "LCoset*" H:70 => LeftCosetMul i H
  notation:70 H:70 "RCoset*" i:70 => RightCosetMul H i

  /-
  def LeftCosetEqMul [Group G] (g h : Set G) (i j : G):=
    i LCoset* g = j LCoset* h

  def RightCosetEqMul [Group G] (i j : G) (g h : Set G) :=
    g RCoset* i = h RCoset* j

  -/

  --notation:50 i:50 "LCoset*" H:50 "LCoset=" j:50 "LCoset*" K:50 => LeftCosetEqMul H K i j
  --notation:50 H:50 "RCoset*" i:50 "RCoset=" K:50 "RCoset*" j:50 => RightCosetEqMul i j H K

  namespace CosetsMul

  variable (G : Type) [Group G] (H : Subgroup G)

  lemma AssocLeftCosetMul (a b : G) (H : Subgroup G) :
  a LCoset* b LCoset* H = (a*b) LCoset* H := by
    sorry
    done

  lemma AssocRightCosetMul (a b : G) (H : Subgroup G) :
  (H RCoset* a) RCoset* b = H RCoset* (a*b) := by
    sorry
    done

  lemma LeftCosetElemImpEqMul (a b : G) (H : Subgroup G) :
  a = b ↔ a LCoset* H = b LCoset* H := by
    sorry
    done

  lemma RightCosetElemImpEqMul (a b : G) (H : Subgroup G) :
  a = b ↔ H RCoset* a = H RCoset* b := by
    sorry
    done

    --May be more lemmas needed

  -- if h ∈ iH and jH then iH = jH
  lemma LeftCosetEqOrDisjointMul (g i j : G) (H : Subgroup G)
  (h : g ∈ (i LCoset* H) ∧ g ∈ (j LCoset* H)) :
  i LCoset* H = j LCoset* H := by
    sorry
    done

  lemma RightCosetEqOrDisjointMul (g i j : G) (H : Subgroup G)
  (h : g ∈ (H RCoset* i) ∧ g ∈ (H RCoset* j)) :
  H RCoset* i = H RCoset* j := by
    sorry
    done

  /-!
  lemma UnionOfLeftCosetsIsGroup (H : Subgroup G) : ∀ (g : G),
  G = LeftCosetMul g H := by
  sorry
  done
  -/

  def indexMul : ℕ :=
    sorry
    -- number of cosets iH, jH ... that makes up G

  --Langrange's Theorem

end CosetsMul

end cosetsMul

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
  namespace CosetsMul

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


section cosetsAdd

end cosetsAdd
