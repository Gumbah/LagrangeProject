import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.Subgroup.Basic
--import Mathlib.Data.Finite.Card

import Mathlib.Tactic

--In this file we will use the basic definitions of Groups to
--prove basic things about them only using the axioms of acossiativity,
--inverses and the identity

section group

namespace groupsMul

  variable {G : Type} [Group G]

  @[simp]lemma LeftCancelMul : ∀ (a b c : G), a * b = a * c → b = c := by
    sorry
    done

  @[simp]lemma LeftInvEqMul (a b c : G) : a = b⁻¹ * c ↔ b * a = c := by
    sorry
    done

  @[simp]lemma MulOne (a : G) : a * 1 = a := by
    sorry
    done

  @[simp]lemma MulInv (a : G) : a * a⁻¹ = 1 := by
    sorry
    done

  @[simp]lemma RightInvEqMul (a b c : G) : a = b * c⁻¹ ↔ a * c = b := by
    sorry
    done

  @[simp]lemma IdUniqueMul (a b : G) : a * b = b ↔ a = 1 := by
    sorry
    done

  @[simp]lemma InvUniqueRightMul (a b : G) (h : a * b = 1) : a = b⁻¹ := by
    sorry
    done

  @[simp]lemma InvUniqueLeftMul (a b : G) (h : a * b = 1) : b = a⁻¹ := by
    sorry
    done

  @[simp]lemma InvInvMul (a : G) : (a⁻¹)⁻¹ = a := by
    sorry
    done

end groupsMul

namespace addGroups

  variable {G : Type} [AddGroup G]

  @[simp]lemma LeftCancelAdd : ∀ (a b c : G), a + b = a + c → b = c := by
    sorry
    done

  @[simp]lemma LeftInvEqAdd (a b c : G) : a = -b + c ↔ b + a = c := by
    sorry
    done

  @[simp]lemma AddZero (a : G) : a + 0 = a := by
    sorry
    done

  @[simp]lemma AddInv (a : G) : a - a = 0 := by
    sorry
    done

  @[simp]lemma RightInvEqAdd (a b c : G) : a = b - c ↔ a + c = b := by
    sorry
    done

  @[simp]lemma IdUniqueAdd (a b : G) : a + b = b ↔ a = 0 := by
    sorry
    done

  @[simp]lemma InvUniqueRightAdd (a b : G) (h : a + b = 0) : a = -b := by
    sorry
    done

  @[simp]lemma InvUniqueLeftAdd (a b : G) (h : a + b = 0) : b = -a := by
    sorry
    done

  @[simp]lemma InvInvAdd (a : G) : -(-a) = a := by
    sorry
    done

end addGroups

end group


section cosetsMul

--variable {G : Type} [Group G] (H : Subgroup G)

  def LeftCosetMul [Group G] (g : G) (H : Set G) : Set G :=
    (fun h => g * h) '' H

  def RightCosetMul [Group G] (H : Set G) (g : G) : Set G :=
    (fun h => h * g) '' H

  def LeftCosetEqMul [Group G] (g h : Set G) (i j : G):=
    LeftCosetMul i g = LeftCosetMul j h

  def RightCosetEqMul [Group G] (i j : G) (g h : Set G) :=
    RightCosetMul g i = RightCosetMul h j

  variable (G : Type) [Group G] (H : Set G)

  lemma AssocLeftCosetMul (a b : G) (H : Set G) :
  LeftCosetEqMul H (LeftCosetMul b H) (a*b) a := by
    sorry
    done

  lemma AssocRightCosetMul (a b : G) (H : Set G) :
  RightCosetEqMul (a*b) a H (RightCosetMul H b) := by
    sorry
    done

  lemma LeftCosetElemImpEqMul (a b : G) (H : Set G) :
  a = b ↔ LeftCosetEqMul H H a b := by
    sorry
    done

  lemma RightCosetElemImpEqMul (a b : G) (H : Set G) :
  a = b ↔ RightCosetEqMul a b H H := by
    sorry
    done

    --May be more lemmas needed

  -- if h ∈ iH and jH then iH = jH
  lemma LeftCosetEqOrDisjoint (g i j : G) (H : Set G)
  (h : g ∈ (LeftCosetMul i H) ∧ g ∈ (LeftCosetMul j H)) :
  LeftCosetEqMul H H i j := by
    sorry
    done

  lemma RightCosetEqOrDisjoint (g i j : G) (H : Set G)
  (h : g ∈ (RightCosetMul H i) ∧ g ∈ (RightCosetMul H j)) :
  RightCosetEqMul i j H H := by
    sorry
    done


  -- ...

  def indexMul : ℕ :=
    sorry
    -- number of cosets iH, jH ... that makes up G

  --Langrange's Theorem

end cosetsMul
