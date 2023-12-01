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
  lemma LeftCosetEqOrDisjoint (g i j : G) (H : Subgroup G)
  (h : g ∈ (i LCoset* H) ∧ g ∈ (j LCoset* H)) :
  i LCoset* H = j LCoset* H := by
    sorry
    done

  lemma RightCosetEqOrDisjoint (g i j : G) (H : Subgroup G)
  (h : g ∈ (RightCosetMul H i) ∧ g ∈ (RightCosetMul H j)) :
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

end cosetsMul
