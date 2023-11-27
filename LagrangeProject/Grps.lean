import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Finite.Card

import Mathlib.Tactic

--In this file we will use the basic definitions of Groups to
--prove basic things about them only using the axioms of acossiativity,
--inverses and the identity

section group

namespace groups

  variable {G : Type} [Group G]

  @[simp]lemma left_cancel_mul : ∀ (a b c : G), a * b = a * c → b = c := by
    sorry
    done

  @[simp]lemma left_inv_eq_mul (a b c : G) : a = b⁻¹ * c ↔ b * a = c := by
    sorry
    done

  @[simp]lemma mul_one (a : G) : a * 1 = a := by
    sorry
    done

  @[simp]lemma mul_inv (a : G) : a * a⁻¹ = 1 := by
    sorry
    done

  @[simp]lemma right_inv_eq_mul (a b c : G) : a = b * c⁻¹ ↔ a * c = b := by
    sorry
    done

  @[simp]lemma id_unique_mul (a b : G) : a * b = b ↔ a = 1 := by
    sorry
    done

  @[simp]lemma inv_unique_right_mul (a b : G) (h : a * b = 1) : a = b⁻¹ := by
    sorry
    done

  @[simp]lemma inv_unique_left_mul (a b : G) (h : a * b = 1) : b = a⁻¹ := by
    sorry
    done

  @[simp]lemma inv_inv_mul (a : G) : (a⁻¹)⁻¹ = a := by
    sorry
    done

end groups

namespace addGroups

  variable {G : Type} [AddGroup G]

  @[simp]lemma left_cancel_add : ∀ (a b c : G), a + b = a + c → b = c := by
    sorry
    done


end addGroups

end group


section cosets

--variable {G : Type} [Group G] (H : Subgroup G)

  def LeftCosetMul [Group G] (g : G) (H : Subgroup G) : Set G :=
    (fun h => g * h) '' H

  def RightCosetMul [Group G] (H : Subgroup G) (g : G) : Set G :=
    (fun h => h * g) '' H

  def LeftCosetEqMul [Group G] (g : Subgroup G) (i j : G):=
    LeftCosetMul i g = LeftCosetMul j g

  def RightCosetEqMul [Group G] (i j : G) (g : Subgroup G) :=
    RightCosetMul g i = RightCosetMul g j

  -- lemma acossiativity
  -- lemma if (i = j) then iH = jH
  -- lemma if h ∈ iH and jH then iH = jH
  -- ...

  def indexMul : ℕ :=
    sorry
    -- number of cosets iH, jH ... that makes up G

  --Langrange's Theorem

end cosets
