import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.Subgroup.Basic
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


section subgroups

namespace Subgroups

variable {G : Type} [Group G] (H : Subgroup G)

  noncomputable def index : ℕ :=
    G.card

end Subgroups

end subgroups

section cosets

def LeftCoset [Group G] (g : G) (H : Subgroup G) : Set G :=
  (fun h => g * h) '' H

def RightCoset [Group G] (H : Subgroup G) (g : G) : Set G :=
  (fun h => h * g) '' H

def


end cosets
