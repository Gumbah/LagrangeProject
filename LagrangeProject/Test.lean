import Mathlib

class MyGroupMul (G : Type) extends Mul G, One G, Inv G where
(assoc_mul : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(left_inv_mul : ∀ (a : G), a⁻¹ * a = 1)



namespace my_group

variable {G : Type} [MyGroupMul G]

lemma mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
sorry
done

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b := by
rw [← left_inv_mul] at h
done
