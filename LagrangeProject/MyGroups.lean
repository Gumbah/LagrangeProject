import Mathlib

class MyGroupMul (G : Type) extends Mul G, One G, Inv G where
(assoc_mul : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(left_inv_mul : ∀ (a : G), a⁻¹ * a = 1)



namespace my_group

variable {G : Type} [MyGroupMul G]

theorem mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
sorry
done

theorem right_inv_mul (a b : G) : a * a⁻¹ = 1 := by
sorry
done

theorem inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : b = a⁻¹ := by
--rw [← right_inv_mul a] at h
sorry
done

end my_group
