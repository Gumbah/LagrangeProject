import Mathlib

class MyGroupMul (G : Type) :=
(assoc_mul : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(left_inv_mul : ∀ (a : G), a⁻¹ * a = 1)



namespace group
variables {G : Type} [group G]
[@simp]lemma mul_left_cancel (a b c : G) (h : a * b = a * c) : x = y :=
sorry
done

[@simp]lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
sorry
done
