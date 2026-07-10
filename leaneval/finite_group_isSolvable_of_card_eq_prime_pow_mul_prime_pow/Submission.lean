import Mathlib
import Submission.Burnside

namespace Submission

theorem finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  have _ := hpq
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  exact burnside_solvable (by rw [Nat.card_eq_fintype_card, hcard])

end Submission
