module

public import Steiner.Numerics

@[expose] public section

namespace Steiner

/-- A zero Euler gap can occur in only the one integral critical degree. -/
theorem degree_eq_criticalFloor_of_gap_zero {n t r s : ℕ} (hr : 0 < r)
    (h : (n : ℤ) * t - (r : ℤ) * s = 0) :
    s = criticalFloor n t r := by
  have hm : r * s = n * t := by
    exact_mod_cast (sub_eq_zero.mp h).symm
  change s = n * t / r
  rw [← hm]
  simpa only [Nat.mul_comm] using (Nat.mul_div_cancel_left s hr).symm

end Steiner
