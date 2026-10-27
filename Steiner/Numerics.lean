module

public import Steiner.Homogeneous

@[expose] public section

/-!
# Dimensions and critical degrees for a Steiner presentation

All statements in this file are elementary arithmetic. The source dimension at
zero is explicitly zero, as required by the convention `S₋₁ = 0`.
-/

namespace Steiner

/-- Dimension of the degree-`s` target of a Steiner presentation. -/
def steinerTargetDimension (n t s : ℕ) : ℕ := t * (n + s).choose n

/-- Dimension of the degree-`s` source, with the negative graded piece zero. -/
def steinerSourceDimension (n t r s : ℕ) : ℕ :=
  if s = 0 then 0 else (t + r) * (n + s - 1).choose n

/-- Last degree on the injective side of the dimension crossing. -/
def criticalFloor (n t r : ℕ) : ℕ := n * t / r

/-- First degree on the surjective side of the dimension crossing. -/
def criticalCeil (n t r : ℕ) : ℕ := (n * t + r - 1) / r

@[simp] theorem steinerSourceDimension_zero (n t r : ℕ) :
    steinerSourceDimension n t r 0 = 0 := by simp [steinerSourceDimension]

@[simp] theorem steinerTargetDimension_zero (n t : ℕ) :
    steinerTargetDimension n t 0 = t := by simp [steinerTargetDimension]

/-- The adjacent binomial coefficients obey the dimension ratio in positive degree. -/
theorem choose_degree_ratio {n s : ℕ} (hs : 1 ≤ s) :
    (n + s).choose n * s = (n + s - 1).choose n * (n + s) := by
  have h := Nat.choose_mul_succ_eq (n + s - 1) n
  have ha : n + s - 1 + 1 = n + s := by omega
  have hb : n + s - n = s := by omega
  rw [ha, hb] at h
  exact h.symm

/-- The source dimension after multiplying by its positive degree. -/
theorem steinerSource_mul_degree {n t r s : ℕ} (hs : 1 ≤ s) :
    steinerSourceDimension n t r s * s =
      (n + s - 1).choose n * (t * s + r * s) := by
  simp only [steinerSourceDimension, show s ≠ 0 by omega, ↓reduceIte]
  ring

/-- The target dimension after multiplying by its positive degree. -/
theorem steinerTarget_mul_degree {n t s : ℕ} (hs : 1 ≤ s) :
    steinerTargetDimension n t s * s =
      (n + s - 1).choose n * (t * s + n * t) := by
  dsimp [steinerTargetDimension]
  calc
    _ = t * ((n + s).choose n * s) := by ring
    _ = t * ((n + s - 1).choose n * (n + s)) := by rw [choose_degree_ratio hs]
    _ = _ := by ring

/-- Dimension comparison for the positive-degree multiplication map. -/
theorem steinerSource_le_target_iff_of_pos {n t r s : ℕ} (hs : 1 ≤ s) :
    steinerSourceDimension n t r s ≤ steinerTargetDimension n t s ↔ r * s ≤ n * t := by
  have hB : 0 < (n + s - 1).choose n := Nat.choose_pos (by omega)
  calc
    _ ↔ steinerSourceDimension n t r s * s ≤ steinerTargetDimension n t s * s :=
      (Nat.mul_le_mul_right_iff (by omega : 0 < s)).symm
    _ ↔ (n + s - 1).choose n * (t * s + r * s) ≤
        (n + s - 1).choose n * (t * s + n * t) := by
      rw [steinerSource_mul_degree hs, steinerTarget_mul_degree hs]
    _ ↔ t * s + r * s ≤ t * s + n * t := Nat.mul_le_mul_left_iff hB
    _ ↔ r * s ≤ n * t := by omega

/-- The reverse comparison for the positive-degree multiplication map. -/
theorem steinerTarget_le_source_iff_of_pos {n t r s : ℕ} (hs : 1 ≤ s) :
    steinerTargetDimension n t s ≤ steinerSourceDimension n t r s ↔ n * t ≤ r * s := by
  have hB : 0 < (n + s - 1).choose n := Nat.choose_pos (by omega)
  calc
    _ ↔ steinerTargetDimension n t s * s ≤ steinerSourceDimension n t r s * s :=
      (Nat.mul_le_mul_right_iff (by omega : 0 < s)).symm
    _ ↔ (n + s - 1).choose n * (t * s + n * t) ≤
        (n + s - 1).choose n * (t * s + r * s) := by
      rw [steinerSource_mul_degree hs, steinerTarget_mul_degree hs]
    _ ↔ t * s + n * t ≤ t * s + r * s := Nat.mul_le_mul_left_iff hB
    _ ↔ n * t ≤ r * s := by omega

/-- The dimension comparison also holds at degree zero. -/
theorem steinerSource_le_target_iff (n t r s : ℕ) :
    steinerSourceDimension n t r s ≤ steinerTargetDimension n t s ↔ r * s ≤ n * t := by
  by_cases hs : s = 0
  · subst s; simp
  · exact steinerSource_le_target_iff_of_pos (by omega)

/-- The reverse dimension comparison includes degree zero when `n` is positive. -/
theorem steinerTarget_le_source_iff {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    steinerTargetDimension n t s ≤ steinerSourceDimension n t r s ↔ n * t ≤ r * s := by
  by_cases hs : s = 0
  · subst s
    simp only [steinerTargetDimension_zero, steinerSourceDimension_zero, Nat.mul_zero]
    constructor
    · intro h
      have ht : t = 0 := by omega
      simp [ht]
    · intro h
      have ht : t = 0 := by nlinarith
      omega
  · exact steinerTarget_le_source_iff_of_pos (by omega)

/-- The multiplication map is square exactly at the rational crossing. -/
theorem steinerDimensions_eq_iff {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    steinerSourceDimension n t r s = steinerTargetDimension n t s ↔ r * s = n * t := by
  rw [le_antisymm_iff, steinerSource_le_target_iff, steinerTarget_le_source_iff hn]
  omega

/-- The source is strictly smaller exactly on the injective side. -/
theorem steinerSource_lt_target_iff {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    steinerSourceDimension n t r s < steinerTargetDimension n t s ↔ r * s < n * t := by
  rw [← not_le, steinerTarget_le_source_iff hn]
  omega

/-- The target is strictly smaller exactly on the surjective side. -/
theorem steinerTarget_lt_source_iff (n t r s : ℕ) :
    steinerTargetDimension n t s < steinerSourceDimension n t r s ↔ n * t < r * s := by
  rw [← not_le, steinerSource_le_target_iff]
  omega

/-- Degrees up to the floor are exactly on the injective side. -/
theorem le_criticalFloor_iff {n t r s : ℕ} (hr : 1 ≤ r) :
    s ≤ criticalFloor n t r ↔ r * s ≤ n * t := by
  simp only [criticalFloor, Nat.le_div_iff_mul_le (by omega : 0 < r), Nat.mul_comm]

/-- Degrees from the ceiling onward are exactly on the surjective side. -/
theorem criticalCeil_le_iff {n t r s : ℕ} (hr : 1 ≤ r) :
    criticalCeil n t r ≤ s ↔ n * t ≤ r * s := by
  have h := Nat.div_lt_iff_lt_mul (x := n * t + r - 1) (y := s + 1)
    (by omega : 0 < r)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm s r] at h
  dsimp [criticalCeil]
  omega

/-- The floor lies on the injective side. -/
theorem criticalFloor_mul_le {n t r : ℕ} (hr : 1 ≤ r) :
    r * criticalFloor n t r ≤ n * t :=
  (le_criticalFloor_iff hr).mp le_rfl

/-- The ceiling lies on the surjective side. -/
theorem le_mul_criticalCeil {n t r : ℕ} (hr : 1 ≤ r) :
    n * t ≤ r * criticalCeil n t r :=
  (criticalCeil_le_iff hr).mp le_rfl

/-- Floor and ceiling are ordered. -/
theorem criticalFloor_le_criticalCeil {n t r : ℕ} (hr : 1 ≤ r) :
    criticalFloor n t r ≤ criticalCeil n t r := by
  apply (Nat.mul_le_mul_left_iff (by omega : 0 < r)).mp
  exact (criticalFloor_mul_le hr).trans (le_mul_criticalCeil hr)

/-- Floor and ceiling differ by at most one. -/
theorem criticalCeil_le_criticalFloor_add_one {n t r : ℕ} (hr : 1 ≤ r) :
    criticalCeil n t r ≤ criticalFloor n t r + 1 := by
  apply (criticalCeil_le_iff hr).mpr
  have h := (Nat.div_lt_iff_lt_mul (x := n * t)
    (y := n * t / r + 1) (by omega : 0 < r)).mp (Nat.lt_succ_self _)
  simpa only [criticalFloor, Nat.mul_comm] using Nat.le_of_lt h

/-- The two critical degrees are equal or consecutive. -/
theorem criticalCeil_eq_floor_or_succ {n t r : ℕ} (hr : 1 ≤ r) :
    criticalCeil n t r = criticalFloor n t r ∨
      criticalCeil n t r = criticalFloor n t r + 1 := by
  have h₁ := criticalFloor_le_criticalCeil (n := n) (t := t) hr
  have h₂ := criticalCeil_le_criticalFloor_add_one (n := n) (t := t) hr
  omega

/-- Every degree belongs to one of the two propagated ranges. -/
theorem degree_le_floor_or_ceil_le {n t r : ℕ} (hr : 1 ≤ r) (s : ℕ) :
    s ≤ criticalFloor n t r ∨ criticalCeil n t r ≤ s := by
  have h := criticalCeil_le_criticalFloor_add_one (n := n) (t := t) hr
  omega

/-- The floor has the dimension inequality needed for injectivity. -/
theorem criticalFloor_source_le_target {n t r : ℕ} (hr : 1 ≤ r) :
    steinerSourceDimension n t r (criticalFloor n t r) ≤
      steinerTargetDimension n t (criticalFloor n t r) :=
  (steinerSource_le_target_iff n t r _).mpr (criticalFloor_mul_le hr)

/-- The ceiling has the dimension inequality needed for surjectivity. -/
theorem criticalCeil_target_le_source {n t r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    steinerTargetDimension n t (criticalCeil n t r) ≤
      steinerSourceDimension n t r (criticalCeil n t r) :=
  (steinerTarget_le_source_iff hn t r _).mpr (le_mul_criticalCeil hr)

/-- The floor and ceiling coincide precisely when the critical ratio is integral. -/
theorem criticalCeil_eq_floor_iff_dvd {n t r : ℕ} (hr : 1 ≤ r) :
    criticalCeil n t r = criticalFloor n t r ↔ r ∣ n * t := by
  constructor
  · intro h
    have h₁ := criticalFloor_mul_le (n := n) (t := t) hr
    have h₂ := le_mul_criticalCeil (n := n) (t := t) hr
    rw [h] at h₂
    exact ⟨criticalFloor n t r, Nat.le_antisymm h₂ h₁⟩
  · intro h
    have heq : r * criticalFloor n t r = n * t := by
      dsimp [criticalFloor]
      exact Nat.mul_div_cancel' h
    apply Nat.le_antisymm
    · exact (criticalCeil_le_iff hr).mpr (Nat.le_of_eq heq.symm)
    · exact criticalFloor_le_criticalCeil hr

/-- In the rational boundary case, the critical degree is `t`. -/
theorem criticalFloor_self {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    criticalFloor n t n = t := by
  dsimp [criticalFloor]
  exact Nat.mul_div_cancel_left t (by omega)

/-- The ceiling is also `t` in the rational boundary case. -/
theorem criticalCeil_self {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    criticalCeil n t n = t := by
  rw [(criticalCeil_eq_floor_iff_dvd hn).mpr (dvd_mul_right n t), criticalFloor_self hn]

/-- Dimension of the actual target vector space of homogeneous forms. -/
theorem finrank_steinerTarget (K : Type*) [Field K] (n t s : ℕ) :
    Module.finrank K (Fin t → Forms K (n + 1) s) = steinerTargetDimension n t s := by
  have heq : n + 1 + s - 1 = n + s := by omega
  have hc : (n + s).choose s = (n + s).choose n :=
    Nat.choose_symm_of_eq_add (by omega : n + s = s + n)
  simp [Module.finrank_pi_fintype, finrank_forms, heq, hc, steinerTargetDimension]

/-- Dimension of the actual source vector space in positive degree. -/
theorem finrank_steinerSource_of_pos (K : Type*) [Field K]
    (n t r : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    Module.finrank K (Fin (t + r) → Forms K (n + 1) (s - 1)) =
      steinerSourceDimension n t r s := by
  have heq : n + 1 + (s - 1) - 1 = n + s - 1 := by omega
  have hc : (n + s - 1).choose (s - 1) = (n + s - 1).choose n :=
    Nat.choose_symm_of_eq_add (by omega : n + s - 1 = s - 1 + n)
  simp [Module.finrank_pi_fintype, finrank_forms, heq, hc, steinerSourceDimension,
    show s ≠ 0 by omega]

/-- Dimension comparison directly in the nonnegative twist convention. -/
theorem finrank_forms_source_le_target_iff (K : Type*) [Field K]
    (n t r q : ℕ) :
    Module.finrank K (Fin (t + r) → Forms K (n + 1) q) ≤
      Module.finrank K (Fin t → Forms K (n + 1) (q + 1)) ↔
        r * (q + 1) ≤ n * t := by
  have h := steinerSource_le_target_iff n t r (q + 1)
  rw [← finrank_steinerTarget K] at h
  rw [← finrank_steinerSource_of_pos K n t r (Nat.le_add_left 1 q)] at h
  simpa using h

/-- The reverse dimension comparison in the nonnegative twist convention. -/
theorem finrank_forms_target_le_source_iff (K : Type*) [Field K]
    {n : ℕ} (hn : 1 ≤ n) (t r q : ℕ) :
    Module.finrank K (Fin t → Forms K (n + 1) (q + 1)) ≤
      Module.finrank K (Fin (t + r) → Forms K (n + 1) q) ↔
        n * t ≤ r * (q + 1) := by
  have h := steinerTarget_le_source_iff hn t r (q + 1)
  rw [← finrank_steinerTarget K] at h
  rw [← finrank_steinerSource_of_pos K n t r (Nat.le_add_left 1 q)] at h
  simpa using h

/-- For positive parameters the first surjective degree is positive. -/
theorem criticalCeil_pos {n t r : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r) :
    1 ≤ criticalCeil n t r := by
  have hnt : 0 < n * t := Nat.mul_pos (by omega) (by omega)
  have h := criticalCeil_le_iff (n := n) (t := t) (s := 0) hr
  simp only [Nat.mul_zero] at h
  omega

/-- For positive projective dimension the binomial formula automatically vanishes at zero. -/
theorem steinerSourceDimension_eq {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    steinerSourceDimension n t r s = (t + r) * (n + s - 1).choose n := by
  by_cases hs : s = 0
  · subst s
    simp only [steinerSourceDimension_zero, Nat.add_zero]
    rw [Nat.choose_eq_zero_of_lt (by omega : n - 1 < n), Nat.mul_zero]
  · simp [steinerSourceDimension, hs]

/-- Euler characteristic: target dimension minus source dimension as an integer. -/
def steinerEulerCharacteristic (n t r s : ℕ) : ℤ :=
    steinerTargetDimension n t s - steinerSourceDimension n t r s

/-- An integral version of the binomial Euler-characteristic formula. -/
theorem steinerEulerCharacteristic_mul_dimension {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    (n : ℤ) * steinerEulerCharacteristic n t r s =
      ((n + s - 1).choose (n - 1) : ℤ) * ((n : ℤ) * t - (r : ℤ) * s) := by
  have hn' : n - 1 + 1 = n := by omega
  have hsum : n + s - 1 + 1 = n + s := by omega
  have hsub : n + s - 1 - (n - 1) = s := by omega
  have ht := Nat.add_one_mul_choose_eq (n + s - 1) (n - 1)
  rw [hn', hsum] at ht
  have hs := Nat.choose_succ_right_eq (n + s - 1) (n - 1)
  rw [hn', hsub] at hs
  have ht' : ((n + s).choose n : ℤ) * n =
      ((n + s - 1).choose (n - 1) : ℤ) * (n + s) := by
    exact_mod_cast (ht.symm.trans (Nat.mul_comm _ _))
  have hs' : ((n + s - 1).choose n : ℤ) * n =
      ((n + s - 1).choose (n - 1) : ℤ) * s := by exact_mod_cast hs
  dsimp [steinerEulerCharacteristic, steinerTargetDimension]
  rw [steinerSourceDimension_eq hn]
  push_cast
  calc
    _ = (t : ℤ) * (((n + s).choose n : ℤ) * n) -
        ((t : ℤ) + r) * (((n + s - 1).choose n : ℤ) * n) := by ring
    _ = _ := by rw [ht', hs']; ring

/-- Positive Euler characteristic is exactly the injective side of the crossing. -/
theorem steinerEulerCharacteristic_pos_iff {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    0 < steinerEulerCharacteristic n t r s ↔ r * s < n * t := by
  dsimp [steinerEulerCharacteristic]
  rw [sub_pos]
  exact_mod_cast steinerSource_lt_target_iff hn t r s

/-- Negative Euler characteristic is exactly the surjective side of the crossing. -/
theorem steinerEulerCharacteristic_neg_iff (n t r s : ℕ) :
    steinerEulerCharacteristic n t r s < 0 ↔ n * t < r * s := by
  dsimp [steinerEulerCharacteristic]
  rw [sub_neg]
  exact_mod_cast steinerTarget_lt_source_iff n t r s

/-- Vanishing Euler characteristic identifies the square critical map. -/
theorem steinerEulerCharacteristic_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) (t r s : ℕ) :
    steinerEulerCharacteristic n t r s = 0 ↔ r * s = n * t := by
  dsimp [steinerEulerCharacteristic]
  rw [sub_eq_zero]
  have h := steinerDimensions_eq_iff hn t r s
  have h' : steinerTargetDimension n t s = steinerSourceDimension n t r s ↔
      r * s = n * t := by
    rw [eq_comm]
    exact h
  exact_mod_cast h'

end Steiner
