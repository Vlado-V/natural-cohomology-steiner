module

public import Steiner.Numerics
public import Steiner.GenericBaseChange
public import Steiner.Fiber

@[expose] public section

noncomputable section
namespace Steiner
open Module MvPolynomial

variable {K L : Type*} [Field K] [Field L] {n t r : ℕ}

/-- Injectivity at the paper's last injective degree. -/
def CriticalInjective (M : LinearMatrix K n t (t + r)) : Prop :=
  0 < criticalFloor n t r →
    Function.Injective (linearMatrixMap M (criticalFloor n t r - 1))

/-- Surjectivity at the paper's first surjective degree. -/
def CriticalSurjective (M : LinearMatrix K n t (t + r)) : Prop :=
  Function.Surjective (linearMatrixMap M (criticalCeil n t r - 1))

/-- An all-degree matrix witness has the required critical injectivity. -/
theorem criticalInjective_of_all_ranks
    (M : LinearMatrix K n t (t + r)) (hr : 1 ≤ r)
    (hM : ∀ d, LinearMatrixMaximalRank M d) : CriticalInjective M := by
  intro hpos
  apply (linearMatrixMaximalRank_iff_injective M _ ?_).mp (hM _)
  apply (finrank_forms_source_le_target_iff K n t r _).mpr
  simpa only [Nat.sub_add_cancel hpos] using
    (criticalFloor_mul_le (n := n) (t := t) hr)

/-- An all-degree matrix witness has the required critical surjectivity. -/
theorem criticalSurjective_of_all_ranks
    (M : LinearMatrix K n t (t + r)) (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (hM : ∀ d, LinearMatrixMaximalRank M d) : CriticalSurjective M := by
  apply (linearMatrixMaximalRank_iff_surjective M _ ?_).mp (hM _)
  apply (finrank_forms_target_le_source_iff K hn t r _).mpr
  simpa only [Nat.sub_add_cancel (criticalCeil_pos hn ht hr)] using
    (le_mul_criticalCeil (n := n) (t := t) hr)

/-- Both critical conditions imply maximal rank in every positive paper degree. -/
theorem all_ranks_of_critical
    (M : LinearMatrix K n t (t + r)) (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (hi : CriticalInjective M) (hs : CriticalSurjective M) :
    ∀ d, LinearMatrixMaximalRank M d := by
  intro d
  have hc := criticalCeil_pos hn ht hr
  by_cases hd : d + 1 ≤ criticalFloor n t r
  · exact linearMatrixMaximalRank_of_injective M d
      (linearMatrixMap_injective_downward M (by omega) (hi (by omega)))
  · apply linearMatrixMaximalRank_of_surjective M d
    apply linearMatrixMap_surjective_upward M (h := hs)
    have h := degree_le_floor_or_ceil_le (n := n) (t := t) hr (d + 1)
    omega

/-- One principal open in the actual scalar coefficient space, not an
intersection of infinitely many degree-wise opens. -/
def GenericMatrixConclusion (K : Type*) [Field K] (n t r : ℕ) : Prop :=
  ∃ D : MvPolynomial (LinearMatrixParameter n t (t + r)) K,
    (∃ u, eval u D ≠ 0) ∧
    ∀ u, eval u D ≠ 0 →
      ∀ d, LinearMatrixMaximalRank (universalLinearMatrix K n t (t + r) u) d

/-- A single actual all-degree witness over an extension proves the generic
matrix assertion over the original infinite field. -/
theorem genericMatrixConclusion_of_extension_witness [Infinite K]
    (k : K →+* L) (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : LinearMatrix L n t (t + r)) (hM : ∀ d, LinearMatrixMaximalRank M d) :
    GenericMatrixConclusion K n t r := by
  have hi := criticalInjective_of_all_ranks M hr hM
  have hs := criticalSurjective_of_all_ranks M hn ht hr hM
  by_cases hb : 0 < criticalFloor n t r
  · apply universalLinearMatrix_allTwists_principal_open_of_extension k M
      (criticalFloor n t r - 1) (criticalCeil n t r - 1) ?_ (hi hb) hs
    have h := criticalCeil_le_criticalFloor_add_one (n := n) (t := t) hr
    omega
  · have hc : criticalCeil n t r = 1 := by
      have h₁ := criticalCeil_le_criticalFloor_add_one (n := n) (t := t) hr
      have h₂ := criticalCeil_pos hn ht hr
      omega
    apply universalLinearMatrix_allTwists_principal_open_of_extension_surjective_zero k M
    change Function.Surjective (linearMatrixMap M (criticalCeil n t r - 1)) at hs
    rw [hc] at hs
    exact hs

/-- An all-degree maximal-rank matrix is fiberwise surjective at every
nonzero homogeneous coordinate vector. -/
theorem fiberMap_surjective_of_all_ranks
    (M : LinearMatrix K n t (t + r)) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hM : ∀ d, LinearMatrixMaximalRank M d)
    (x : Fin (n + 1) → K) (hx : x ≠ 0) : Function.Surjective (fiberMap M x) := by
  apply fiberMap_surjective_of_homogeneous M (n * t) ?_ x hx
  apply (linearMatrixMaximalRank_iff_surjective M _ ?_).mp (hM _)
  apply (finrank_forms_target_le_source_iff K hn t r _).mpr
  have h := Nat.mul_le_mul_right (n * t + 1) hr
  simp only [one_mul] at h
  exact (Nat.le_succ (n * t)).trans h

/-- The degree-zero convention is the actual zero map from a zero-dimensional
source. It is injective, as required by the paper's `S₋₁ = 0` convention. -/
theorem degree_zero_injective :
    Function.Injective (0 : (Fin 0 → K) →ₗ[K] (Fin t → Forms K (n + 1) 0)) := by
  intro v w _
  exact Subsingleton.elim _ _

end Steiner
