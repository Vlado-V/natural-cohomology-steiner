module

public import Steiner.LinearMatrix

@[expose] public section

/-! Pointwise surjectivity of a matrix whose homogeneous cokernel vanishes.
All maps here are actual polynomial evaluation maps. -/

noncomputable section
namespace Steiner
open MvPolynomial

variable {K : Type*} [Field K] {n a c : ℕ}

/-- The scalar matrix obtained by evaluating each linear entry at `x`. -/
def fiberMap (L : LinearMatrix K n a c) (x : Fin (n + 1) → K) :
    (Fin c → K) →ₗ[K] (Fin a → K) where
  toFun v i := ∑ j, eval x (L i j).val * v j
  map_add' v w := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' k v := by
    funext i
    simp [Finset.mul_sum, mul_left_comm]

/-- Evaluation commutes with the homogeneous multiplication map. -/
theorem eval_linearMatrixMap (L : LinearMatrix K n a c)
    (x : Fin (n + 1) → K) (d : ℕ) (v : MatrixSource K n c d) :
    (fun i => eval x (linearMatrixMap L d v i).val) =
      fiberMap L x (fun j => eval x (v j).val) := by
  funext i
  simp [linearMatrixMap, fiberMap]

/-- Vanishing of the homogeneous cokernel forces surjectivity at every
projective point, expressed using a nonzero homogeneous coordinate vector. -/
theorem fiberMap_surjective_of_homogeneous
    (L : LinearMatrix K n a c) (d : ℕ)
    (h : Function.Surjective (linearMatrixMap L d))
    (x : Fin (n + 1) → K) (hx : x ≠ 0) :
    Function.Surjective (fiberMap L x) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! he
    exact hx (funext he)
  let yForm (y : Fin a → K) : MatrixTarget K n a d := fun i =>
    ⟨C (y i) * X j ^ (d + 1), by
      simpa using (isHomogeneous_C (Fin (n + 1)) (y i)).mul ((isHomogeneous_X K j).pow (d + 1))⟩
  intro y
  obtain ⟨v, hv⟩ := h (yForm y)
  let w : Fin c → K := fun k => (x j ^ (d + 1))⁻¹ * eval x (v k).val
  refine ⟨w, ?_⟩
  have he := eval_linearMatrixMap L x d v
  rw [hv] at he
  funext i
  have hei := congrFun he i
  have hpow : x j ^ (d + 1) ≠ 0 := pow_ne_zero _ hj
  change ∑ k, eval x (L i k).val *
      ((x j ^ (d + 1))⁻¹ * eval x (v k).val) = y i
  calc
    _ = (x j ^ (d + 1))⁻¹ *
        (∑ k, eval x (L i k).val * eval x (v k).val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (x j ^ (d + 1))⁻¹ * (y i * x j ^ (d + 1)) := by
      congr 1
      simpa [yForm, fiberMap] using hei.symm
    _ = y i := by field_simp

end Steiner
