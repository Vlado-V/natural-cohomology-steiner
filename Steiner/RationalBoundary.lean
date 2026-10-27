module

public import Steiner.LinearMatrix
public import Steiner.RationalErase

@[expose] public section

/-! An elementary rational-boundary construction. The banded Toeplitz matrix
has no polynomial syzygy below its row count. Erasing the first variable and
then dividing by it proves this simultaneously in every number of variables. -/

noncomputable section
namespace Steiner
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- The row equations of a banded Toeplitz matrix. -/
def RationalToeplitzEquations (n a : ℕ) (f : ℕ → Poly K (n+1)) : Prop :=
  ∀ i < a, ∑ k : Fin (n+1), X k * f (i + k.val) = 0

/-- A homogeneous polynomial syzygy below the row count vanishes. -/
theorem rationalToeplitz_syzygy_zero (n a d : ℕ) (f : ℕ → Poly K (n+1))
    (hf : ∀ i < a+n, (f i).IsHomogeneous d)
    (heq : RationalToeplitzEquations n a f) (hda : d < a) :
    ∀ i < a+n, f i = 0 := by
  induction n generalizing a d with
  | zero =>
    intro i hi
    have h := heq i (by omega)
    have hh : X (0 : Fin 1) * f i = 0 := by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Nat.add_zero] using h
    exact (mul_eq_zero.mp hh).resolve_left (X_ne_zero 0)
  | succ n hn =>
    induction a generalizing d f with
    | zero => omega
    | succ a ha =>
      have hdiv : ∀ i < a+n+1, X (0 : Fin (n+1+1)) ∣ f (i+1) := by
        intro i hi
        apply x_dvd_of_eraseFirst_eq_zero
        let g : ℕ → Poly K (n+1) := fun j => eraseFirst (f (j+1))
        have hgh : ∀ j < (a+1)+n, (g j).IsHomogeneous d := by
          intro j hj
          exact eraseFirst_isHomogeneous (hf (j+1) (by omega))
        have hgeq : RationalToeplitzEquations n (a+1) g := by
          intro j hj
          have h := congrArg eraseFirst (heq j hj)
          rw [Fin.sum_univ_succ, map_add, map_mul, eraseFirst_X_zero, zero_mul, zero_add, map_sum] at h
          simpa only [map_mul, eraseFirst_X_succ, Fin.val_succ, Nat.add_assoc, Nat.add_right_comm, g, map_zero] using h
        exact hn (a+1) d g hgh hgeq hda i (by omega)
      have htail : ∀ i < a+n+1, f (i+1) = 0 := by
        cases d with
        | zero =>
          intro i hi
          exact homogeneous_zero_of_x_dvd (f (i+1)) (hf (i+1) (by omega)) (hdiv i hi)
        | succ d =>
          let g : ℕ → Poly K (n+1+1) :=
            fun i => (f (i+1)).divMonomial (Finsupp.single 0 1)
          have hfg : ∀ i < a+n+1, X 0 * g i = f (i+1) := by
            intro i hi
            exact x_mul_div_of_x_dvd (f (i+1)) (hdiv i hi)
          have hgh : ∀ i < a+(n+1), (g i).IsHomogeneous d := by
            intro i hi
            exact homogeneous_div_x (f (i+1)) (hf (i+1) (by omega))
          have hgeq : RationalToeplitzEquations (n+1) a g := by
            intro j hj
            have h := heq (j+1) (by omega)
            have hh : X (0 : Fin (n+1+1)) *
                (∑ k : Fin (n+1+1), X k * g (j+k.val)) = 0 := by
              rw [Finset.mul_sum]
              convert h using 1
              apply Finset.sum_congr rfl
              intro k hk
              rw [show j+1+k.val = j+k.val+1 by omega, ← hfg (j+k.val) (by omega)]
              ring
            exact (mul_eq_zero.mp hh).resolve_left (X_ne_zero 0)
          have hgz := ha d g hgh hgeq (by omega)
          intro i hi
          rw [← hfg i hi, hgz i (by omega), mul_zero]
      have hf0 : f 0 = 0 := by
        have h := heq 0 (by omega)
        rw [Fin.sum_univ_succ] at h
        have hz : (∑ k : Fin (n+1), X k.succ * f (0+k.succ.val)) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [show 0+k.succ.val = k.val+1 by simp, htail k.val (by omega), mul_zero]
        simp only [Fin.val_zero, hz, add_zero] at h
        exact (mul_eq_zero.mp h).resolve_left (X_ne_zero 0)
      intro i hi
      cases i with
      | zero => exact hf0
      | succ i => exact htail i (by omega)

end Steiner

namespace Steiner
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- The banded matrix with `x₀,…,xₙ` in every row, shifted one step per row. -/
def rationalToeplitzMatrix (K : Type*) [Field K] (n a : ℕ) :
    LinearMatrix K n a (a+n) := fun i j =>
  ⟨∑ k : Fin (n+1), if j = (⟨i.val+k.val, by omega⟩ : Fin (a+n)) then X k else 0, by
    apply IsHomogeneous.sum
    intro k hk
    split_ifs
    · exact isHomogeneous_X K k
    · exact (Forms K (n+1) 1).zero_mem⟩

@[simp] theorem rationalToeplitzMatrix_map_val {n a d : ℕ}
    (v : MatrixSource K n (a+n) d) (i : Fin a) :
    (linearMatrixMap (rationalToeplitzMatrix K n a) d v i).val =
      ∑ k : Fin (n+1), X k * (v ⟨i.val+k.val, by omega⟩).val := by
  classical
  simp only [linearMatrixMap_val, rationalToeplitzMatrix, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- The rational construction is injective strictly below the number of rows. -/
theorem rationalToeplitzMatrix_injective {n a d : ℕ} (hda : d < a) :
    Function.Injective (linearMatrixMap (rationalToeplitzMatrix K n a) d) := by
  intro v w hvw
  have hzero : linearMatrixMap (rationalToeplitzMatrix K n a) d (v-w) = 0 := by
    rw [map_sub, hvw, sub_self]
  let f : ℕ → Poly K (n+1) := fun i =>
    if h : i < a+n then ((v-w) ⟨i,h⟩).val else 0
  have hf : ∀ i < a+n, (f i).IsHomogeneous d := by
    intro i hi
    simp only [f, dite_eq_left hi]
    exact ((v-w) ⟨i,hi⟩).property
  have heq : RationalToeplitzEquations n a f := by
    intro i hi
    have h := congrArg (fun u : MatrixTarget K n a d => (u ⟨i,hi⟩).val) hzero
    simp only [rationalToeplitzMatrix_map_val, Pi.zero_apply, Submodule.coe_zero] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f, dite_eq_left (show i+k.val < a+n by omega)]
  have hz := rationalToeplitz_syzygy_zero n a d f hf heq hda
  funext i
  apply sub_eq_zero.mp
  apply Subtype.ext
  have h := hz i.val i.isLt
  simpa only [f, dite_eq_left i.isLt, Pi.sub_apply, Submodule.coe_zero] using h

/-- At the critical twist the rational matrix is square and invertible. -/
theorem rationalToeplitzMatrix_bijective {n a : ℕ} (ha : 0 < a) :
    Function.Bijective (linearMatrixMap (rationalToeplitzMatrix K n a) (a-1)) := by
  have hi := rationalToeplitzMatrix_injective (K := K) (n := n) (by omega : a-1 < a)
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi
  rw [finrank_matrixSource, finrank_matrixTarget]
  have h := Nat.add_one_mul_choose_eq (n+(a-1)) (a-1)
  have hna : n+(a-1)+1 = n+a := by omega
  have ha' : a-1+1 = a := by omega
  simpa only [hna, ha', Nat.add_comm, Nat.mul_comm] using h

/-- One explicit matrix has maximal rank in every degree at the boundary `r=n`.
The elementary construction in fact works over every field. -/
theorem rationalToeplitzMatrix_maximalRank {n a : ℕ} (ha : 0 < a) :
    ∀ d, LinearMatrixMaximalRank (rationalToeplitzMatrix K n a) d :=
  linearMatrixMaximalRank_all_of_bijective _ (a-1) (rationalToeplitzMatrix_bijective ha)

/-- The all-degree rational-boundary existence theorem. -/
theorem exists_rationalBoundary_maximalRank (n a : ℕ) (ha : 0 < a) :
    ∃ L : LinearMatrix K n a (a+n), ∀ d, LinearMatrixMaximalRank L d :=
  ⟨rationalToeplitzMatrix K n a, rationalToeplitzMatrix_maximalRank ha⟩

end Steiner
