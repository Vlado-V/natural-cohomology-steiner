import SteinerGeometry.KernelMonomialCoordinates
import Mathlib.LinearAlgebra.Pi

/-! Completing a frame of an actual functional kernel by one unit-valued vector. -/
noncomputable section
namespace SteinerGeometry
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}

/-- A splitting vector together with a frame of the kernel gives coordinates on the whole module. -/
def functionalFrameMap (ell : (Fin (n+1) → R) →ₗ[R] R)
    (v0 : Fin (n+1) → R) (E : (Fin n → R) ≃ₗ[R] ell.ker) :
    (Fin (n+1) → R) →ₗ[R] (Fin (n+1) → R) where
  toFun x := x 0 • v0 + (E (fun i => x i.succ)).val
  map_add' x y := by
    change (x 0 + y 0) • v0 + (E ((fun i => x i.succ) + (fun i => y i.succ))).val = _
    simp only [add_smul, map_add, Submodule.coe_add]
    abel
  map_smul' r x := by
    change (r * x 0) • v0 + (E (r • (fun i => x i.succ))).val = _
    simp only [map_smul, Submodule.coe_smul, smul_add, mul_smul, RingHom.id_apply]

theorem functionalFrameMap_value (ell : (Fin (n+1) → R) →ₗ[R] R)
    (v0 : Fin (n+1) → R) (h0 : ell v0 = 1)
    (E : (Fin n → R) ≃ₗ[R] ell.ker) (x : Fin (n+1) → R) :
    ell (functionalFrameMap ell v0 E x) = x 0 := by
  change ell (x 0 • v0 + (E (fun i => x i.succ)).val) = _
  rw [map_add, map_smul, h0, show ell (E (fun i => x i.succ)).val = 0 from
    (E (fun i => x i.succ)).property]
  simp

theorem functionalFrameMap_bijective (ell : (Fin (n+1) → R) →ₗ[R] R)
    (v0 : Fin (n+1) → R) (h0 : ell v0 = 1)
    (E : (Fin n → R) ≃ₗ[R] ell.ker) : Function.Bijective (functionalFrameMap ell v0 E) := by
  constructor
  · intro x y h
    have hxy : x 0 = y 0 := by
      simpa only [functionalFrameMap_value ell v0 h0 E] using congrArg ell h
    have hE : E (fun i => x i.succ) = E (fun i => y i.succ) := by
      apply Subtype.ext
      change x 0 • v0 + (E (fun i => x i.succ)).val =
        y 0 • v0 + (E (fun i => y i.succ)).val at h
      rw [hxy] at h
      exact add_left_cancel h
    have ht := E.injective hE
    funext i
    exact Fin.cases hxy (fun j => congrFun ht j) i
  · intro v
    let k : ell.ker := ⟨v - ell v • v0, by simp [map_sub, map_smul, h0]⟩
    refine ⟨Fin.cases (ell v) (E.symm k), ?_⟩
    change ell v • v0 + (E (fun i => E.symm k i)).val = v
    rw [E.apply_symm_apply]
    dsimp [k]
    abel

/-- The corresponding full frame equivalence. -/
def functionalFrameEquiv (ell : (Fin (n+1) → R) →ₗ[R] R)
    (v0 : Fin (n+1) → R) (h0 : ell v0 = 1)
    (E : (Fin n → R) ≃ₗ[R] ell.ker) :
    (Fin (n+1) → R) ≃ₗ[R] (Fin (n+1) → R) :=
  LinearEquiv.ofBijective (functionalFrameMap ell v0 E) (functionalFrameMap_bijective ell v0 h0 E)

private theorem pi_as_sum (x : Fin (n+1) → R) :
    x = ∑ i, x i • Pi.single i (1 : R) := by
  classical
  funext j
  simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply]

private theorem linearMap_rows (F : (Fin (n+1) → R) →ₗ[R] (Fin (n+1) → R))
    (x : Fin (n+1) → R) (j : Fin (n+1)) :
    F x j = ∑ i, x i * F (Pi.single i 1) j := by
  conv_lhs => rw [pi_as_sum x]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
/-- A kernel frame has an invertible completion whose first row splits the functional. -/
theorem exists_kernelFrame_matrices (ell : (Fin (n+1) → R) →ₗ[R] R)
    (v0 : Fin (n+1) → R) (h0 : ell v0 = 1)
    (E : (Fin n → R) ≃ₗ[R] ell.ker) :
    ∃ A B : Matrix (Fin (n+1)) (Fin (n+1)) R,
      A * B = 1 ∧ B * A = 1 ∧ A 0 = v0 ∧
      (∀ i : Fin n, A i.succ = (E (Pi.single i 1)).val) ∧
      (∀ i, ∑ j, ell (Pi.single j 1) * A i j = if i = 0 then 1 else 0) := by
  classical
  let F := functionalFrameEquiv ell v0 h0 E
  let A : Matrix (Fin (n+1)) (Fin (n+1)) R := fun i => F (Pi.single i 1)
  let B : Matrix (Fin (n+1)) (Fin (n+1)) R := fun i => F.symm (Pi.single i 1)
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    change (∑ k, F (Pi.single i 1) k * F.symm (Pi.single k 1) j) = _
    calc
      _ = F.symm (F (Pi.single i 1)) j := (linearMap_rows F.symm.toLinearMap _ j).symm
      _ = _ := by simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · ext i j
    change (∑ k, F.symm (Pi.single i 1) k * F (Pi.single k 1) j) = _
    calc
      _ = F (F.symm (Pi.single i 1)) j := (linearMap_rows F.toLinearMap _ j).symm
      _ = _ := by simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · dsimp [A, F, functionalFrameEquiv, functionalFrameMap]
    have ht : (fun i : Fin n => (Pi.single (0 : Fin (n+1)) (1 : R) : Fin (n+1) → R) i.succ) = 0 := by
      funext i
      simp
    rw [ht, map_zero]
    simp
  · intro i
    dsimp [A, F, functionalFrameEquiv, functionalFrameMap]
    have ht : (fun j : Fin n => (Pi.single i.succ (1 : R) : Fin (n+1) → R) j.succ) = Pi.single i 1 := by
      funext j
      simp [Pi.single_apply, Fin.succ_inj]
    rw [ht]
    simp
  · intro i
    have he : ell (F (Pi.single i 1)) = (Pi.single i (1 : R) : Fin (n+1) → R) 0 := by
      exact functionalFrameMap_value ell v0 h0 E _
    have hs : ell (F (Pi.single i 1)) =
        ∑ j, F (Pi.single i 1) j * ell (Pi.single j 1) := by
      conv_lhs => rw [pi_as_sum (F (Pi.single i 1))]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [hs] at he
    simpa [A, mul_comm, Pi.single_apply, eq_comm] using he

end SteinerGeometry
