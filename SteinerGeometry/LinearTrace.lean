import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! The normalized trace splits scalar extension for every module. -/

noncomputable section

namespace SteinerGeometry.LinearTrace

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [AddCommGroup S] [Module R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

def tensorTrace (t : S →ₗ[R] R) : S ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (TensorProduct.map t (LinearMap.id : M →ₗ[R] M))

@[simp]
theorem tensorTrace_tmul (t : S →ₗ[R] R) (s : S) (m : M) :
    tensorTrace t (s ⊗ₜ[R] m) = t s • m := by
  simp [tensorTrace]

theorem tensorTrace_section (t : S →ₗ[R] R) (s : S) (hs : t s = 1) (m : M) :
    tensorTrace t (s ⊗ₜ[R] m) = m := by
  rw [tensorTrace_tmul, hs, one_smul]

end SteinerGeometry.LinearTrace
