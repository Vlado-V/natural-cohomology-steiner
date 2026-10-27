import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Support of a finite module is detected by its actual fiber over any field. -/
noncomputable section
namespace SteinerGeometry.SupportFieldFiber
open TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {S : Type v} [Field S]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem mem_support_iff_nontrivial_fieldTensor (φ : R →+* S) :
    letI := φ.toAlgebra
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) ∈ Module.support R M ↔
      Nontrivial (S ⊗[R] M) := by
  letI := φ.toAlgebra
  let p : PrimeSpectrum R := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  haveI : p.asIdeal.IsPrime := p.isPrime
  let K := p.asIdeal.ResidueField
  have hunit : p.asIdeal.primeCompl ≤ (IsUnit.submonoid S).comap φ := by
    intro x hx
    exact isUnit_iff_ne_zero.mpr hx
  let ψ : K →+* S := Ideal.ResidueField.lift p.asIdeal φ le_rfl hunit
  letI := ψ.toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p.asIdeal φ le_rfl hunit r).symm)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let e := AlgebraTensorModule.cancelBaseChange R K S S M
  exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right K S).symm.trans e.nontrivial_congr

end SteinerGeometry.SupportFieldFiber
