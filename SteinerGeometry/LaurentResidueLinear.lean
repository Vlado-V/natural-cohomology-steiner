import SteinerGeometry.LaurentResidueShift

/-! # Linear forms on Laurent factors and their residue transpose -/
noncomputable section
namespace SteinerGeometry.LaurentResidueShift
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open LaurentMultiplication ProjectiveResiduePairing

universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ] [Fintype σ]

/-- Complementary coefficient extraction is linear on the actual Laurent factor. -/
def residueProjection {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (m : ℕ) (d : ℤ)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ)) :
    AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d) →ₗ[Γ(Spec (.of R), ⊤)]
      ResidueCoefficients σ Γ(Spec (.of R), ⊤) m where
  toFun := residueCoefficients a ha m d hd
  map_add' x y := by
    funext e
    simp [residueCoefficients]
  map_smul' r x := by
    funext e
    simp [residueCoefficients]

/-- The actual Laurent factor map associated to a linear form. -/
def linearFormFactor {q : ℕ} (a : Fin (q + 1) → σ) (d : ℤ)
    (L : σ → Γ(Spec (.of R), ⊤)) :
    AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d) →ₗ[Γ(Spec (.of R), ⊤)]
      AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a (d + 1)) :=
  ∑ j, L j • shiftFactor (R := R) a d j

/-- Complementary Laurent coefficients of multiplication by a linear form
are exactly the transpose of polynomial multiplication by that form. -/
theorem residueProjection_linearFormFactor {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (m : ℕ) (d : ℤ)
    (hsource : d = -((m + 1 : ℕ) : ℤ) - (Fintype.card σ : ℤ))
    (htarget : d + 1 = -(m : ℤ) - (Fintype.card σ : ℤ))
    (L : σ → Γ(Spec (.of R), ⊤)) :
    (residueProjection (R := R) a ha m (d + 1) htarget).comp (linearFormFactor a d L) =
      (multiplyResidueLinearForm m L).comp
        (residueProjection (R := R) a ha (m + 1) d hsource) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, linearFormFactor, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  change (∑ j, L j • residueCoefficients a ha m (d + 1) htarget
      (shiftFactor (R := R) a d j x)) = _
  simp only [residueCoefficients_shiftFactor a ha m d _ hsource htarget]
  simp only [multiplyResidueLinearForm, LinearMap.sum_apply, LinearMap.smul_apply,
    residueProjection]
  rfl

/-- The residue pairing computes the adjoint of an actual Laurent-factor
linear-form map, coefficient by coefficient. -/
theorem pairing_linearFormFactor {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (m : ℕ) (d : ℤ)
    (hsource : d = -((m + 1 : ℕ) : ℤ) - (Fintype.card σ : ℤ))
    (htarget : d + 1 = -(m : ℤ) - (Fintype.card σ : ℤ))
    (L : σ → Γ(Spec (.of R), ⊤))
    (p : PolynomialCoefficients σ Γ(Spec (.of R), ⊤) m)
    (x : AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d)) :
    pairing p (residueProjection a ha m (d + 1) htarget (linearFormFactor a d L x)) =
      pairing (multiplyLinearForm m L p)
        (residueProjection a ha (m + 1) d hsource x) := by
  have h := LinearMap.congr_fun
    (residueProjection_linearFormFactor a ha m d hsource htarget L) x
  change residueProjection a ha m (d + 1) htarget (linearFormFactor a d L x) = _ at h
  rw [h]
  exact (pairing_multiplyLinearForm m L p _).symm

end SteinerGeometry.LaurentResidueShift
