import SteinerGeometry.LaurentResidueLinear
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap

/-! Homogeneous Laurent coordinates identify multiplication by a dehomogenized
coordinate with the actual exponent shift. -/
noncomputable section
namespace SteinerGeometry.LaurentChartMultiplication
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open LaurentMultiplication
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

abbrev RawExponent {q : ℕ} (a : Fin (q+1) → σ) :=
  LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
    (StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)

abbrev Raw {q : ℕ} (a : Fin (q+1) → σ) :=
  AddMonoidAlgebra Γ(Spec (.of R), ⊤) (RawExponent a)

def reindex {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) :
    Raw (R := R) a ≃ₗ[Γ(Spec (.of R), ⊤)]
      AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d) :=
  AddMonoidAlgebra.mapDomainLinearEquiv _ _
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d)

/-- The local coordinate ratio has precisely the translated global exponent. -/
theorem exponent_shift {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ)
    (e : RawExponent a) :
    LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (d+1)
      (e + PolynomialChartMap.MvPolynomial.polynomialChartExponent a (Finsupp.single j 1)) =
    shiftAllowed a d j (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d e) := by
  apply (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (d+1)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  ext i
  rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_symm_apply]
  change e.val i +
      (PolynomialChartMap.MvPolynomial.polynomialChartExponent a (Finsupp.single j 1)).val i =
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d e).val.val i.val +
      (Finsupp.single j (1 : ℤ)) i.val
  rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne a d e i.val i.property]
  simp [PolynomialChartMap.MvPolynomial.polynomialChartExponent, Finsupp.single_apply]

/-- Multiplication by a coordinate polynomial in a chart induces the homogeneous
Laurent exponent-shift linear map. -/
theorem reindex_mul_X {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ)
    (x : Raw (R := R) a) :
    reindex (R := R) a (d+1)
      (x * PolynomialChartMap.MvPolynomial.polynomialChartRingHom
        Γ(Spec (.of R), ⊤) a (MvPolynomial.X j)) =
      shiftFactor (R := R) a d j (reindex (R := R) a d x) := by
  let s : Raw (R := R) a := PolynomialChartMap.MvPolynomial.polynomialChartRingHom
    Γ(Spec (.of R), ⊤) a (MvPolynomial.X j)
  have hmap : (reindex (R := R) a (d+1)).toLinearMap.comp
      (LinearMap.mulRight Γ(Spec (.of R), ⊤) s) =
      (shiftFactor (R := R) a d j).comp (reindex (R := R) a d).toLinearMap := by
    apply AddMonoidAlgebra.lhom_ext'
    intro e
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AddMonoidAlgebra.lsingle_apply, s, MvPolynomial.X,
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial,
      AddMonoidAlgebra.single_mul_single, mul_one, reindex,
      LinearEquiv.coe_coe, AddMonoidAlgebra.mapDomainLinearEquiv_single, shiftFactor_single]
    rw [exponent_shift]
  exact LinearMap.congr_fun hmap x

/-- The polynomial determined by the coordinate coefficients of a linear form. -/
def linearPolynomial (L : σ → Γ(Spec (.of R), ⊤)) : MvPolynomial σ Γ(Spec (.of R), ⊤) :=
  ∑ j, MvPolynomial.monomial (Finsupp.single j 1) (L j)

/-- Reindexing raw Laurent coordinates turns multiplication by an arbitrary
linear polynomial into the actual finite sum of homogeneous exponent shifts. -/
theorem reindex_mul_linearPolynomial {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ)
    (L : σ → Γ(Spec (.of R), ⊤)) (x : Raw (R := R) a) :
    reindex (R := R) a (d+1)
      (x * PolynomialChartMap.MvPolynomial.polynomialChartRingHom
        Γ(Spec (.of R), ⊤) a (linearPolynomial L)) =
      LaurentResidueShift.linearFormFactor a d L (reindex (R := R) a d x) := by
  simp only [linearPolynomial, map_sum, Finset.mul_sum,
    LaurentResidueShift.linearFormFactor, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hmon : PolynomialChartMap.MvPolynomial.polynomialChartRingHom
      Γ(Spec (.of R), ⊤) a (MvPolynomial.monomial (Finsupp.single j 1) (L j)) =
      L j • PolynomialChartMap.MvPolynomial.polynomialChartRingHom
        Γ(Spec (.of R), ⊤) a (MvPolynomial.X j) := by
    simp only [MvPolynomial.X, PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial,
      AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hmon, mul_smul_comm, map_smul, reindex_mul_X]

end SteinerGeometry.LaurentChartMultiplication
