module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option backward.privateInPublic true
@[expose] public section

/-! # The finite Laurent coefficient pairing

This proves the coefficient identity behind projective Serre duality without
inferring any map identity from dimensions. A full-negative exponent paired
with a monomial `a` is `(-a_i-1)_i`. Multiplication by `x_i` on negative
Laurent coefficients is transposed to multiplication by `x_i` on monomials.
The separate geometric comparison must identify these coefficient maps with
the map induced on actual sheaf cohomology.
-/

noncomputable section
namespace SteinerGeometry.ProjectiveResiduePairing

open scoped BigOperators

variable {σ R : Type*} [CommRing R]

/-- Precisely the monomial index subtype occurring in OAI's
`fullNegativeLaurentWeightEquivDegree`. -/
abbrev DegreeMonomial (σ : Type*) (m : ℕ) :=
  {a : σ →₀ ℕ // Finsupp.degree a = m}

/-- The full-negative exponent complementary to an ordinary monomial. -/
def negativeExponent {m : ℕ} (a : DegreeMonomial σ m) (i : σ) : ℤ :=
  -(a.val i : ℤ) - 1

@[simp] theorem negativeExponent_lt_zero {m : ℕ} (a : DegreeMonomial σ m) (i : σ) :
    negativeExponent a i < 0 := by
  dsimp [negativeExponent]
  omega

/-- Multiply a monomial index by the variable `x_i`. -/
def raiseCoordinate (m : ℕ) (i : σ) (a : DegreeMonomial σ m) : DegreeMonomial σ (m+1) :=
  ⟨a.val + Finsupp.single i 1, by simp [a.property]⟩

@[simp] theorem raiseCoordinate_val (m : ℕ) (i : σ) (a : DegreeMonomial σ m) :
    (raiseCoordinate m i a).val = a.val + Finsupp.single i 1 := rfl

/-- Monomial multiplication by a variable is injective on exponent indices. -/
theorem raiseCoordinate_injective (m : ℕ) (i : σ) :
    Function.Injective (raiseCoordinate m i : DegreeMonomial σ m → DegreeMonomial σ (m+1)) := by
  intro a b hab
  apply Subtype.ext
  exact add_right_cancel (congrArg Subtype.val hab)

/-- Complementary exponents turn positive multiplication into negative
Laurent multiplication in the reverse direction. -/
theorem negativeExponent_raiseCoordinate (m : ℕ) (i j : σ) (a : DegreeMonomial σ m) :
    negativeExponent (raiseCoordinate m i a) j + (Finsupp.single i (1 : ℤ)) j =
      negativeExponent a j := by
  classical
  by_cases hij : i = j
  · subst j
    simp [negativeExponent, raiseCoordinate]
    omega
  · simp [negativeExponent, raiseCoordinate, hij]

/-- A source exponent with zero `i`th ordinary coordinate becomes zero in
that Laurent coordinate after multiplication and therefore leaves full-negative support. -/
theorem negativeExponent_add_variable_eq_zero_iff {m : ℕ}
    (a : DegreeMonomial σ m) (i : σ) :
    negativeExponent a i + 1 = 0 ↔ a.val i = 0 := by
  dsimp [negativeExponent]
  omega

/-- Finite polynomial coefficient vectors. -/
abbrev PolynomialCoefficients (σ : Type*) (R : Type*) [Zero R] (m : ℕ) :=
  DegreeMonomial σ m →₀ R

/-- Full-negative Laurent coefficient vectors after the complementary
exponent reindexing. The OAI top-cohomology model is a function space. -/
abbrev ResidueCoefficients (σ R : Type*) (m : ℕ) :=
  DegreeMonomial σ m → R

/-- Coefficientwise residue pairing. -/
def pairing {m : ℕ} (p : PolynomialCoefficients σ R m)
    (q : ResidueCoefficients σ R m) : R :=
  Finsupp.linearCombination R q p

@[simp] theorem pairing_single {m : ℕ} (a : DegreeMonomial σ m) (r : R)
    (q : ResidueCoefficients σ R m) :
    pairing (Finsupp.single a r) q = r * q a := by
  simp [pairing]

/-- The residue pairing is perfect: every linear functional is uniquely
represented by its values on individual monomials. This requires no dimension count. -/
def coefficientDualEquiv (m : ℕ) :
    ResidueCoefficients σ R m ≃ₗ[R] Module.Dual R (PolynomialCoefficients σ R m) where
  toFun q := Finsupp.linearCombination R q
  invFun f a := f (Finsupp.single a 1)
  left_inv q := by
    funext a
    simp
  right_inv f := by
    apply Finsupp.lhom_ext
    intro a r
    simp only [Finsupp.linearCombination_single, smul_eq_mul]
    have h : Finsupp.single a r = r • Finsupp.single a (1 : R) := by simp
    rw [h, map_smul, smul_eq_mul]
  map_add' q r := by
    apply Finsupp.lhom_ext
    intro a c
    simp [mul_add]
  map_smul' r q := by
    apply Finsupp.lhom_ext
    intro a c
    simp [mul_left_comm]

/-- Multiplication by the variable `x_i` on ordinary coefficient vectors. -/
def multiplyCoordinate (m : ℕ) (i : σ) :
    PolynomialCoefficients σ R m →ₗ[R] PolynomialCoefficients σ R (m+1) :=
  Finsupp.lmapDomain R R (raiseCoordinate m i)

/-- Multiplication by `x_i` on the full-negative residue coefficients, after
projection onto the surviving full-negative exponents. -/
def multiplyResidueCoordinate (m : ℕ) (i : σ) :
    ResidueCoefficients σ R (m+1) →ₗ[R] ResidueCoefficients σ R m where
  toFun q a := q (raiseCoordinate m i a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The fundamental transpose identity holds coefficient by coefficient. -/
theorem pairing_multiplyCoordinate (m : ℕ) (i : σ)
    (p : PolynomialCoefficients σ R m) (q : ResidueCoefficients σ R (m+1)) :
    pairing (multiplyCoordinate m i p) q =
      pairing p (multiplyResidueCoordinate m i q) := by
  exact LinearMap.congr_fun (Finsupp.linearCombination_comp_lmapDomain R (v' := q) (raiseCoordinate m i)) p

/-- The coefficient vector interpreted as an actual multivariate polynomial. -/
def polynomialOfCoefficients (m : ℕ) :
    PolynomialCoefficients σ R m →ₗ[R] MvPolynomial σ R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap.comp
    (Finsupp.lmapDomain R R Subtype.val)

@[simp] theorem polynomialOfCoefficients_single (m : ℕ) (a : DegreeMonomial σ m) (r : R) :
    polynomialOfCoefficients m (Finsupp.single a r) = MvPolynomial.monomial a.val r := by
  change AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain Subtype.val (Finsupp.single a r)) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- Coefficient interpretation is injective, as the homogeneous exponent
subtype embeds into all monomial exponents. -/
theorem polynomialOfCoefficients_injective (m : ℕ) :
    Function.Injective (polynomialOfCoefficients (σ := σ) (R := R) m) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.injective.comp
    (Finsupp.mapDomain_injective Subtype.val_injective)

/-- The positive coefficient shift is genuine polynomial multiplication by `X i`. -/
theorem polynomialOfCoefficients_multiplyCoordinate (m : ℕ) (i : σ)
    (p : PolynomialCoefficients σ R m) :
    polynomialOfCoefficients (m+1) (multiplyCoordinate m i p) =
      MvPolynomial.X i * polynomialOfCoefficients m p := by
  have h : (polynomialOfCoefficients (σ := σ) (R := R) (m+1)).comp
      (multiplyCoordinate m i) =
      (LinearMap.mulLeft R (MvPolynomial.X i)).comp (polynomialOfCoefficients m) := by
    apply Finsupp.lhom_ext
    intro a r
    simp only [LinearMap.comp_apply, multiplyCoordinate, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, polynomialOfCoefficients_single]
    change MvPolynomial.monomial (a.val + Finsupp.single i 1) r =
      MvPolynomial.monomial (Finsupp.single i 1) 1 * MvPolynomial.monomial a.val r
    rw [MvPolynomial.monomial_mul_monomial, one_mul, add_comm]
  exact LinearMap.congr_fun h p

/-- Multiplication by a linear form on polynomial coefficients. -/
def multiplyLinearForm [Fintype σ] (m : ℕ) (L : σ → R) :
    PolynomialCoefficients σ R m →ₗ[R] PolynomialCoefficients σ R (m+1) :=
  ∑ i, L i • multiplyCoordinate m i

/-- The transposed linear-form map on negative Laurent coefficients. -/
def multiplyResidueLinearForm [Fintype σ] (m : ℕ) (L : σ → R) :
    ResidueCoefficients σ R (m+1) →ₗ[R] ResidueCoefficients σ R m :=
  ∑ i, L i • multiplyResidueCoordinate m i

/-- Linearity extends the variable identity to every linear form. -/
theorem pairing_multiplyLinearForm [Fintype σ] (m : ℕ) (L : σ → R)
    (p : PolynomialCoefficients σ R m) (q : ResidueCoefficients σ R (m+1)) :
    pairing (multiplyLinearForm m L p) q =
      pairing p (multiplyResidueLinearForm m L q) := by
  classical
  simp only [multiplyLinearForm, multiplyResidueLinearForm, LinearMap.sum_apply,
    LinearMap.smul_apply, pairing, map_sum, map_smul]
  change ∑ i, L i * pairing (multiplyCoordinate m i p) q =
    Finsupp.linearCombination R (∑ i, L i • multiplyResidueCoordinate m i q) p
  simp only [pairing_multiplyCoordinate]
  symm
  have hlin : Finsupp.linearCombination R (∑ i, L i • multiplyResidueCoordinate m i q) =
      ∑ i, L i • Finsupp.linearCombination R (multiplyResidueCoordinate m i q) := by
    change (coefficientDualEquiv (σ := σ) (R := R) m)
        (∑ i, L i • multiplyResidueCoordinate m i q) =
      ∑ i, L i • (coefficientDualEquiv (σ := σ) (R := R) m) (multiplyResidueCoordinate m i q)
    simp only [map_sum, map_smul]
  rw [hlin, LinearMap.sum_apply]
  rfl

end SteinerGeometry.ProjectiveResiduePairing
