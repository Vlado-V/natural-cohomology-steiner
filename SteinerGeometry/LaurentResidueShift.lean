module

public import SteinerGeometry.LaurentMultiplication
public import SteinerGeometry.ProjectiveResiduePairing

set_option backward.privateInPublic true
@[expose] public section

/-! # Coordinate shifts in full-negative Laurent residues

The coefficient formula is proved on the actual homogeneous Laurent Čech
factor. Complementary exponent reindexing then identifies it with the
transpose of polynomial coordinate multiplication. -/
noncomputable section
namespace SteinerGeometry.LaurentResidueShift

open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open LaurentMultiplication ProjectiveResiduePairing

universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

/-- The unique possible predecessor of an exponent after multiplication by
a coordinate. -/
def lowerWeight (d : ℤ) (j : σ) (e : Weight (σ := σ) (d + 1)) : Weight (σ := σ) d :=
  ⟨e.val - Finsupp.single j 1, by simp [e.property]⟩

omit [LinearOrder σ] in
@[simp] theorem shiftWeight_lowerWeight (d : ℤ) (j : σ)
    (e : Weight (σ := σ) (d + 1)) :
    shiftWeight d j (lowerWeight d j e) = e := by
  apply Subtype.ext
  simp [shiftWeight, lowerWeight]

/-- On the full coordinate intersection every homogeneous weight is allowed. -/
def allowedOfSurjective {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) {d : ℤ} (e : Weight (σ := σ) d) : Allowed a d :=
  ⟨e, fun i _ => ha i⟩

def lowerAllowed {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (d : ℤ) (j : σ) (e : Allowed a (d + 1)) :
    Allowed a d := allowedOfSurjective a ha (lowerWeight d j e.val)

@[simp] theorem shiftAllowed_lowerAllowed {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (d : ℤ) (j : σ) (e : Allowed a (d + 1)) :
    shiftAllowed a d j (lowerAllowed a ha d j e) = e := by
  apply Subtype.ext
  exact shiftWeight_lowerWeight d j e.val

/-- Exact coefficient extraction on the genuine Laurent factor: the target
coefficient is the coefficient at its unique predecessor. -/
theorem shiftFactor_coeff_predecessor {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (d : ℤ) (j : σ)
    (x : AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d))
    (e : Allowed a (d + 1)) :
    (shiftFactor (R := R) a d j x).coeff e =
      x.coeff (lowerAllowed a ha d j e) := by
  simpa only [shiftAllowed_lowerAllowed] using
    (shiftFactor_coeff_shifted a d j x (lowerAllowed a ha d j e))

section Complementary
variable [Fintype σ]

/-- The complementary exponent of a homogeneous polynomial monomial, at
an explicitly identified Laurent degree. -/
def complementaryWeight (m : ℕ) (d : ℤ)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ)) (a : DegreeMonomial σ m) :
    Weight (σ := σ) d :=
  ⟨Finsupp.equivFunOnFinite.symm (negativeExponent a), by
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, negativeExponent]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Nat.cast_sum,
      ← Finsupp.degree_eq_sum, a.property]
    simpa using hd.symm⟩

omit [LinearOrder σ] in
@[simp] theorem complementaryWeight_apply (m : ℕ) (d : ℤ)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ)) (a : DegreeMonomial σ m) (i : σ) :
    (complementaryWeight m d hd a).val i = negativeExponent a i := by
  simp [complementaryWeight]

omit [LinearOrder σ] in
theorem lowerWeight_complementary (m : ℕ) (d : ℤ) (j : σ)
    (hsource : d = -((m + 1 : ℕ) : ℤ) - (Fintype.card σ : ℤ))
    (htarget : d + 1 = -(m : ℤ) - (Fintype.card σ : ℤ))
    (a : DegreeMonomial σ m) :
    lowerWeight d j (complementaryWeight m (d + 1) htarget a) =
      complementaryWeight (m + 1) d hsource (raiseCoordinate m j a) := by
  apply Subtype.ext
  ext i
  change (complementaryWeight m (d + 1) htarget a).val i -
      (Finsupp.single j (1 : ℤ)) i = _
  simp only [complementaryWeight_apply]
  exact (eq_sub_iff_add_eq.mpr (negativeExponent_raiseCoordinate m j i a)).symm

/-- Read full-negative coefficients using complementary ordinary monomials. -/
def residueCoefficients {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (m : ℕ) (d : ℤ)
    (hd : d = -(m : ℤ) - (Fintype.card σ : ℤ))
    (x : AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d)) :
    ResidueCoefficients σ Γ(Spec (.of R), ⊤) m :=
  fun e => x.coeff (allowedOfSurjective a ha (complementaryWeight m d hd e))

/-- On the actual Laurent Čech factor, coordinate multiplication followed
by full-negative coefficient extraction is the residue transpose map. -/
theorem residueCoefficients_shiftFactor {q : ℕ} (a : Fin (q + 1) → σ)
    (ha : Function.Surjective a) (m : ℕ) (d : ℤ) (j : σ)
    (hsource : d = -((m + 1 : ℕ) : ℤ) - (Fintype.card σ : ℤ))
    (htarget : d + 1 = -(m : ℤ) - (Fintype.card σ : ℤ))
    (x : AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed a d)) :
    residueCoefficients a ha m (d + 1) htarget (shiftFactor (R := R) a d j x) =
      multiplyResidueCoordinate m j (residueCoefficients a ha (m + 1) d hsource x) := by
  funext e
  rw [residueCoefficients, shiftFactor_coeff_predecessor a ha d j]
  change x.coeff (lowerAllowed a ha d j
      (allowedOfSurjective a ha (complementaryWeight m (d + 1) htarget e))) =
    x.coeff (allowedOfSurjective a ha
      (complementaryWeight (m + 1) d hsource (raiseCoordinate m j e)))
  congr 1
  apply Subtype.ext
  exact lowerWeight_complementary m d j hsource htarget e

end Complementary
end SteinerGeometry.LaurentResidueShift
