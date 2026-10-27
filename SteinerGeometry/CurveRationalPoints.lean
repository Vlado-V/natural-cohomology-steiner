import Mathlib.AlgebraicGeometry.AlgClosed.Basic

namespace SteinerGeometry

noncomputable section

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K] {C : Scheme}

/-- Genuine rational points compatible with the curve's structural map. -/
def CurveRationalPoint (p : C ⟶ Spec (.of K)) :=
  {a : Spec (.of K) ⟶ C // a ≫ p = 𝟙 _}

def CurveRationalPoint.underlying (p : C ⟶ Spec (.of K))
    (a : CurveRationalPoint p) : C := a.val (⊥ : PrimeSpectrum K)

/-- Over an algebraically closed field, different rational points of a
finite-type scheme have different underlying points. -/
theorem CurveRationalPoint.underlying_injective [IsAlgClosed K]
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p] :
    Function.Injective (CurveRationalPoint.underlying p) := by
  intro a b h
  apply Subtype.ext
  apply ext_of_apply_closedPoint_eq p a.property b.property
  change a.val (⊥ : PrimeSpectrum K) = b.val (⊥ : PrimeSpectrum K) at h
  convert h using 1 <;> congr 1 <;> exact Subsingleton.elim _ _

/-- A nonempty finite-type scheme over an algebraically closed field has a
rational point. -/
instance CurveRationalPoint.nonempty [IsAlgClosed K] [Nonempty C]
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p] : Nonempty (CurveRationalPoint p) := by
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set C).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨⟨pointOfClosedPoint p x hx, pointOfClosedPoint_comp p x hx⟩⟩

end
end SteinerGeometry
