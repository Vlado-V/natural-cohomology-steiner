module

public import SteinerGeometry.KernelNaturality
public import OAI.AlgebraicGeometry.SheafCohomology.AffineH
public import OAI.AlgebraicGeometry.SheafCohomology.Module

set_option backward.privateInPublic true
@[expose] public section

/-! # Natural cohomology of actual scheme-module presentations
These wrappers map an actual short exact sequence of scheme modules through
the exact forgetful functor. All cohomology is the existing Ext-based
`AffineH.Projective.H`; no substitute cohomology theory is introduced.
-/

noncomputable section
namespace SteinerGeometry

open CategoryTheory AlgebraicGeometry

universe u
namespace SchemeModules

abbrev additiveSheaf (X : Scheme.{u}) :=
  OAI.AlgebraicGeometry.SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X

abbrev H {X : Scheme.{u}} (M : X.Modules) (q : ℕ) :=
  OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q

/-- The OAI Zariski cohomology group is definitionally Mathlib's sheaf Ext group. -/
theorem H_eq_sheafH {X : Scheme.{u}} (M : X.Modules) (q : ℕ) :
    H M q = Sheaf.H ((additiveSheaf X).obj M) q := rfl

/-- The OAI cohomology map is the actual map of the underlying sheaf cohomology. -/
theorem map_eq_sheafH_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (q : ℕ) :
    ((OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective.zariskiFunctor X q).map f).hom =
      Sheaf.H.map ((additiveSheaf X).map f) q := rfl

/-- Natural cohomology for a scheme module in the existing OAI model. -/
def HasNaturalCohomology {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ d : ℕ, ∀ q : ℕ, q ≠ d → Subsingleton (H M q)

variable {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

/-- The actual additive-sheaf forgetful functor preserves this short exact sequence. -/
theorem additiveSheaf_shortExact :
    ((additiveSheaf X).mapShortComplex.obj S).ShortExact :=
  hS.map_of_exact (additiveSheaf X)

/-- Nonnegative-twist criterion for the actual cokernel module. -/
theorem cokernel_natural_of_positive_vanishing
    (hA : ∀ q : ℕ, 0 < q → Subsingleton (H S.X₁ q))
    (hB : ∀ q : ℕ, 0 < q → Subsingleton (H S.X₂ q)) :
    HasNaturalCohomology S.X₃ := by
  exact SteinerGeometry.cokernel_natural_of_positive_vanishing
    (additiveSheaf_shortExact hS) hA hB

/-- Negative-twist criterion for an actual module presentation. The two
known terms have cohomology only in degree `n`; the top map has maximal rank. -/
theorem cokernel_natural_of_top_maximalRank (n : ℕ) (hn : 0 < n)
    (hA : ∀ q : ℕ, q ≠ n → Subsingleton (H S.X₁ q))
    (hB : ∀ q : ℕ, q ≠ n → Subsingleton (H S.X₂ q))
    (hmax : SteinerGeometry.HasMaximalRank
      ((OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective.zariskiFunctor X n).map S.f)) :
    HasNaturalCohomology S.X₃ := by
  exact SteinerGeometry.cokernel_natural_of_top_maximalRank
    (additiveSheaf_shortExact hS) n hn hA hB hmax

/-- Kernel criterion for an actual module presentation with maximal rank on H0. -/
theorem kernel_natural_of_degreeZero_maximalRank
    (hB : ∀ q : ℕ, 0 < q → Subsingleton (H S.X₂ q))
    (hC : ∀ q : ℕ, 0 < q → Subsingleton (H S.X₃ q))
    (hmax : SteinerGeometry.HasMaximalRank
      ((OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective.zariskiFunctor X 0).map S.g)) :
    HasNaturalCohomology S.X₁ := by
  exact SteinerGeometry.kernel_natural_of_degreeZero_maximalRank
    (additiveSheaf_shortExact hS) hB hC hmax

end SchemeModules
end SteinerGeometry
