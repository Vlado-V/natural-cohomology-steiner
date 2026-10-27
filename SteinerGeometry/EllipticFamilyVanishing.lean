module

public import SteinerGeometry.EllipticEulerCohomology
public import SteinerGeometry.CurveCohomologyFinite

set_option backward.privateInPublic true
@[expose] public section

/-! Uniform vanishing for the equal-degree line summands of the elliptic
construction. The zero-degree exception is one finite exclusion in the caller. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

theorem equal_euler_line_family_vanishing
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (J : Line.Bundles.LineBundle X) (hJ : 0 < χ p J.sheaf)
    (P : Line.Bundles.LineBundle X) (hP : χ p P.sheaf = 0)
    (hPne : ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule X))
    {ι : Type*} (L : ι → Line.Bundles.LineBundle X) (v : ℤ)
    (hL : ∀ i, χ p (L i).sheaf = v)
    (havoid : v = 0 → ∀ i,
      ¬ Nonempty ((L i).sheaf ≅ Line.Bundles.structureModule X)) :
    (∀ i, IsZero (H p (L i).sheaf 0)) ∨
      (∀ i, IsZero (H p (L i).sheaf 1)) := by
  rcases lt_trichotomy v 0 with hneg | hzero | hpos
  · left
    intro i
    apply negative_euler_difference_h0_zero p hd (L i)
    rw [hL i, hO]
    exact hneg
  · left
    intro i
    exact (zero_euler_nontrivial_cohomology p hd hO (L i)
      ((hL i).trans hzero) (havoid hzero i)).1
  · right
    intro i
    apply positive_euler_h1_zero_of_reference p hd hO J hJ P hP hPne (L i)
    rw [hL i]
    exact hpos

end SteinerGeometry
