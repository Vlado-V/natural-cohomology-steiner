module

public import SteinerGeometry.RectangularRelativeKernel
public import SteinerGeometry.CyclicComplexBase
public import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
public import OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj
open OAI.RepresentationTheory.Theta.Geometric

abbrev ComplexAbelianVariety :=
  OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety

local instance rectangularVariety_integral (A : ComplexAbelianVariety) :
    IsIntegral A.toOver.left := A.variety.property
local instance rectangularVariety_smooth (A : ComplexAbelianVariety) :
    Smooth A.toOver.hom := A.variety.presentation.smooth

/-- A genuine algebraic model of the rectangular torus, with its group comparison retained. -/
structure RectangularModel (k : ℕ) [NeZero k] where
  variety : ComplexAbelianVariety
  comparison : (rectangularPeriodData k).periodTorus ≃ₘ⟮𝓘(ℂ, (rectangularPeriodData k).space),
      𝓘(ℂ, AlgebraicAction.AbelianModel variety)⟯
    OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints variety.toOver
  comparison_add : ∀ u v, comparison (u + v) = comparison u * comparison v

namespace RectangularModel

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

instance rectangularModel_integral : IsIntegral B.variety.toOver.left := B.variety.variety.property
instance rectangularModel_smooth : Smooth B.variety.toOver.hom := B.variety.variety.presentation.smooth

theorem dimension_one :
    OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension
      B.variety.toOver.hom = 1 := by
  calc
    _ = Module.finrank ℂ (rectangularPeriodData k).space :=
      AbelianScheme.abelian_model_dimension (rectangularPeriodData k) B.variety B.comparison
    _ = 1 := by change Module.finrank ℂ ℂ = 1; simp

/-- The native algebraic model is a one-dimensional abelian scheme. -/
def elliptic : EllipticScheme :=
  let A := AbelianScheme.abelianSchemeOfVariety B.variety
  { scheme := A.scheme
    group := A.group
    commutative := A.commutative
    proper := A.proper
    smoothDimension := by
      rw [← B.dimension_one]
      exact A.smoothDimension
    connected := A.connected }

instance rectangularModel_ellipticIntegral : IsIntegral B.elliptic.scheme.left := B.variety.variety.property

instance rectangularModel_pointsInfinite :
    Infinite (Over.mk (𝟙 complexBase) ⟶ B.elliptic.scheme) := by
  let : Infinite (rectangularPeriodData k).periodTorus :=
    inferInstanceAs (Infinite (RectangularTorus k))
  exact Infinite.of_injective B.comparison B.comparison.injective

def pointEquiv : Multiplicative (RectangularTorus k) ≃*
    (Over.mk (𝟙 complexBase) ⟶ B.elliptic.scheme) where
  toFun t := B.comparison t.toAdd
  invFun p := Multiplicative.ofAdd (B.comparison.symm p)
  left_inv t := B.comparison.symm_apply_apply t.toAdd
  right_inv p := B.comparison.apply_symm_apply p
  map_mul' u v := B.comparison_add u.toAdd v.toAdd

def projective :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      B.elliptic.scheme.left B.elliptic.scheme.hom :=
  B.variety.variety.presentation.projective

end RectangularModel

theorem exists_rectangularModel (k : ℕ) [NeZero k] : Nonempty (RectangularModel k) := by
  obtain ⟨A, e, he⟩ :=
    Torus.AbelianModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model_with_group
      (rectangularPeriodData k)
  exact ⟨⟨A, e, he⟩⟩

end
end SteinerGeometry
