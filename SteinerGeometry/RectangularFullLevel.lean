import SteinerGeometry.RectangularSelfCover
import SteinerGeometry.GeometricKernelFunctor

/-! A full level-two structure obtained from the four actual half-periods. -/
noncomputable section
namespace SteinerGeometry.RectangularModel
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

def binaryCoordinateEquiv : (Fin 2 → ZMod 2) ≃+ (ZMod 2 × ZMod 2) where
  toEquiv := finTwoArrowEquiv (ZMod 2)
  map_add' _ _ := rfl

def fullLevelTwo : B.elliptic.FullLevel 2 := by
  let e := Classical.choice B.doubling_kernel_points
  let labels := (AddEquiv.toMultiplicative binaryCoordinateEquiv).trans e
  exact kernelFunctorIso_of_points B.doubling labels ≪≫
    kernelTorsionFunctorIso B.elliptic B.doubling 2 rfl

end SteinerGeometry.RectangularModel
