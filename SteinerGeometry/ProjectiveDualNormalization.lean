module

public import SteinerGeometry.ProjectiveSteinerBundle
public import SteinerGeometry.DualModelComparison

set_option backward.privateInPublic true
@[expose] public section

/-! Canonical coordinate normalizations of the reversed dual linear presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ProjectiveDualNormalization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance normMonoidal (n : ℕ) : MonoidalCategory (projectiveSpace R n).Modules :=
  Monoidal.Scheme.Modules.monoidalCategory _
local instance normBiproducts (n : ℕ) : HasFiniteBiproducts (projectiveSpace R n).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Duality carries the finite coproduct to the coproduct of the actual duals. -/
def dualCoproductIso {X : Scheme.{u}} {s : ℕ} (M : Fin s → X.Modules) :
    SheafDual.dual (∐ M) ≅ ∐ (fun j => SheafDual.dual (M j)) := by
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  exact SheafDual.dualIso (biproduct.isoCoproduct M).symm ≪≫
    SheafDual.dualBiproductIso M ≪≫ biproduct.isoCoproduct _

/-- The dual of `O` is canonically `O`. -/
def zeroDualIso (n : ℕ) : SheafDual.dual (projectiveTwist R n 0) ≅ projectiveTwist R n 0 :=
  SheafDual.dualIso (TensorSections.monoidalUnitObjIso (projectiveSpace R n)) ≪≫
    InternalHomUnit.Construction.internalHomUnitIso (Line.Bundles.structureModule _) ≪≫
      (TensorSections.monoidalUnitObjIso (projectiveSpace R n)).symm

/-- The internal-Hom dual of the negative hyperplane line is the actual positive twist. -/
def minusOneDualIso (n : ℕ) :
    SheafDual.dual (projectiveTwist R n (-1)) ≅ projectiveTwist R n 1 := by
  let j : Fin (n+1) := 0
  let I := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  exact SheafDual.dualIso (λ_ I) ≪≫ SheafDual.nativeDualIso I ≪≫
    (λ_ (Dual.Scheme.Modules.dualObj I)).symm

/-- Canonical coordinates on the dual of a free sum. -/
def zeroSumDualIso (n s : ℕ) :
    SheafDual.dual (projectiveTwistSum R n s 0) ≅ projectiveTwistSum R n s 0 :=
  dualCoproductIso _ ≪≫ Sigma.mapIso (fun _ => zeroDualIso n)

/-- Canonical coordinates on the dual of a sum of negative hyperplane lines. -/
def minusOneSumDualIso (n s : ℕ) :
    SheafDual.dual (projectiveTwistSum R n s (-1)) ≅ projectiveTwistSum R n s 1 :=
  dualCoproductIso _ ≪≫ Sigma.mapIso (fun _ => minusOneDualIso n)

/-- The actual evaluation map associated to the literal negative presentation. -/
def evaluation {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) :
    projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1 :=
  (zeroSumDualIso n (t+r)).inv ≫ SheafDual.dualMap i ≫ (minusOneSumDualIso n t).hom

end SteinerGeometry.ProjectiveDualNormalization
