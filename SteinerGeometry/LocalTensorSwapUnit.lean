module

public import SteinerGeometry.TensorSwapUnitIso
public import SteinerGeometry.LocalTensorLeftUnitor
public import SteinerGeometry.LocalTensorCoherence

set_option backward.privateInPublic true
@[expose] public section

/-! Removing a local unit before exchanging the two tensor factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.LocalTensorSwapUnit
open CategoryTheory AlgebraicGeometry MonoidalCategory Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI
local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

/-- The unitor removes a local unit inside a second tensor product. -/
theorem tensor_leftUnitor_tensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (x : Γ(M,U)) (y : Γ(N,U)) :
    (((λ_ M).hom ⊗ₘ 𝟙 N).val.app (op U))
      (TensorSections.tensorSection (𝟙_ X.Modules ⊗ M) N U
        (TensorSections.tensorSection (𝟙_ X.Modules) M U
          (PowerCancellationPairing.localMonoidalUnitSection X U) x) y) =
      TensorSections.tensorSection M N U x y := by
  rw [TensorFrameSections.tensorSection_map,
    LocalTensorLeftUnitor.leftUnitor_tensorSection]
  rfl

/-- The canonical unit-removal and braiding send the local pair to the reversed pair. -/
theorem braiding_leftUnitor_tensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (x : Γ(M,U)) (y : Γ(N,U)) :
    (β_ M N).hom.val.app (op U)
      ((((λ_ M).hom ⊗ₘ 𝟙 N).val.app (op U))
        (TensorSections.tensorSection (𝟙_ X.Modules ⊗ M) N U
          (TensorSections.tensorSection (𝟙_ X.Modules) M U
            (PowerCancellationPairing.localMonoidalUnitSection X U) x) y)) =
      TensorSections.tensorSection N M U y x := by
  rw [tensor_leftUnitor_tensorSection,
    LocalTensorCoherence.braiding_tensorSection]

/-- The shared named isomorphism has the same local pure-tensor formula. -/
theorem iso_tensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (x : Γ(M,U)) (y : Γ(N,U)) :
    (TensorSwapUnitIso.iso M N).hom.val.app (op U)
      (TensorSections.tensorSection (𝟙_ X.Modules ⊗ M) N U
        (TensorSections.tensorSection (𝟙_ X.Modules) M U
          (PowerCancellationPairing.localMonoidalUnitSection X U) x) y) =
      TensorSections.tensorSection N M U y x := by
  change (β_ M N).hom.val.app (op U)
    ((((λ_ M).hom ⊗ₘ 𝟙 N).val.app (op U))
      (TensorSections.tensorSection (𝟙_ X.Modules ⊗ M) N U
        (TensorSections.tensorSection (𝟙_ X.Modules) M U
          (PowerCancellationPairing.localMonoidalUnitSection X U) x) y)) = _
  exact braiding_leftUnitor_tensorSection M N U x y

end SteinerGeometry.LocalTensorSwapUnit
