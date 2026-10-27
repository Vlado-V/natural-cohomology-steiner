module

public import SteinerGeometry.LinePushforwardLocallyFree

set_option backward.privateInPublic true
@[expose] public section

/-! # Finite type of a finite direct image -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- Finite direct image preserves finite type for quasicoherent modules.
The proof uses the actual scalar restriction on each affine open. -/
theorem finitePushforward_isFiniteType
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj M).IsFiniteType := by
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  apply OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_of_sections_module_finite
  intro U
  let V : Y.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have : Module.Finite Γ(Y, V.1) Γ(M, V.1) :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.app U.1).hom.toAlgebra
  let : Module Γ(X, U.1) Γ(M, V.1) :=
    Module.compHom Γ(M, V.1) (f.app U.1).hom
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(M, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite Γ(X, U.1) Γ(Y, V.1) := f.finite_app U.1 U.2
  change Module.Finite Γ(X, U.1) Γ(M, V.1)
  exact Module.Finite.trans Γ(Y, V.1) Γ(M, V.1)

/-- An actual line bundle has finite-type direct image under a finite map. -/
theorem linePushforward_isFiniteType
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (L : Line.Bundles.LineBundle Y) :
    ((Scheme.Modules.pushforward f).obj L.sheaf).IsFiniteType := by
  have := L.isQuasicoherent
  have := L.isFiniteType
  exact finitePushforward_isFiniteType f L.sheaf

end SteinerGeometry
