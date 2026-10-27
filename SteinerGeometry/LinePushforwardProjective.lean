import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.AffineSectionsFlat
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! Finite-flat direct image of a line bundle: the affine section modules are
finite projective over a locally Noetherian base. -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace SteinerGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

theorem affineLinePushforward_sections_projective
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] (L : Line.Bundles.LineBundle Y) :
    Module.Finite Γ(X, ⊤) Γ((Scheme.Modules.pushforward f).obj L.sheaf, ⊤) ∧
      Module.Projective Γ(X, ⊤) Γ((Scheme.Modules.pushforward f).obj L.sheaf, ⊤) := by
  let R := Γ(X, ⊤)
  let S := Γ(Y, ⊤)
  let M := Γ(L.sheaf, ⊤)
  letI : Algebra R S := f.appTop.hom.toAlgebra
  letI : Module R M := Module.compHom M f.appTop.hom
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  haveI : Module.Finite R S := f.finite_appTop
  haveI : Module.Flat R S := f.flat_appTop
  haveI : Module.Finite S M := L.affine_sections_finite
  haveI : Module.Flat S M :=
    LineBundle.AffineSectionsFlat.lineBundle_affineOpen_sections_flat L
      ⟨⊤, isAffineOpen_top Y⟩
  haveI : Module.Finite R M := Module.Finite.trans S M
  haveI : Module.Flat R M := Module.Flat.trans R S M
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  change Module.Finite R M ∧ Module.Projective R M
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end SteinerGeometry
