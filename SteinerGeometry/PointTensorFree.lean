import SteinerGeometry.PointTensorUnit
import SteinerGeometry.PointTensorFunctor
import SteinerGeometry.AdditiveBiproductIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- Transport a line bundle along a genuine sheaf isomorphism. -/
def pointTensorLineOfIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    {I : X.Modules} (e : L.sheaf ≅ I) : Line.Bundles.LineBundle X where
  sheaf := I
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨d⟩⟩ := L.locallyTrivial x
    exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ d⟩⟩

theorem actualTensorLeft_additive_of_line {X : Scheme.{u}}
    (L : Line.Bundles.LineBundle X) {I : X.Modules} (e : L.sheaf ≅ I) :
    (actualTensorLeft I).Additive := by
  let J := pointTensorLineOfIso L e
  let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence J).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  exact Functor.additive_of_iso (actualLineTensorFunctorIso J)

/-- On a finite free module the ideal-times-module map is exactly the kernel
of the canonical restriction to the closed subscheme. -/
theorem pointTensorKernelMap_isIso_of_free {X Y : Scheme.{0}} (a : Y ⟶ X)
    [IsClosedImmersion a]
    (L : Line.Bundles.LineBundle X)
    (eL : L.sheaf ≅ OAI.MaximalSeshadri.IdealModule.closedModule a.ker)
    {E : X.Modules} {J : Type} [Fintype J] (eE : E ≅ SheafOfModules.free J) :
    IsIso (pointTensorKernelMap a E) := by
  let F := actualTensorLeft (OAI.MaximalSeshadri.IdealModule.closedModule a.ker)
  let G := pointEvaluationKernelFunctor a
  let η := pointTensorKernelTransformation a
  have : F.Additive := actualTensorLeft_additive_of_line L eL
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  have hf : IsIso (η.app (SheafOfModules.free J)) := by
    change IsIso (η.app (∐ fun _ : J => Line.Bundles.structureModule X))
    exact natTrans_isIso_finite_coproduct F G η _
      (fun _ => pointTensorKernelMap_unit_isIso a)
  have hn := η.naturality eE.hom
  have hi : IsIso (η.app E ≫ G.map eE.hom) := by
    rw [← hn]
    infer_instance
  exact (isIso_comp_right_iff (η.app E) (G.map eE.hom)).mp hi

end SteinerGeometry
