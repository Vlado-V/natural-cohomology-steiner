module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- A restriction vanishing on an open of an open subscheme vanishes on the
same open viewed inside the ambient scheme. -/
theorem restrict_image_isZero {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (V : X.Opens)
    (h : IsZero ((M.restrict f).restrict V.ι)) :
    IsZero (M.restrict (f ''ᵁ V).ι) := by
  let e := f.isoImage V
  let T := M.restrict (f ''ᵁ V).ι
  let H : T.restrict e.hom ≅ (M.restrict f).restrict V.ι :=
    ((restrictFunctorComp e.hom (f ''ᵁ V).ι).symm.app M) ≪≫
      ((restrictFunctorCongr (f.isoImage_hom_ι V)).app M) ≪≫
        ((restrictFunctorComp V.ι f).app M)
  have hz : IsZero (T.restrict e.hom) := H.isZero_iff.mpr h
  let J := LineBundle.IsoImage.restrictFunctorInverseIso e.symm
  exact (J.app T).isZero_iff.mp ((restrictFunctor e.inv).map_isZero hz)

end
end SteinerGeometry
