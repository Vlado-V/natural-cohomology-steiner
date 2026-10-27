module

public import SteinerGeometry.CurveGenerators
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismQuasicoherentPullback
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GlobalSectionsDetectMaps

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {K : Type} [Field K] {C : Scheme}

/-- Spanning by the evaluated section values gives a genuine epimorphism on
the field point, by affine global sections. -/
theorem pullback_sectionFamily_epi_of_span
    (p : C ⟶ Spec (.of K)) {E : C.Modules} [E.IsQuasicoherent]
    {I : Type} (s : I → (SheafOfModules.unit C.ringCatSheaf ⟶ E))
    (a : Spec (.of K) ⟶ C) (ha : a ≫ p = 𝟙 _)
    (hs : Submodule.span K (Set.range (fun i =>
      sectionEvaluation p E a (Scheme.Modules.Hom.app (s i) ⊤ (1 : Γ(C, ⊤))))) = ⊤) :
    Epi ((Scheme.Modules.pullback a).map (Sigma.desc s)) := by
  let : IsClosedImmersion a := isClosedImmersion_of_comp_eq_id p a ha
  let : ((Scheme.Modules.pullback a).obj E).IsQuasicoherent :=
    Affine.MorphismQuasicoherentPullback.quasicoherent_pullback_of_isAffineHom a E
  let B : C.Modules := ∐ fun _ : I => SheafOfModules.unit C.ringCatSheaf
  let f : B ⟶ E := Sigma.desc s
  let L := ((sectionFunctor (a ≫ p)).map ((Scheme.Modules.pullback a).map f)).hom
  have himage (i : I) :
      sectionEvaluation p E a (Scheme.Modules.Hom.app (s i) ⊤ (1 : Γ(C, ⊤))) ∈ L.range := by
    let u : (sectionFunctor p).obj B :=
      Scheme.Modules.Hom.app (Sigma.ι (fun _ : I => SheafOfModules.unit C.ringCatSheaf) i)
        ⊤ (1 : Γ(C, ⊤))
    refine ⟨sectionEvaluation p B a u, ?_⟩
    have hv : (sectionFunctor p).map f u =
        Scheme.Modules.Hom.app (s i) ⊤ (1 : Γ(C, ⊤)) := by
      exact congrArg (fun g : SheafOfModules.unit C.ringCatSheaf ⟶ E =>
        Scheme.Modules.Hom.app g ⊤ (1 : Γ(C, ⊤)))
        (Sigma.ι_comp_desc s i)
    exact (sectionEvaluation_natural p f a u).symm.trans (congrArg (sectionEvaluation p E a) hv)
  have hrange : L.range = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact himage i)
  apply Affine.GlobalSectionsDetectMaps.module_epi_of_affine_globalSections_surjective
  have hsurj : Function.Surjective L := LinearMap.range_eq_top.mp hrange
  exact hsurj

end
end SteinerGeometry
