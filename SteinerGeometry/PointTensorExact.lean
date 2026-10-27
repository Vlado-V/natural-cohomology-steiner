import SteinerGeometry.PointTensorFree
import SteinerGeometry.PointTensorRestriction
import SteinerGeometry.FiniteLocalFrames
import SteinerGeometry.ClosedImmersionUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

theorem pointTensorKernelMap_isIso_of_finiteFrames {X Y : Scheme.{0}}
    (a : Y ⟶ X) [IsClosedImmersion a]
    (L : Line.Bundles.LineBundle X)
    (eL : L.sheaf ≅ OAI.MaximalSeshadri.IdealModule.closedModule a.ker)
    (E : X.Modules) (D : TildeFiniteProjective.FiniteGeometricFrameCover E) :
    IsIso (pointTensorKernelMap a E) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨i, hi⟩ := (IsOpenCover.mk D.covers).exists_mem x
  let U := D.U i
  refine ⟨U, hi, ?_⟩
  have : Finite (D.Q i) := D.finite i
  let : Fintype (D.Q i) := Fintype.ofFinite _
  let J := L.pullback U.ι
  let eJ : J.sheaf ≅ OAI.MaximalSeshadri.IdealModule.closedModule (a ∣_ U).ker :=
    (Scheme.Modules.pullback U.ι).mapIso eL ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        (OAI.MaximalSeshadri.IdealModule.closedModule a.ker)).symm ≪≫
          pointIdealRestrictIso a U
  let eE : E.restrict U.ι ≅ SheafOfModules.free (D.Q i) :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ D.frame i
  have hl : IsIso (pointTensorKernelMap (a ∣_ U) (E.restrict U.ι)) :=
    pointTensorKernelMap_isIso_of_free (a ∣_ U) J eJ eE
  have hh : IsIso ((pointTensorSourceRestrictIso a U E).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map (pointTensorKernelMap a E) ≫
      (pointKernelRestrictIso a U E).hom) := by
    rw [pointTensorKernelMap_restrict]
    exact hl
  have hr : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (pointTensorKernelMap a E)) :=
    (isIso_comp_right_iff _ (pointKernelRestrictIso a U E).hom).mp
      ((isIso_comp_left_iff (pointTensorSourceRestrictIso a U E).hom _).mp hh)
  exact (Power.Nonvanishing.isIso_restrict_map_iff U.ι (pointTensorKernelMap a E)).mp hr

/-- The actual ideal-evaluation sequence for any finite locally free module. -/
theorem pointTensor_shortExact {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 p]
    (a : Spec (.of ℂ) ⟶ X) (ha : a ≫ p = 𝟙 _)
    (E : X.Modules) [E.IsQuasicoherent]
    (D : TildeFiniteProjective.FiniteGeometricFrameCover E) :
    (ShortComplex.mk (pointTensorInclusion a E)
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E)
      (pointTensorInclusion_unit_zero a E)).ShortExact := by
  let : IsClosedImmersion a := isClosedImmersion_of_comp_eq_id p a ha
  let L := rationalPointIdealLineBundle p a ha
  let h := pointTensorKernelMap_isIso_of_finiteFrames a L (Iso.refl _) E D
  let : IsIso (pointTensorKernelMap a E) := h
  let := ClosedImmersionUnit.pullbackUnit_epi a E
  let T := ShortComplex.mk
    (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E))
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E) (kernel.condition _)
  have hT : T.ShortExact := ⟨ShortComplex.exact_kernel _⟩
  let e : (ShortComplex.mk (pointTensorInclusion a E)
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E)
      (pointTensorInclusion_unit_zero a E)) ≅ T :=
    ShortComplex.isoMk (asIso (pointTensorKernelMap a E)) (Iso.refl _) (Iso.refl _)
      (by simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using pointTensorKernelMap_ι a E)
      (by simp [T])
  exact ShortComplex.shortExact_of_iso e.symm hT

end SteinerGeometry
