import SteinerGeometry.TraceAffineComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiniteFlatTrace

/-! A normalized finite-flat trace splits pullback for every quasicoherent sheaf. -/

noncomputable section
namespace SteinerGeometry.CanonicalTrace

open CategoryTheory AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u

theorem pullbackUnit_splitMono_of_structureTrace
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (t : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶
      Line.Bundles.structureModule X)
    (ht : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ t = 𝟙 _) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let B : X.affineOpens → X.Opens := Subtype.val
  have hb : ∀ i, Function.Bijective (TraceGluing.sectionTensorMap f M (B i)) :=
    fun i => TraceAffineComparison.sectionTensorMap_affineOpen_bijective f M i.val i.property
  have hB : Opens.IsBasis (Set.range B) := by
    simpa only [B, Subtype.range_val] using X.isBasis_affineOpens
  exact TraceGluing.pullbackUnit_splitMono f M B hb t hB ht

theorem pullbackUnit_splitMono_of_structureUnit_splitMono
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (h : IsSplitMono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  obtain ⟨⟨t, ht⟩⟩ := h
  exact pullbackUnit_splitMono_of_structureTrace f M t ht

theorem finiteFlat_pullbackUnit_splitMono
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ}
    (hn : ∀ x, f.finrank x = n) (v : Γ(X, ⊤)ˣ) (hv : (v : Γ(X, ⊤)) = n)
    (M : X.Modules) [M.IsQuasicoherent] :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) :=
  pullbackUnit_splitMono_of_structureUnit_splitMono f M
    (LocallyNoetherian.FiniteFlatTrace.locallyNoetherianFiniteFlat_structureUnit_splitMono
      f hn v hv)

end SteinerGeometry.CanonicalTrace
