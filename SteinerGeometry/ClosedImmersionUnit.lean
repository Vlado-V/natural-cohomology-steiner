module

public import SteinerGeometry.TraceAffineComparison
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.ClosedImmersionUnit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open scoped TensorProduct
universe u

local instance closedImmersionUnit_pullPushSectionModule {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    Module Γ(Y, f ⁻¹ᵁ U) Γ(TraceGluing.pullPush f M, U) :=
  inferInstanceAs (Module Γ(Y, f ⁻¹ᵁ U)
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U))

/-- On an affine open, the actual closed-immersion pullback unit is surjective. -/
theorem unitSectionMap_surjective
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (TraceGluing.unitSectionMap f M U) := by
  intro z
  obtain ⟨w, hw⟩ :=
    (TraceAffineComparison.sectionTensorMap_affineOpen_bijective f M U hU).surjective z
  suffices h : ∀ w, ∃ m, TraceGluing.unitSectionMap f M U m =
      TraceGluing.sectionTensorMap f M U w by
    obtain ⟨m, hm⟩ := h w
    exact ⟨m, hm.trans hw⟩
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul a m =>
    obtain ⟨r, hr⟩ := f.app_surjective U hU a
    refine ⟨r • m, ?_⟩
    rw [map_smul, TraceGluing.sectionTensorMap_tmul]
    change f.app U r • TraceGluing.unitSectionMap f M U m = _
    rw [hr]
    rfl
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [map_add, map_add, hm, hn]⟩

/-- Restriction to a closed subscheme is an epimorphism on any quasicoherent module. -/
theorem pullbackUnit_epi
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  constructor
  intro N g h heq
  apply Module.BasisIsomorphisms.moduleMap_eq_of_basis
    (fun U : X.affineOpens => (U : X.Opens))
    (by simpa only [Subtype.range_val] using X.isBasis_affineOpens)
  intro U
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨m, hm⟩ := unitSectionMap_surjective f M U U.property z
  have hc := congrArg (fun k => k.app U m) heq
  change g.app U (TraceGluing.unitSectionMap f M U m) =
    h.app U (TraceGluing.unitSectionMap f M U m) at hc
  simpa only [hm] using hc

end SteinerGeometry.ClosedImmersionUnit
