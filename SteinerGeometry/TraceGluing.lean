module

public import SteinerGeometry.LinearTrace
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleScalarTensorMap
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms

set_option backward.privateInPublic true
@[expose] public section

/-! Gluing the local scalar-extension trace. -/

noncomputable section

namespace SteinerGeometry.TraceGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open scoped TensorProduct

universe u v

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

abbrev pullPush := (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M)

local instance traceGluing_sectionAlgebra (U : X.Opens) : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

local instance traceGluing_pullPushSectionModule (U : X.Opens) :
    Module Γ(Y, f ⁻¹ᵁ U) Γ(pullPush f M, U) :=
  inferInstanceAs (Module Γ(Y, f ⁻¹ᵁ U) Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U))

local instance traceGluing_sectionTower (U : X.Opens) :
    IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ(pullPush f M, U) :=
  IsScalarTower.of_compHom _ _ _

local instance traceGluing_sectionComm (U : X.Opens) :
    SMulCommClass Γ(Y, f ⁻¹ᵁ U) Γ(X, U) Γ(pullPush f M, U) where
  smul_comm r a x := by
    change r • ((f.app U a) • x) = (f.app U a) • (r • x)
    exact smul_comm _ _ _

def unitSectionMap (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(pullPush f M, U) where
  toFun := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U
  map_add' := map_add _
  map_smul' := fun r x => ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul r x

/-- Canonical scalar extension on sections: `a ⊗ m ↦ a · η(m)`. -/
def sectionTensorMap (U : X.Opens) :
    Γ(Y, f ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(pullPush f M, U) :=
  CompatibleScalarTensorMap.compatibleScalarTensorMap
    (Algebra.lsmul Γ(X, U) Γ(X, U) Γ(pullPush f M, U)).toRingHom
    (fun _ _ => rfl)
    (unitSectionMap f M U)

@[simp] theorem sectionTensorMap_tmul (U : X.Opens)
    (a : Γ(Y, f ⁻¹ᵁ U)) (m : Γ(M, U)) :
    sectionTensorMap f M U (a ⊗ₜ[Γ(X, U)] m) =
      a • unitSectionMap f M U m := rfl

variable {ι : Type v} (B : ι → X.Opens)
variable (hb : ∀ i, Function.Bijective (sectionTensorMap f M (B i)))
variable (t : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶
    Line.Bundles.structureModule X)

def traceOnSections (U : X.Opens) : Γ(Y, f ⁻¹ᵁ U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun := t.app U
  map_add' := map_add _
  map_smul' := fun r x => t.app_smul r x

/-- The affine section trace, characterized without a choice of basis. -/
def sectionTrace (i : ι) : Γ(pullPush f M, B i) →ₗ[Γ(X, B i)] Γ(M, B i) :=
  (LinearTrace.tensorTrace (traceOnSections f t (B i))).comp
    (LinearEquiv.ofBijective (sectionTensorMap f M (B i)) (hb i)).symm.toLinearMap

theorem sectionTrace_tensor (i : ι) (z : Γ(Y, f ⁻¹ᵁ B i) ⊗[Γ(X, B i)] Γ(M, B i)) :
    sectionTrace f M B hb t i (sectionTensorMap f M (B i) z) =
      LinearTrace.tensorTrace (traceOnSections f t (B i)) z := by
  simp only [sectionTrace, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact congrArg (LinearTrace.tensorTrace (traceOnSections f t (B i)))
    ((LinearEquiv.ofBijective (sectionTensorMap f M (B i)) (hb i)).symm_apply_apply z)

theorem sectionTrace_pair (i : ι) (a : Γ(Y, f ⁻¹ᵁ B i)) (m : Γ(M, B i)) :
    sectionTrace f M B hb t i
      (a • unitSectionMap f M (B i) m) =
      traceOnSections f t (B i) a • m := by
  rw [← sectionTensorMap_tmul, sectionTrace_tensor, LinearTrace.tensorTrace_tmul]

set_option maxHeartbeats 2000000 in
theorem sectionTrace_natural (i j : ι) (h : B i ≤ B j) (s : Γ(pullPush f M, B j)) :
    sectionTrace f M B hb t i ((pullPush f M).presheaf.map (homOfLE h).op s) =
      M.presheaf.map (homOfLE h).op (sectionTrace f M B hb t j s) := by
  obtain ⟨z, rfl⟩ := (hb j).surjective s
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a m =>
    rw [sectionTensorMap_tmul]
    have hsmul (x : Γ(pullPush f M, B j)) :
        (pullPush f M).presheaf.map (homOfLE h).op (a • x) =
          Y.presheaf.map ((Opens.map f.base).map (homOfLE h)).op a •
            (pullPush f M).presheaf.map (homOfLE h).op x := by
      exact ((Scheme.Modules.pullback f).obj M).map_smul
        ((Opens.map f.base).map (homOfLE h)) a x
    have hη : (pullPush f M).presheaf.map (homOfLE h).op (unitSectionMap f M (B j) m) =
        unitSectionMap f M (B i) (M.presheaf.map (homOfLE h).op m) := by
      exact (ConcreteCategory.congr_hom
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
          (homOfLE h).op) m).symm
    rw [hsmul, hη, sectionTrace_pair, sectionTrace_pair, Scheme.Modules.map_smul]
    have ht := ConcreteCategory.congr_hom (t.mapPresheaf.naturality (homOfLE h).op) a
    exact congrArg (fun c => c • M.presheaf.map (homOfLE h).op m) ht

def traceBasisMap : Module.MapBasisExtension.ModuleBasisMap B (pullPush f M) M where
  app := sectionTrace f M B hb t
  naturality := sectionTrace_natural f M B hb t

variable (hB : Opens.IsBasis (Set.range B))

def trace : pullPush f M ⟶ M := (traceBasisMap f M B hb t).extend hB

theorem trace_retraction
    (ht : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ t = 𝟙 _) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      trace f M B hb t hB = 𝟙 M := by
  apply Module.BasisIsomorphisms.moduleMap_eq_of_basis B hB
  intro i
  apply ConcreteCategory.hom_ext
  intro m
  change (trace f M B hb t hB).app (B i)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app (B i) m) = m
  rw [trace, (traceBasisMap f M B hb t).extend_app]
  change sectionTrace f M B hb t i (unitSectionMap f M (B i) m) = m
  have he := sectionTrace_pair f M B hb t i (1 : Γ(Y, f ⁻¹ᵁ B i)) m
  rw [one_smul] at he
  have h1 : traceOnSections f t (B i) (1 : Γ(Y, f ⁻¹ᵁ B i)) = 1 := by
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun a : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X =>
        a.app (B i)) ht) (1 : Γ(X, B i))
    change traceOnSections f t (B i) ((f.app (B i)) (1 : Γ(X, B i))) = 1 at hh
    simpa only [map_one] using hh
  simpa only [h1, one_smul] using he

include B hb hB in
theorem pullbackUnit_splitMono
    (ht : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ t = 𝟙 _) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) :=
  ⟨⟨trace f M B hb t hB, trace_retraction f M B hb t hB ht⟩⟩

end SteinerGeometry.TraceGluing
