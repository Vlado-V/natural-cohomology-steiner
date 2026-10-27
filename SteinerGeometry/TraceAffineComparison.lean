module

public import SteinerGeometry.TraceGluing
public import SteinerGeometry.OpenBaseChangeSections
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackSectionValues
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.AdjunctionUnit
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange

set_option backward.privateInPublic true
@[expose] public section

/-! The canonical section scalar-extension map on affine charts. -/

noncomputable section
namespace SteinerGeometry.TraceAffineComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open scoped TensorProduct ChangeOfRings
attribute [local instance] RingHomInvPair.of_ringEquiv
set_option backward.isDefEq.respectTransparency false
universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

local instance topIsoInvPair (U : X.Opens) :
    RingHomInvPair U.topIso.commRingCatIsoToRingEquiv.toRingHom
      U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv U.topIso.commRingCatIsoToRingEquiv

local instance topIsoInvPairSymm (U : X.Opens) :
    RingHomInvPair U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom
      U.topIso.commRingCatIsoToRingEquiv.toRingHom :=
  RingHomInvPair.symm _ _

def restrictedSectionEquiv (U : X.Opens) :
    LinearEquiv U.topIso.commRingCatIsoToRingEquiv.toRingHom
      (σ' := U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom)
      Γ(M.restrict U.ι, ⊤) Γ(M, U) where
  __ := (Open.RestrictedSectionBases.moduleRestrictTopIso M U).addCommGroupIsoToAddEquiv
  map_smul' r x := Open.RestrictedSectionBases.moduleRestrictTopIso_smul M U r x

local instance openSectionAlgebra (U : X.Opens) :
    Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

local instance restrictedOpenSectionAlgebra (U : X.Opens) :
    Algebra Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
  (f ∣_ U).appTop.hom.toAlgebra

def restrictedScalarEquiv (U : X.Opens) :
    LinearEquiv U.topIso.commRingCatIsoToRingEquiv.toRingHom
      (σ' := U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom)
      Γ((f ⁻¹ᵁ U).toScheme, ⊤) Γ(Y, f ⁻¹ᵁ U) where
  __ := (f ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv.toAddEquiv
  map_smul' r s := by
    change (f ⁻¹ᵁ U).topIso.hom ((f ∣_ U).appTop r * s) =
      f.app U (U.topIso.hom r) * (f ⁻¹ᵁ U).topIso.hom s
    rw [map_mul]
    congr 1
    exact ConcreteCategory.congr_hom
      (Open.FunctionsBaseChange.morphismRestrict_appTop_topIso f U) r

def restrictedTensorEquiv (U : X.Opens) :
    LinearEquiv U.topIso.commRingCatIsoToRingEquiv.toRingHom
      (σ' := U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom)
      (Γ((f ⁻¹ᵁ U).toScheme, ⊤) ⊗[Γ(U.toScheme, ⊤)] Γ(M.restrict U.ι, ⊤))
      (Γ(Y, f ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) :=
  TensorProduct.congr
    (σ₂₁ := U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom)
    (restrictedScalarEquiv f U) (restrictedSectionEquiv M U)

def restrictedPullbackEquiv (U : X.Opens) :
    Γ((Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι), ⊤) ≃+
      Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  (((Affine.SectionAdjunction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U).toScheme).mapIso
    ((OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).app M)).toLinearEquiv.toAddEquiv).trans
      (Open.RestrictedSectionBases.moduleRestrictTopIso
        ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)).addCommGroupIsoToAddEquiv

theorem restrictedPullbackEquiv_smul (U : X.Opens)
    (a : Γ((f ⁻¹ᵁ U).toScheme, ⊤))
    (z : Γ((Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι), ⊤)) :
    restrictedPullbackEquiv f M U (a • z) =
      (f ⁻¹ᵁ U).topIso.hom a • restrictedPullbackEquiv f M U z := by
  let e := (Affine.SectionAdjunction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U).toScheme).mapIso
    ((OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).app M)
  change (Open.RestrictedSectionBases.moduleRestrictTopIso
      ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)).hom (e.hom.hom (a • z)) = _
  erw [e.hom.hom.map_smul]
  exact Open.RestrictedSectionBases.moduleRestrictTopIso_smul _ _ _ _

theorem restrictedPullbackEquiv_unit (U : X.Opens) (m : Γ(M.restrict U.ι, ⊤)) :
    restrictedPullbackEquiv f M U
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          (M.restrict U.ι)).app ⊤ m) =
      TraceGluing.unitSectionMap f M U (restrictedSectionEquiv M U m) := by
  have h := congrArg (fun φ => φ.app ⊤ m)
    (OpenPullback.AdjunctionUnit.OpenPullbackSquare.unit_square f U M)
  have h' := congrArg (fun z => (Open.RestrictedSectionBases.moduleRestrictTopIso
    ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)).hom z) h
  change (Open.RestrictedSectionBases.moduleRestrictTopIso
    ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)).hom
      (((OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app
        ((Scheme.Modules.pullback f).obj M)).app ⊤
        (((Scheme.Modules.restrictFunctor U.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).app ⊤ m)) =
    restrictedPullbackEquiv f M U
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          (M.restrict U.ι)).app ⊤ m) at h'
  rw [openBaseChangeMap_top_value] at h'
  erw [moduleRestrictTopIso_natural] at h'
  exact h'.symm

theorem sectionTensorMap_top_bijective [IsAffine X] [IsAffine Y] [M.IsQuasicoherent] :
    Function.Bijective (TraceGluing.sectionTensorMap f M ⊤) := by
  letI := f.appTop.hom.toAlgebra
  let e := Affine.GeometricSections.AffineGeometricSections.iso f M
  have h : (fun z => TraceGluing.sectionTensorMap f M ⊤ z) =
      (fun z => e.hom.hom z) := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      rw [TraceGluing.sectionTensorMap_tmul]
      erw [Affine.PullbackSectionValues.affinePullbackSections_tmul]
      rfl
    | add z w hz hw =>
      rw [map_add, hz, hw]
      exact (e.hom.hom.map_add z w).symm
  change Function.Bijective (fun z => TraceGluing.sectionTensorMap f M ⊤ z)
  rw [h]
  exact e.toLinearEquiv.bijective

theorem sectionTensorMap_affineOpen_bijective [IsAffineHom f] [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (TraceGluing.sectionTensorMap f M U) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let e := Affine.GeometricSections.AffineGeometricSections.iso (f ∣_ U) (M.restrict U.ι)
  have h (z) : restrictedPullbackEquiv f M U (e.hom.hom z) =
      TraceGluing.sectionTensorMap f M U (restrictedTensorEquiv f M U z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      rw [Affine.PullbackSectionValues.affinePullbackSections_tmul,
        restrictedPullbackEquiv_smul]
      erw [restrictedPullbackEquiv_unit]
      change _ = TraceGluing.sectionTensorMap f M U
        (TensorProduct.congr
          (σ₂₁ := U.topIso.commRingCatIsoToRingEquiv.symm.toRingHom)
          (restrictedScalarEquiv f U) (restrictedSectionEquiv M U) (a ⊗ₜ m))
      rw [TensorProduct.congr_tmul, TraceGluing.sectionTensorMap_tmul]
      rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  have hb := (restrictedPullbackEquiv f M U).bijective.comp e.toLinearEquiv.bijective
  change Function.Bijective (fun z => restrictedPullbackEquiv f M U (e.hom.hom z)) at hb
  have heq : (fun z => restrictedPullbackEquiv f M U (e.hom.hom z)) =
      (fun z => TraceGluing.sectionTensorMap f M U (restrictedTensorEquiv f M U z)) := funext h
  rw [heq] at hb
  exact (Function.Bijective.of_comp_iff (TraceGluing.sectionTensorMap f M U)
    (restrictedTensorEquiv f M U).bijective).mp hb

end SteinerGeometry.TraceAffineComparison
