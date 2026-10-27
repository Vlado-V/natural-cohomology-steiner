module

public import SteinerGeometry.CurveGenerators
public import SteinerGeometry.CurveOpenZero
public import SteinerGeometry.CurveAffineFiberVanishing
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {K : Type} [Field K]

/-- A finite-type quasicoherent module on a finite-type scheme over an
algebraically closed field is zero if its actual rational fibers are zero. -/
theorem isZero_of_rational_pullbacks [IsAlgClosed K]
    {C : Scheme} (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (M : C.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hz : ∀ a : CurveRationalPoint p, IsZero ((Scheme.Modules.pullback a.val).obj M)) : IsZero M := by
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  have hclosed (x : C) (hx : IsClosed ({x} : Set C)) :
      x ∈ Module.VanishingOpen.moduleVanishingOpen M := by
    let a : CurveRationalPoint p := ⟨pointOfClosedPoint p x hx, pointOfClosedPoint_comp p x hx⟩
    let U : C.Opens := (C.affineCover.f (C.affineCover.idx x)).opensRange
    have hxU : x ∈ U := C.affineCover.covers x
    let : IsAffine U.toScheme := isAffineOpen_opensRange _
    have haU : a.val (⊥ : PrimeSpectrum K) ∈ U := by
      simpa only [a, pointOfClosedPoint_apply] using hxU
    let b := pointInOpen a.val U haU
    let N := M.restrict U.ι
    let : N.IsFiniteType := Quasicoherent.RestrictionFiniteType.quasicoherent_openRestrict_finiteType U.ι M
    let I : (Scheme.Modules.pullback b).obj N ≅ (Scheme.Modules.pullback a.val).obj M :=
      (Scheme.Modules.pullback b).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
        (pullbackComp b U.ι).app M ≪≫
          (pullbackCongr (pointInOpen_fac a.val U haU)).app M
    have hb : IsZero ((Scheme.Modules.pullback b).obj N) := I.isZero_iff.mpr (hz a)
    obtain ⟨V, hbV, hV⟩ :=
      (Module.VanishingOpen.mem_moduleVanishingOpen N _).mp
        (affine_mem_vanishingOpen_of_pullback_isZero N b hb)
    apply (Module.VanishingOpen.mem_moduleVanishingOpen M x).mpr
    refine ⟨U.ι ''ᵁ V, ?_, restrict_image_isZero U.ι M V hV⟩
    refine ⟨b (⊥ : PrimeSpectrum K), hbV, ?_⟩
    have hp := congrArg (fun f : Spec (.of K) ⟶ C => f (⊥ : PrimeSpectrum K))
      (pointInOpen_fac a.val U haU)
    exact hp.trans (pointOfClosedPoint_apply p x hx _)
  apply (Module.VanishingOpen.moduleVanishingOpen_eq_top_iff M).mp
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show ((Module.VanishingOpen.moduleVanishingOpen M : Set C)ᶜ).Nonempty from ⟨x, hx⟩)
    (Module.VanishingOpen.moduleVanishingOpen M).isOpen.isClosed_compl.isLocallyClosed
  exact hy (hclosed y hyclosed)

end
end SteinerGeometry
