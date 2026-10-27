module

public import SteinerGeometry.KernelLocalFreeness
public import SteinerGeometry.SplitKernelFunctor
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary geometric pullback preserves kernels of locally split epimorphisms. -/
noncomputable section
namespace SteinerGeometry.LocallySplitPullbackKernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

local instance locallySplitPullbackKernelPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

local instance locallySplitPullbackKernelRestrictAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).Additive := { map_add := by intros; rfl }

theorem openPullback_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (Scheme.Modules.pullback U.ι) := by
  have := KernelLocalFreeness.restrict_preservesFiniteLimits U.ι
  exact preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback U.ι)

/-- Pullback and restriction to corresponding opens form the actual
commuting functor square needed for the local argument. -/
def openSquare {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm

/-- The canonical kernel comparison is an isomorphism whenever the original
map splits on an open cover. There is no flatness hypothesis on the pullback. -/
theorem kernelComparison_isIso_of_locallySplit {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (e : M ⟶ N) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤)
    (hsplit : ∀ i, IsSplitEpi ((Scheme.Modules.pullback (U i).ι).map e)) :
    IsIso (kernelComparison e (Scheme.Modules.pullback f)) := by
  let F := Scheme.Modules.pullback f
  let V : I → Y.Opens := fun i => f ⁻¹ᵁ U i
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := (IsOpenCover.mk hU).exists_mem (f y)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  apply Invertible.Scheme.Modules.isIso_of_isIso_restrict
    (kernelComparison e F) V hV
  intro i
  let G := Scheme.Modules.restrictFunctor (V i).ι
  let R := Scheme.Modules.pullback (U i).ι
  let T := Scheme.Modules.pullback (f ∣_ U i)
  have : PreservesFiniteLimits G := KernelLocalFreeness.restrict_preservesFiniteLimits (V i).ι
  have : PreservesFiniteLimits R := openPullback_preservesFiniteLimits (U i)
  have : IsSplitEpi (R.map e) := hsplit i
  have : IsIso (kernelComparison (R.map e) T) :=
    SplitKernelFunctor.kernelComparison_isIso (R.map e) T
  have hRT : IsIso (kernelComparison e (R ⋙ T)) := by
    have hcomp := SplitKernelFunctor.kernelComparison_comp e R T
    have : IsIso (T.map (kernelComparison e R) ≫ kernelComparison (R.map e) T) :=
      inferInstance
    rwa [hcomp] at this
  have : IsIso (kernelComparison e (R ⋙ T)) := hRT
  have : PreservesLimit (parallelPair e 0) (R ⋙ T) :=
    PreservesKernel.of_iso_comparison (R ⋙ T) e
  have : PreservesLimit (parallelPair e 0) (F ⋙ G) :=
    preservesLimit_of_natIso (parallelPair e 0) (openSquare f (U i)).symm
  exact SplitKernelFunctor.map_kernelComparison_isIso e F G

/-- The resulting isomorphism uses the canonical comparison, so its
composition with the kernel inclusion is the pulled-back inclusion. -/
def kernelIso_of_locallySplit {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (e : M ⟶ N) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤)
    (hsplit : ∀ i, IsSplitEpi ((Scheme.Modules.pullback (U i).ι).map e)) :
    (Scheme.Modules.pullback f).obj (kernel e) ≅ kernel ((Scheme.Modules.pullback f).map e) := by
  have := kernelComparison_isIso_of_locallySplit f e U hU hsplit
  exact asIso (kernelComparison e (Scheme.Modules.pullback f))


@[reassoc (attr := simp)]
theorem kernelIso_hom_ι {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (e : M ⟶ N) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤)
    (hsplit : ∀ i, IsSplitEpi ((Scheme.Modules.pullback (U i).ι).map e)) :
    (kernelIso_of_locallySplit f e U hU hsplit).hom ≫
        kernel.ι ((Scheme.Modules.pullback f).map e) =
      (Scheme.Modules.pullback f).map (kernel.ι e) :=
  kernelComparison_comp_ι e (Scheme.Modules.pullback f)

end SteinerGeometry.LocallySplitPullbackKernel
