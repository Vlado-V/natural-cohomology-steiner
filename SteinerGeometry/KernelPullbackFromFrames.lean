import SteinerGeometry.LocallySplitPullbackKernel
import SteinerGeometry.AffineFreeSplit

/-! Canonical kernel base change from actual affine local frames. -/
noncomputable section
namespace SteinerGeometry.KernelPullbackFromFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

/-- An epimorphism with a finite free target on each affine chart has its
actual kernel preserved by arbitrary geometric pullback. -/
theorem kernelComparison_isIso_of_epi_affine_target_frames
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (e : M ⟶ N) [Epi e]
    {I : Type u} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (haff : ∀ i, IsAffine (U i).toScheme) (J : I → Type u) (hJ : ∀ i, Finite (J i))
    (eN : ∀ i, (Scheme.Modules.pullback (U i).ι).obj N ≅ SheafOfModules.free (J i)) :
    IsIso (kernelComparison e (Scheme.Modules.pullback f)) :=
  LocallySplitPullbackKernel.kernelComparison_isIso_of_locallySplit f e U hcover
    (SteinerGeometry.locallySplit_of_epi_free_affine_cover e U haff J hJ eN)

/-- Restriction-frame form, convenient for finite sums of line bundles. -/
theorem kernelComparison_isIso_of_epi_affine_restriction_frames
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (e : M ⟶ N) [Epi e]
    {I : Type u} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (haff : ∀ i, IsAffine (U i).toScheme) (J : I → Type u) (hJ : ∀ i, Finite (J i))
    (eN : ∀ i, N.restrict (U i).ι ≅ SheafOfModules.free (J i)) :
    IsIso (kernelComparison e (Scheme.Modules.pullback f)) :=
  LocallySplitPullbackKernel.kernelComparison_isIso_of_locallySplit f e U hcover
    (SteinerGeometry.locallySplit_of_epi_free_affine_restrict e U haff J hJ eN)

end SteinerGeometry.KernelPullbackFromFrames
