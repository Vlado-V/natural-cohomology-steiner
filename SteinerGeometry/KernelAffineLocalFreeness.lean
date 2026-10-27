module

public import SteinerGeometry.KernelSheafSections
public import SteinerGeometry.AffineLocalFreeness
public import SteinerGeometry.SheafLocalFreeLocality
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

set_option backward.privateInPublic true
@[expose] public section

/-! Locally free kernels of actual epimorphisms on affine schemes. -/
noncomputable section
namespace SteinerGeometry.KernelAffineLocalFreeness
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

/-- An affine epimorphism onto a sheaf with projective sections has a
locally free kernel when its source has finite projective sections. -/
theorem locallyFree_kernel_of_affine_epi {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)]
    [Module.Projective Γ(X, ⊤) Γ(M, ⊤)]
    [Module.Projective Γ(X, ⊤) Γ(N, ⊤)] :
    (kernel f).IsLocallyFree := by
  have : (kernel f).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  have hs := Quasicoherent.Scheme.Modules.isQuasicoherent_surjective_of_epi f
  have : Module.Finite Γ(X, ⊤) Γ(kernel f, ⊤) :=
    KernelSheafSections.kernel_sections_finite f ⊤ hs
  have : Module.Projective Γ(X, ⊤) Γ(kernel f, ⊤) :=
    KernelSheafSections.kernel_sections_projective f ⊤ hs
  exact TildeFiniteProjective.locallyFree_of_affine_sections_projective X (kernel f)

/-- In particular, the kernel of an epimorphism between finite free sheaves
on an affine scheme is locally free. No local kernel frame is assumed. -/
theorem locallyFree_kernel_of_affine_free_epi {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (I J : Type u) [Finite I] [Finite J]
    (eM : M ≅ SheafOfModules.free I) (eN : N ≅ SheafOfModules.free J) :
    (kernel f).IsLocallyFree := by
  have := KernelSheafSections.sections_finite_of_freeIso M I eM
  have := KernelSheafSections.sections_projective_of_freeIso M I eM
  have := KernelSheafSections.sections_projective_of_freeIso N J eN
  exact locallyFree_kernel_of_affine_epi f


/-- An epimorphism between sheaves with finite free frames on an affine
open cover has a genuinely locally free kernel. -/
theorem locallyFree_kernel_of_affine_free_cover {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] {A : Type u} (U : A → X.Opens) (hU : iSup U = ⊤)
    (haff : ∀ a, IsAffine (U a).toScheme)
    (I J : Type u) [Finite I] [Finite J]
    (eM : ∀ a, (Scheme.Modules.restrictFunctor (U a).ι).obj M ≅ SheafOfModules.free I)
    (eN : ∀ a, (Scheme.Modules.restrictFunctor (U a).ι).obj N ≅ SheafOfModules.free J) :
    (kernel f).IsLocallyFree := by
  apply TildeFiniteProjective.locallyFree_of_openCover (kernel f) U hU
  intro a
  let F := Scheme.Modules.restrictFunctor (U a).ι
  let : F.Additive := { map_add := by intros; rfl }
  have : PreservesFiniteLimits F := KernelLocalFreeness.restrict_preservesFiniteLimits (U a).ι
  have : IsAffine (U a).toScheme := haff a
  have hK : (kernel (F.map f)).IsLocallyFree :=
    locallyFree_kernel_of_affine_free_epi (F.map f) I J (eM a) (eN a)
  have hR : (F.obj (kernel f)).IsLocallyFree :=
    TildeFiniteProjective.locallyFree_of_iso (PreservesKernel.iso F f).symm hK
  exact TildeFiniteProjective.locallyFree_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback (U a).ι).app (kernel f)) hR

end SteinerGeometry.KernelAffineLocalFreeness
