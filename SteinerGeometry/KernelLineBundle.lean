import SteinerGeometry.KernelSectionRankOne
import SteinerGeometry.RationalFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RankOneLocalFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionFrameImage

/-! # The actual line bundle kernel of a rank-one-excess epimorphism -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.SheafCohomology.Projective
set_option backward.isDefEq.respectTransparency false

/-- An actual epimorphism locally framed as `O^(n+1) → O^n` has an actual
line-bundle kernel. No line-bundle conclusion is assumed in the inputs. -/
def kernelLineBundleOfAffineFreeNeighborhoods
    {X : Scheme} {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (n : ℕ)
    (hframes : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.free (Fin (n + 1))) ∧
      Nonempty (N.restrict U.ι ≅ SheafOfModules.free (Fin n))) :
    Line.Bundles.LineBundle X where
  sheaf := kernel f
  locallyTrivial x := by
    obtain ⟨U, hU, hx, ⟨eM⟩, ⟨eN⟩⟩ := hframes x
    let : IsAffine U.toScheme := hU
    let F := Scheme.Modules.restrictFunctor U.ι
    let : F.Additive := { map_add := by intros; rfl }
    let : PreservesFiniteLimits F := KernelLocalFreeness.restrict_preservesFiniteLimits U.ι
    let fU := F.map f
    have : (kernel fU).IsQuasicoherent :=
      Quasicoherent.Scheme.Modules.isQuasicoherent_kernel fU
    obtain ⟨hfin, hproj⟩ :=
      KernelSectionRankOne.kernel_sections_finite_projective fU
        (Fin (n + 1)) (Fin n) eM eN
    let := hfin
    let := hproj
    have hrank := KernelSectionRankOne.kernel_sections_rank_one fU n eM eN
    obtain ⟨V, hxV, ⟨eV⟩⟩ :=
      Affine.RankOneLocalFrames.affineRankOne_localFrames (kernel fU) hrank ⟨x, hx⟩
    let eK : (kernel f).restrict U.ι ≅ kernel fU := PreservesKernel.iso F f
    let e : (Scheme.Modules.pullback V.ι).obj ((kernel f).restrict U.ι) ≅
        Line.Bundles.structureModule V.toScheme :=
      (Scheme.Modules.pullback V.ι).mapIso eK ≪≫ eV
    exact ⟨U.ι ''ᵁ V, U.mem_ι_image_iff.mpr hxV,
      ⟨RestrictionFrameImage.restrictionFrameImage (kernel f) U V e⟩⟩

@[simp] theorem kernelLineBundleOfAffineFreeNeighborhoods_sheaf
    {X : Scheme} {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (n : ℕ)
    (hframes : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.free (Fin (n + 1))) ∧
      Nonempty (N.restrict U.ι ≅ SheafOfModules.free (Fin n))) :
    (kernelLineBundleOfAffineFreeNeighborhoods f n hframes).sheaf = kernel f := rfl

local instance kernelLineBundle_hasFiniteBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- On a finite-type scheme over an algebraically closed field, rank-`n`
frames at rational points suffice to construct the kernel line bundle. -/
def kernelLineBundleOfRationalFrames
    {K : Type} [Field K] [IsAlgClosed K] {C : Scheme}
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (N : C.Modules) [N.IsQuasicoherent] (n : ℕ)
    (f : (show C.Modules from SheafOfModules.free (Fin (n + 1))) ⟶ N) [Epi f]
    (hframes : ∀ a : CurveRationalPoint p, ∃ U : C.Opens,
      a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Line.Bundles.LineBundle C := by
  apply kernelLineBundleOfAffineFreeNeighborhoods f n
  intro x
  obtain ⟨U, hU, hx, ⟨eN⟩⟩ := affine_frame_at_of_rational_frames p N n hframes x
  refine ⟨U, hU, hx, ⟨?_⟩, ⟨eN⟩⟩
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    TildeFiniteProjective.pullbackFreeIso U.ι (Fin (n + 1))

@[simp] theorem kernelLineBundleOfRationalFrames_sheaf
    {K : Type} [Field K] [IsAlgClosed K] {C : Scheme}
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (N : C.Modules) [N.IsQuasicoherent] (n : ℕ)
    (f : (show C.Modules from SheafOfModules.free (Fin (n + 1))) ⟶ N) [Epi f]
    (hframes : ∀ a : CurveRationalPoint p, ∃ U : C.Opens,
      a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    (kernelLineBundleOfRationalFrames p N n f hframes).sheaf = kernel f := rfl

/-- The same actual kernel-line construction with the finite biproduct
presentation used by the evaluation map. -/
def kernelLineBundleOfRationalBiproductFrames
    {K : Type} [Field K] [IsAlgClosed K] {C : Scheme}
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (N : C.Modules) [N.IsQuasicoherent] (n : ℕ)
    (f : (show C.Modules from
      ⨁ fun _ : Fin (n + 1) => (SheafOfModules.unit C.ringCatSheaf : C.Modules)) ⟶ N) [Epi f]
    (hframes : ∀ a : CurveRationalPoint p, ∃ U : C.Opens,
      a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Line.Bundles.LineBundle C := by
  let eFree : (show C.Modules from
      ⨁ fun _ : Fin (n + 1) => (SheafOfModules.unit C.ringCatSheaf : C.Modules)) ≅
      (show C.Modules from SheafOfModules.free (Fin (n + 1))) :=
    biproduct.isoCoproduct (C := C.Modules) _
  have : (show C.Modules from
      ⨁ fun _ : Fin (n + 1) => (SheafOfModules.unit C.ringCatSheaf : C.Modules)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent C.ringCatSheaf).prop_of_iso eFree.symm inferInstance
  apply kernelLineBundleOfAffineFreeNeighborhoods f n
  intro x
  obtain ⟨U, hU, hx, ⟨eN⟩⟩ := affine_frame_at_of_rational_frames p N n hframes x
  refine ⟨U, hU, hx, ⟨?_⟩, ⟨eN⟩⟩
  exact (Scheme.Modules.restrictFunctor U.ι).mapIso eFree ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    TildeFiniteProjective.pullbackFreeIso U.ι (Fin (n + 1))

@[simp] theorem kernelLineBundleOfRationalBiproductFrames_sheaf
    {K : Type} [Field K] [IsAlgClosed K] {C : Scheme}
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (N : C.Modules) [N.IsQuasicoherent] (n : ℕ)
    (f : (show C.Modules from
      ⨁ fun _ : Fin (n + 1) => (SheafOfModules.unit C.ringCatSheaf : C.Modules)) ⟶ N) [Epi f]
    (hframes : ∀ a : CurveRationalPoint p, ∃ U : C.Opens,
      a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    (kernelLineBundleOfRationalBiproductFrames p N n f hframes).sheaf = kernel f := rfl

end SteinerGeometry
