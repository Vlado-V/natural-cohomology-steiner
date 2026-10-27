module

public import SteinerGeometry.ProjectiveKernelRankFrames
public import SteinerGeometry.DualAffinePresentation
public import SteinerGeometry.SheafDualKernel

set_option backward.privateInPublic true
@[expose] public section

/-! The actual dual kernel bundle is the cokernel of the dual presentation. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.ProjectiveDualKernelExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveKernelBundle
universe u

variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The reversed actual sheaf dual of the canonical kernel sequence. -/
@[simps]
def dualKernelSequence {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    ShortComplex X.Modules :=
  ShortComplex.mk (SheafDual.dualMap f) (SheafDual.dualMap (kernel.ι f)) (by
    rw [← SheafDual.dualMap_comp, kernel.condition, SheafDual.dualMap_zero])

private theorem kernelSequence_shortExact {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Epi f] : (ShortComplex.kernelSequence f).ShortExact where
  exact := ShortComplex.kernelSequence_exact f
  mono_f := by dsimp [ShortComplex.kernelSequence]; infer_instance
  epi_g := by dsimp [ShortComplex.kernelSequence]; infer_instance

/-- Restriction of a functional to the actual kernel is surjective: the
original presentation splits on every standard affine chart. -/
theorem dual_kernelι_epi (n r t : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n r j d ⟶ lineSum R n t j e) [Epi f] :
    Epi (SheafDual.dualMap (kernel.ι f)) := by
  have hd (k : Fin r) := InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (d k))
  have he (k : Fin t) := InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (e k))
  have : (lineSum R n r j d).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ hd
  have : (lineSum R n t j e).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ he
  let U := StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+1))
  have hU : ∀ x : space R n, ∃ a, x ∈ U a :=
    (TopologicalSpace.IsOpenCover.mk
      (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))).exists_mem
  have : (ShortComplex.kernelSequence f).X₂.IsQuasicoherent :=
    inferInstanceAs ((lineSum R n r j d).IsQuasicoherent)
  have : (ShortComplex.kernelSequence f).X₃.IsQuasicoherent :=
    inferInstanceAs ((lineSum R n t j e).IsQuasicoherent)
  apply dualMap_epi_of_affine_presentation (ShortComplex.kernelSequence f)
    (kernelSequence_shortExact f) U hU
    (fun a => StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) a)
  intro a
  exact KernelSheafSections.sections_projective_of_freeIso _ (ULift.{u} (Fin t))
    (lineSumRestrictionFrame (R := R) n t a.down j e)

/-- The dual of an epimorphism between finite sums of projective twists gives
the actual short exact presentation of its dual kernel. -/
theorem dualKernelSequence_shortExact (n r t : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n r j d ⟶ lineSum R n t j e) [Epi f] :
    (dualKernelSequence f).ShortExact := by
  have hker := SheafDual.dualKernelOfCokernel (kernel.ι f) f (kernel.condition f)
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f))
  have := dual_kernelι_epi n r t j d e f
  exact
    { exact := (dualKernelSequence f).exact_of_f_is_kernel hker
      mono_f := mono_of_isLimit_fork hker
      epi_g := inferInstanceAs (Epi (SheafDual.dualMap (kernel.ι f))) }

/-- The restriction map to the dual kernel is the cokernel of the dual map. -/
def dualKernelSequence_isCokernel (n r t : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n r j d ⟶ lineSum R n t j e) [Epi f] :
    IsColimit (CokernelCofork.ofπ (SheafDual.dualMap (kernel.ι f))
      (dualKernelSequence f).zero) :=
  (dualKernelSequence_shortExact n r t j d e f).gIsCokernel

/-- The categorical cokernel of the dual map is canonically the dual of the
actual sheaf kernel. -/
def cokernelDualMapIso (n r t : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n r j d ⟶ lineSum R n t j e) [Epi f] :
    cokernel (SheafDual.dualMap f) ≅ SheafDual.dual (kernel f) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (dualKernelSequence_isCokernel n r t j d e f)

@[reassoc (attr := simp)]
theorem cokernel_π_cokernelDualMapIso_hom (n r t : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n r j d ⟶ lineSum R n t j e) [Epi f] :
    cokernel.π (SheafDual.dualMap f) ≫ (cokernelDualMapIso n r t j d e f).hom =
      SheafDual.dualMap (kernel.ι f) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (dualKernelSequence_isCokernel n r t j d e f) WalkingParallelPair.one

end SteinerGeometry.ProjectiveDualKernelExact
