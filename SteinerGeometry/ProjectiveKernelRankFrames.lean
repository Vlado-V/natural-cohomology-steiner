import SteinerGeometry.ProjectiveKernelBundle
import SteinerGeometry.PrescribedRankFrames
import SteinerGeometry.KernelSectionRank
import SteinerGeometry.FiniteDualFrames

/-! Kernels of finite sums of projective twists have the expected finite-rank frames. -/
noncomputable section
namespace SteinerGeometry.ProjectiveKernelRankFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveKernelBundle
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def kernelFiniteFrames (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f] :
    TildeFiniteProjective.FiniteGeometricFrameCover (kernel f) := by
  have hd (k : Fin (t+r)) := InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (d k))
  have he (k : Fin t) := InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (e k))
  have : (lineSum R n (t+r) j d).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ hd
  have : (lineSum R n t j e).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ he
  apply TildeFiniteProjective.finiteFramesOfOpenCover (kernel f)
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+1)))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
  intro a
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) a.down
  let F := Scheme.Modules.restrictFunctor U.ι
  let : F.Additive := { map_add := by intros; rfl }
  have : PreservesFiniteLimits F := KernelLocalFreeness.restrict_preservesFiniteLimits U.ι
  have : IsAffine U.toScheme :=
    MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen a.down
  let eM := lineSumRestrictionFrame (R := R) n (t+r) a.down j d
  let eN := lineSumRestrictionFrame (R := R) n t a.down j e
  have : (kernel (F.map f)).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_kernel (F.map f)
  obtain ⟨hfin,hproj⟩ := KernelSectionRankOne.kernel_sections_finite_projective (F.map f)
    (ULift.{u} (Fin (t+r))) (ULift.{u} (Fin t)) eM eN
  let := hfin
  let := hproj
  have hr : ∀ p : PrimeSpectrum Γ(U.toScheme,⊤),
      Module.rankAtStalk Γ(kernel (F.map f),⊤) p = r := by
    intro p
    have h := KernelSectionRank.kernel_sections_rank_add (F.map f)
      (ULift.{u} (Fin (t+r))) (ULift.{u} (Fin t)) eM eN p
    simp only [Nat.card_ulift, Nat.card_fin] at h
    omega
  let D := PrescribedRankFrames.affineFrameCover U.toScheme (kernel (F.map f)) r hr
  let ek : (Scheme.Modules.pullback U.ι).obj (kernel f) ≅ kernel (F.map f) :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (kernel f)).symm ≪≫
      PreservesKernel.iso F f
  exact D.mapIso ek.symm

theorem kernelFiniteFrames_index (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f]
    (i : (kernelFiniteFrames n r t j d e f).I) :
    (kernelFiniteFrames n r t j d e f).Q i = ULift.{u} (Fin r) := rfl

theorem kernel_frame_at (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f]
    (x : space R n) :
    ∃ U : (space R n).Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj (kernel f) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  let D := kernelFiniteFrames n r t j d e f
  obtain ⟨i,hi⟩ := (TopologicalSpace.IsOpenCover.mk D.covers).exists_mem x
  exact ⟨D.U i, hi, ⟨D.frame i⟩⟩

def dualKernelFiniteFrames (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f] :
    TildeFiniteProjective.FiniteGeometricFrameCover (SheafDual.dual (kernel f)) where
  I := (kernelFiniteFrames n r t j d e f).I
  U := (kernelFiniteFrames n r t j d e f).U
  covers := (kernelFiniteFrames n r t j d e f).covers
  Q _ := ULift.{u} (Fin r)
  frame i := FiniteDualFrames.dualFrame (kernel f)
    ((kernelFiniteFrames n r t j d e f).U i) r
    ((kernelFiniteFrames n r t j d e f).frame i)
  finite _ := inferInstance

theorem dual_kernel_frame_at (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f]
    (x : space R n) :
    ∃ U : (space R n).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (SheafDual.dual (kernel f)) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨U,hU,⟨eU⟩⟩ := kernel_frame_at n r t j d e f x
  exact ⟨U,hU,⟨FiniteDualFrames.dualFrame (kernel f) U r eU⟩⟩

theorem kernel_biproduct_frame_at (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f]
    (x : space R n) :
    ∃ U : (space R n).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (kernel f) ≅
        DualEvaluation.freeSheaf (X := U.toScheme) r) := by
  obtain ⟨U,hU,⟨eU⟩⟩ := kernel_frame_at n r t j d e f x
  exact ⟨U,hU,⟨eU ≪≫ FiniteDualFrames.freeToBiproduct U.toScheme r⟩⟩

theorem dual_kernel_biproduct_frame_at (n r t : ℕ) (j : Fin (n+1))
    (d : Fin (t+r) → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n (t+r) j d ⟶ lineSum R n t j e) [Epi f]
    (x : space R n) :
    ∃ U : (space R n).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (SheafDual.dual (kernel f)) ≅
        DualEvaluation.freeSheaf (X := U.toScheme) r) := by
  obtain ⟨U,hU,⟨eU⟩⟩ := dual_kernel_frame_at n r t j d e f x
  exact ⟨U,hU,⟨eU ≪≫ FiniteDualFrames.freeToBiproduct U.toScheme r⟩⟩

end SteinerGeometry.ProjectiveKernelRankFrames
