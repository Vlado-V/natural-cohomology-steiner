import SteinerGeometry.ProjectiveDualNormalization
import SteinerGeometry.ProjectiveBidual
import SteinerGeometry.CokernelCohomology

/-! The actual fixed Steiner cokernel is the dual of its actual evaluation kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ProjectiveSteinerPresentation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveSteinerBundle ProjectiveDualNormalization
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Canonical bidual coordinates at the negative endpoint. -/
def sourceBidualIso (n t : ℕ) :
    projectiveTwistSum R n t (-1) ≅ SheafDual.dual (projectiveTwistSum R n t 1) :=
  ProjectiveBidual.lineSumBidualIso n t (0 : Fin (n+1)) (fun _ => -1) ≪≫
    SheafDual.dualIso (minusOneSumDualIso n t)

/-- Canonical bidual coordinates at the free endpoint. -/
def targetBidualIso (n m : ℕ) :
    projectiveTwistSum R n m 0 ≅ SheafDual.dual (projectiveTwistSum R n m 0) :=
  ProjectiveBidual.lineSumBidualIso n m (0 : Fin (n+1)) (fun _ => 0) ≪≫
    SheafDual.dualIso (zeroSumDualIso n m)

/-- The double transpose of the one original map is the original map under
natural bidual evaluation, not an independently chosen linear presentation. -/
theorem presentation_dual_evaluation {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) :
    i ≫ (targetBidualIso n (t+r)).hom =
      (sourceBidualIso n t).hom ≫ SheafDual.dualMap (evaluation i) := by
  simp only [sourceBidualIso, targetBidualIso, Iso.trans_hom,
    ProjectiveBidual.lineSumBidualIso_hom, SheafDual.dualIso, ProjectiveDualNormalization.evaluation,
    SheafDual.dualMap_comp, Category.assoc]
  rw [← Category.assoc (SheafDual.dualMap (minusOneSumDualIso n t).inv),
    ← SheafDual.dualMap_comp, Iso.hom_inv_id, SheafDual.dualMap_id, Category.id_comp]
  rw [← SheafDual.bidualEvaluation_naturality_assoc]

/-- An epimorphic evaluation makes the original negative presentation monic. -/
theorem presentation_mono {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)] : Mono i := by
  have hs := ProjectiveDualKernelExact.dualKernelSequence_shortExact n (t+r) t
    (0 : Fin (n+1)) (fun _ => 0) (fun _ => 1) (evaluation i)
  let : Mono (SheafDual.dualMap (evaluation i)) := hs.mono_f
  exact mono_of_mono_fac (presentation_dual_evaluation i)

/-- The fixed cokernel is canonically the dual of the kernel of its actual evaluation. -/
def bundleKernelDualIso {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)] : bundle i ≅ SheafDual.dual (kernel (evaluation i)) :=
  cokernel.mapIso _ _ (sourceBidualIso n t) (targetBidualIso n (t+r))
    (presentation_dual_evaluation i) ≪≫
  ProjectiveDualKernelExact.cokernelDualMapIso n (t+r) t (0 : Fin (n+1))
    (fun _ => 0) (fun _ => 1) (evaluation i)

/-- This one fixed cokernel is a bundle of the prescribed rank. -/
def bundleFiniteFrames {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)] : TildeFiniteProjective.FiniteGeometricFrameCover (bundle i) :=
  (ProjectiveKernelRankFrames.dualKernelFiniteFrames n r t (0 : Fin (n+1))
    (fun _ => 0) (fun _ => 1) (evaluation i)).mapIso (bundleKernelDualIso i).symm

/-- All tensor twists of the same cokernel carry their actual short exact Steiner sequence. -/
theorem all_presentations_shortExact {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)] (b : ℤ) : (presentation i b).ShortExact := by
  have := presentation_mono i
  exact presentation_shortExact i b

/-- Pointwise rank is expressed by an actual free frame with exactly `r` generators. -/
theorem bundle_rank_frame_at {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)] (x : projectiveSpace R n) :
    ∃ U : (projectiveSpace R n).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (bundle i) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨U,hU,⟨eU⟩⟩ := ProjectiveKernelRankFrames.dual_kernel_frame_at n r t
    (0 : Fin (n+1)) (fun _ => 0) (fun _ => 1) (evaluation i) x
  exact ⟨U,hU,⟨(Scheme.Modules.pullback U.ι).mapIso (bundleKernelDualIso i) ≪≫ eU⟩⟩

/-- The actual fixed cokernel is locally free, with finite local frames. -/
theorem bundle_isLocallyFree {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)] : (bundle i).IsLocallyFree :=
  (bundleFiniteFrames i).locallyFree

/-- Top-map maximal rank gives natural cohomology for every genuine tensor
 twist of this one fixed bundle. -/
theorem all_twists_natural {n t r : ℕ} (hn : 0 < n)
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)]
    (hmax : ∀ b : ℤ, b < -(n : ℤ) → HasMaximalRank
      ((OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective.zariskiFunctor
        (projectiveSpace R n) n).map (presentation i b).f)) :
    ∀ b : ℤ, SchemeModules.HasNaturalCohomology (twist (bundle i) b) := by
  exact steinerCokernel_all_twists_natural hn (presentation i)
    (all_presentations_shortExact i) (presentationSourceIso i) (presentationTargetIso i) hmax

end SteinerGeometry.ProjectiveSteinerPresentation
