import SteinerGeometry.NegativePowerTensorIso
import SteinerGeometry.ProjectiveCohomology
import SteinerGeometry.ProjectiveKernelRankFrames
import SteinerGeometry.ProjectiveDualKernelExact
import SteinerGeometry.FiniteFrameProperties
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso

/-! A single actual Steiner cokernel and the exact presentations of its tensor twists. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ProjectiveSteinerBundle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI
local instance steinerSymmetric (n : ℕ) : SymmetricCategory (projectiveSpace R n).Modules :=
  Monoidal.Scheme.Modules.symmetricCategory _
local instance steinerBiproducts (n : ℕ) : HasFiniteBiproducts (projectiveSpace R n).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Tensoring with the actual `O(b)` is an equivalence for every integer `b`. -/
def twistEquivalence (n : ℕ) (b : ℤ) :
    (projectiveSpace R n).Modules ≌ (projectiveSpace R n).Modules :=
  InvertibleTensorEquivalence.invertibleRightTensorEquivalence
    (projectiveTwist R n b)
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (0 : Fin (n+1)) b)

/-- The tensor twist of an actual module sheaf. -/
abbrev twist {n : ℕ} (M : (projectiveSpace R n).Modules) (b : ℤ) :=
  (twistEquivalence (R := R) n b).functor.obj M

/-- The twist by zero is canonically the original sheaf. -/
def twistZeroIso {n : ℕ} (M : (projectiveSpace R n).Modules) :
    twist M 0 ≅ M := ρ_ M

/-- The actual zero-degree line tensored with `O(b)` is `O(b)`. -/
def zeroLineTwistIso (n : ℕ) (b : ℤ) :
    twist (projectiveTwist R n 0) b ≅ projectiveTwist R n b :=
  λ_ (projectiveTwist R n b)

/-- `O(-1) ⊗ O(b)` is the actual line `O(b-1)`, including negative `b`. -/
def minusOneLineTwistIso (n : ℕ) (b : ℤ) :
    twist (projectiveTwist R n (-1)) b ≅ projectiveTwist R n (b-1) := by
  let j : Fin (n+1) := 0
  cases b with
  | ofNat k =>
    cases k with
    | zero => exact ρ_ (projectiveTwist R n (-1))
    | succ k =>
      change _ ≅ projectiveTwist R n (((k+1 : ℕ) : ℤ)-1)
      rw [show (((k+1 : ℕ) : ℤ)-1) = (k : ℤ) by omega]
      change TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j 1 ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (k+1) ≅
          TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j k
      simpa only [Nat.add_sub_cancel] using
        (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE
          (R := R) j 1 (k+1) (by omega))
  | negSucc k =>
    exact NegativePowerTensorIso.iso j (k+1)

/-- The negative branch uses the shared named tensor isomorphism. -/
theorem minusOneLineTwistIso_negSucc (n k : ℕ) :
    minusOneLineTwistIso (R := R) n (Int.negSucc k) =
      NegativePowerTensorIso.iso (R := R) (0 : Fin (n+1)) (k+1) := by
  rfl

/-- The line-normalization map is the actual left unitor. -/
theorem zeroLineTwistIso_hom (n : ℕ) (b : ℤ) :
    (zeroLineTwistIso (R := R) n b).hom = (λ_ (projectiveTwist R n b)).hom := rfl

/-- The tensor-twist functor maps a morphism by right tensoring it. -/
theorem twistEquivalence_map {n : ℕ} (b : ℤ)
    {M N : (projectiveSpace R n).Modules} (f : M ⟶ N) :
    (twistEquivalence (R := R) n b).functor.map f = f ▷ projectiveTwist R n b := rfl

/-- Tensor twists commute with the finite line sums. -/
def twistSumIso (n s : ℕ) (a b : ℤ)
    (e : twist (projectiveTwist R n a) b ≅ projectiveTwist R n (a+b)) :
    twist (projectiveTwistSum R n s a) b ≅ projectiveTwistSum R n s (a+b) := by
  let F := (twistEquivalence (R := R) n b).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  exact ProjectiveKernelBundle.finiteSumMapIso F s _ ≪≫ Sigma.mapIso (fun _ => e)

/-- A single actual Steiner cokernel, before any twist is chosen. -/
abbrev bundle {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) :=
  cokernel i

/-- All presentations are obtained by tensoring the one original cokernel sequence. -/
def presentation {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) (b : ℤ) :
    ShortComplex (projectiveSpace R n).Modules :=
  (ShortComplex.cokernelSequence i).map (twistEquivalence (R := R) n b).functor

/-- The third object is definitionally the twist of the same fixed bundle. -/
theorem presentation_bundle {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) (b : ℤ) :
    (presentation i b).X₃ = twist (bundle i) b := rfl

/-- Every integer twist has the genuine tensor image of the original short exact sequence. -/
theorem presentation_shortExact {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) [Mono i] (b : ℤ) :
    (presentation i b).ShortExact := by
  have h : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := by change Mono i; infer_instance }
  exact h.map_of_exact (twistEquivalence (R := R) n b).functor

/-- The source in the twisted presentation is `O(b-1)^t`. -/
def presentationSourceIso {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) (b : ℤ) :
    (presentation i b).X₁ ≅ projectiveTwistSum R n t (b-1) := by
  let F := (twistEquivalence (R := R) n b).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  exact ProjectiveKernelBundle.finiteSumMapIso F t _ ≪≫
    Sigma.mapIso (fun _ => minusOneLineTwistIso (R := R) n b)

/-- The middle term in the twisted presentation is `O(b)^(t+r)`. -/
def presentationTargetIso {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) (b : ℤ) :
    (presentation i b).X₂ ≅ projectiveTwistSum R n (t+r) b := by
  let F := (twistEquivalence (R := R) n b).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  exact ProjectiveKernelBundle.finiteSumMapIso F (t+r) _ ≪≫
    Sigma.mapIso (fun _ => zeroLineTwistIso (R := R) n b)

end SteinerGeometry.ProjectiveSteinerBundle

namespace SteinerGeometry.ProjectiveSteinerBundle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveKernelBundle
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalize the reversed dual of one actual linear epimorphism. -/
def normalizedDualMap {n t r : ℕ}
    (A : projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1)
    (eSource : SheafDual.dual (projectiveTwistSum R n t 1) ≅ projectiveTwistSum R n t (-1))
    (eTarget : SheafDual.dual (projectiveTwistSum R n (t+r) 0) ≅
      projectiveTwistSum R n (t+r) 0) :
    projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0 :=
  eSource.inv ≫ SheafDual.dualMap A ≫ eTarget.hom

/-- Its actual cokernel is canonically the dual of the actual kernel of `A`. -/
def bundleDualKernelIso {n t r : ℕ}
    (A : projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1) [Epi A]
    (eSource : SheafDual.dual (projectiveTwistSum R n t 1) ≅ projectiveTwistSum R n t (-1))
    (eTarget : SheafDual.dual (projectiveTwistSum R n (t+r) 0) ≅
      projectiveTwistSum R n (t+r) 0) :
    bundle (normalizedDualMap A eSource eTarget) ≅ SheafDual.dual (kernel A) :=
  cokernel.mapIso _ _ eSource.symm eTarget.symm (by
    simp [normalizedDualMap]) ≪≫
  ProjectiveDualKernelExact.cokernelDualMapIso n (t+r) t (0 : Fin (n+1))
    (fun _ => 0) (fun _ => 1) A

/-- The normalized dual presentation is an actual monomorphism. -/
theorem normalizedDualMap_mono {n t r : ℕ}
    (A : projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1) [Epi A]
    (eSource : SheafDual.dual (projectiveTwistSum R n t 1) ≅ projectiveTwistSum R n t (-1))
    (eTarget : SheafDual.dual (projectiveTwistSum R n (t+r) 0) ≅
      projectiveTwistSum R n (t+r) 0) :
    Mono (normalizedDualMap A eSource eTarget) := by
  have h := ProjectiveDualKernelExact.dualKernelSequence_shortExact n (t+r) t
    (0 : Fin (n+1)) (fun _ => 0) (fun _ => 1) A
  let : Mono (SheafDual.dualMap A) := h.mono_f
  dsimp [normalizedDualMap]
  infer_instance

/-- The one fixed cokernel sheaf has local frames of the exact expected rank. -/
def bundleFiniteFrames {n t r : ℕ}
    (A : projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1) [Epi A]
    (eSource : SheafDual.dual (projectiveTwistSum R n t 1) ≅ projectiveTwistSum R n t (-1))
    (eTarget : SheafDual.dual (projectiveTwistSum R n (t+r) 0) ≅
      projectiveTwistSum R n (t+r) 0) :
    TildeFiniteProjective.FiniteGeometricFrameCover
      (bundle (normalizedDualMap A eSource eTarget)) :=
  (ProjectiveKernelRankFrames.dualKernelFiniteFrames n r t (0 : Fin (n+1))
    (fun _ => 0) (fun _ => 1) A).mapIso (bundleDualKernelIso A eSource eTarget).symm

/-- Local freeness follows from the frames of that same cokernel. -/
theorem bundle_isLocallyFree {n t r : ℕ}
    (A : projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1) [Epi A]
    (eSource : SheafDual.dual (projectiveTwistSum R n t 1) ≅ projectiveTwistSum R n t (-1))
    (eTarget : SheafDual.dual (projectiveTwistSum R n (t+r) 0) ≅
      projectiveTwistSum R n (t+r) 0) :
    (bundle (normalizedDualMap A eSource eTarget)).IsLocallyFree :=
  (bundleFiniteFrames A eSource eTarget).locallyFree

/-- At every point the fixed cokernel has a free frame on precisely `r` generators. -/
theorem bundle_rank_frame_at {n t r : ℕ}
    (A : projectiveTwistSum R n (t+r) 0 ⟶ projectiveTwistSum R n t 1) [Epi A]
    (eSource : SheafDual.dual (projectiveTwistSum R n t 1) ≅ projectiveTwistSum R n t (-1))
    (eTarget : SheafDual.dual (projectiveTwistSum R n (t+r) 0) ≅
      projectiveTwistSum R n (t+r) 0) (x : projectiveSpace R n) :
    ∃ U : (projectiveSpace R n).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
        (bundle (normalizedDualMap A eSource eTarget)) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨U,hU,⟨eU⟩⟩ := ProjectiveKernelRankFrames.dual_kernel_frame_at n r t
    (0 : Fin (n+1)) (fun _ => 0) (fun _ => 1) A x
  exact ⟨U,hU,⟨(Scheme.Modules.pullback U.ι).mapIso
    (bundleDualKernelIso A eSource eTarget) ≪≫ eU⟩⟩

end SteinerGeometry.ProjectiveSteinerBundle
