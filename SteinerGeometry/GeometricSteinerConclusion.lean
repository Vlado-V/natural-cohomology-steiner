module

public import SteinerGeometry.SteinerCohomologyCriterion
public import SteinerGeometry.PolynomialMatrixSurjective
public import SteinerGeometry.LiteralSteinerPolynomial
public import SteinerGeometry.ProjectiveSteinerComponents
public import SteinerGeometry.AllDegreeMaximalRank
public import Steiner.ScalarExtension

set_option backward.privateInPublic true
@[expose] public section

/-! The geometric conclusion records one actual cokernel sheaf, its exact
Steiner sequence, rank, kernel duality, and all of its tensor twists. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSteinerBundle ProjectiveDualNormalization
universe u

structure NaturalSteinerPresentation {R : Type u} [CommRing R] {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) : Prop where
  shortExact : (ShortComplex.cokernelSequence i).ShortExact
  locallyFree : (bundle i).IsLocallyFree
  rank : ∀ x : projectiveSpace R n,
    ∃ U : (projectiveSpace R n).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (bundle i) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
  kernelDual : Nonempty (bundle i ≅ SheafDual.dual (kernel (evaluation i)))
  natural : ∀ b : ℤ, SchemeModules.HasNaturalCohomology (twist (bundle i) b)

/-- The rank and exactness clauses are consequences of the actual
epimorphic evaluation; only the cohomological deduction remains. -/
theorem naturalSteinerPresentation_of_evaluation_epi
    {R : Type u} [CommRing R] {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    [Epi (evaluation i)]
    (hnatural : ∀ b : ℤ, SchemeModules.HasNaturalCohomology (twist (bundle i) b)) :
    NaturalSteinerPresentation i := by
  let : Mono i := ProjectiveSteinerPresentation.presentation_mono i
  exact
    { shortExact :=
        { exact := ShortComplex.cokernelSequence_exact i
          mono_f := by
            change Mono i
            infer_instance }
      locallyFree := ProjectiveSteinerPresentation.bundle_isLocallyFree i
      rank := ProjectiveSteinerPresentation.bundle_rank_frame_at i
      kernelDual := ⟨ProjectiveSteinerPresentation.bundleKernelDualIso i⟩
      natural := hnatural }

/-- An all-degree maximal-rank matrix supplies an actual fixed rank-`r`
Steiner bundle on the specified projective space. -/
theorem literalPresentation_naturalSteiner
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R),⊤))
    {n t r : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : Fin t → Fin (t+r) →
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) Γ(Spec (.of R),⊤) 1)
    (hM : letI : Field Γ(Spec (.of R),⊤) := SteinerGeometry.canonicalField hfield
      ∀ d, Steiner.LinearMatrixMaximalRank M d) :
    NaturalSteinerPresentation (PolynomialMatrixSurjective.literalPresentation (R := R) M) := by
  letI := PolynomialMatrixSurjective.literalPresentation_evaluation_epi (R := R) hfield hn ht hr M hM
  apply naturalSteinerPresentation_of_evaluation_epi
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply SteinerCohomologyCriterion.all_twists_natural_of_coefficients (R := R) hfield
    (PolynomialMatrixSurjective.literalPresentation (R := R) M) M hM
  · exact ProjectiveSteinerComponents.deepMap_chartCoefficient (R := R)
      (PolynomialMatrixSurjective.literalPresentation (R := R) M)
  · exact LiteralSteinerPolynomial.originalComponent_polynomial (R := R) M

section Field
variable (K : Type u) [Field K]

noncomputable local instance coefficientField : Field Γ(Spec (.of K),⊤) :=
  SteinerGeometry.canonicalField
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K))

/-- The coefficient map is the canonical inverse of global sections of `Spec K`. -/
def specCoefficientMap : K →+* Γ(Spec (.of K),⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv.hom

/-- A scalar matrix defines the literal transpose map of projective line bundles. -/
def linearPresentation {n t r : ℕ} (M : Steiner.LinearMatrix K n t (t+r)) :
    projectiveTwistSum K n t (-1) ⟶ projectiveTwistSum K n (t+r) 0 :=
  PolynomialMatrixSurjective.literalPresentation (R := K)
    (Steiner.linearMatrixExtend (specCoefficientMap K) M)

/-- The one fixed actual module sheaf associated with a scalar matrix. -/
abbrev steinerBundle {n t r : ℕ} (M : Steiner.LinearMatrix K n t (t+r)) :=
  bundle (linearPresentation K M)

/-- One principal open in the original scalar parameter space, whose points
give actual rank-`r` Steiner bundles with natural cohomology in every twist. -/
def GenericNaturalSteinerConclusion (n t r : ℕ) : Prop :=
  ∃ D : MvPolynomial (Steiner.LinearMatrixParameter n t (t+r)) K,
    (∃ u, MvPolynomial.eval u D ≠ 0) ∧
    ∀ u, MvPolynomial.eval u D ≠ 0 →
      NaturalSteinerPresentation
        (linearPresentation K (Steiner.universalLinearMatrix K n t (t+r) u))

/-- The geometric bridge for one actual scalar matrix over the original field. -/
theorem linearMatrix_naturalSteiner {n t r : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : Steiner.LinearMatrix K n t (t+r))
    (hM : ∀ d, Steiner.LinearMatrixMaximalRank M d) :
    NaturalSteinerPresentation (linearPresentation K M) := by
  let hfield : IsField Γ(Spec (.of K),⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  apply literalPresentation_naturalSteiner (R := K) hfield hn ht hr
    (Steiner.linearMatrixExtend (specCoefficientMap K) M)
  intro d
  exact (Steiner.linearMatrixMaximalRank_extend_iff (specCoefficientMap K) M d).2 (hM d)

/-- A nonempty principal open of all-rank scalar matrices is a nonempty
principal open of actual natural-cohomology Steiner bundles. -/
theorem genericNaturalSteiner_of_genericMatrixConclusion {n t r : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (h : Steiner.GenericMatrixConclusion K n t r) :
    GenericNaturalSteinerConclusion K n t r := by
  obtain ⟨D,hD,hM⟩ := h
  exact ⟨D,hD,fun u hu => linearMatrix_naturalSteiner K hn ht hr _ (hM u hu)⟩

/-- The requested all-parameter theorem, over every characteristic-zero field.
The bundle at each parameter point is the same fixed cokernel for every twist. -/
theorem genericNaturalSteiner_charZero [CharZero K] (n t r : ℕ)
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : n ≤ r) :
    GenericNaturalSteinerConclusion K n t r := by
  apply genericNaturalSteiner_of_genericMatrixConclusion K hn ht (by omega)
  exact Steiner.genericMatrixConclusion_charZero K n t r hn ht hr

end Field
end SteinerGeometry
