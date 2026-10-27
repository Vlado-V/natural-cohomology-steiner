import SteinerGeometry.SymmetricKernelBaseChange
import SteinerGeometry.EvaluationKernelPullback
import SteinerGeometry.CurvePresentation
import SteinerGeometry.NativeCohomologyAdditive
import SteinerGeometry.FiniteSumCohomology
import SteinerGeometry.GeneralCohomologyDescent

/-! Cohomology vanishing for the actual cyclic-cover contraction kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

local instance cyclicContractionVanishingBiproducts (X : Scheme) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]
    [IsLocallyNoetherian q.target.scheme.left]

/-- The actual differential of the dual-evaluation sections from a genuine
presentation of the cyclic pushforward. -/
def contractionMap (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d : ℕ) :=
  curveSectionContraction (DualEvaluation.targetLine P.relationLine) B
    (DualEvaluation.componentSections P.relationLine P.inclusion) d

/-- The kernel is the categorical sheaf kernel of that actual differential. -/
abbrev contractionKernel (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d : ℕ) :=
  kernel (q.contractionMap A P B d)

/-- One line summand in the split pullback of the contraction kernel. -/
def contractionMonomialLine (A : Line.Bundles.LineBundle D.scheme.left)
    (B : Line.Bundles.LineBundle q.target.scheme.left) {s : ℕ} (a : Sym (Fin n) s) :
    Line.Bundles.LineBundle D.scheme.left :=
  (monomialLineBundle (q.firstKernelLineFamily A) a).tensor (B.pullback q.map.hom.left)

/-- The pullback decomposition uses the actual cyclic kernel splitting and
actual epimorphic evaluation; neither is an additional assumption. -/
def contractionKernelPullbackSplitting (p : q.target.scheme.left ⟶ Spec (.of ℂ))
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d : ℕ) :
    (Scheme.Modules.pullback q.map.hom.left).obj (q.contractionKernel A P B d) ≅
      ⨁ fun a : Sym (Fin n) (d+1) => (q.contractionMonomialLine A B a).sheaf := by
  let _ : Epi (DualEvaluation.evaluation P.relationLine P.inclusion) := P.evaluation_epi
  exact (curveKernelBaseChangeSplitIso_of_epi (d := d) q.map.hom.left p
    (DualEvaluation.targetLine P.relationLine) B
    (DualEvaluation.evaluation P.relationLine P.inclusion) (q.firstKernelLineFamily A)
    (q.componentKernelSplitting A P.relationLine P.inclusion P.quotient P.zero P.exact)).symm

omit [NeZero n] [IsLocallyNoetherian q.target.scheme.left] in
/-- The downstairs kernel is quasicoherent because it is the kernel of a
map between actual finite sums of line bundles. -/
theorem contractionKernel_isQuasicoherent
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d : ℕ) :
    (q.contractionKernel A P B d).IsQuasicoherent := by
  let _ : (⨁ fun _ : Sym (Fin (n+1)) (d+1) => B.sheaf).IsQuasicoherent :=
    KernelPullbackLineSum.lineSum_isQuasicoherent B _
  let _ : (⨁ fun _ : Sym (Fin (n+1)) d =>
      ((DualEvaluation.targetLine P.relationLine).tensor B).sheaf).IsQuasicoherent :=
    KernelPullbackLineSum.lineSum_isQuasicoherent
      ((DualEvaluation.targetLine P.relationLine).tensor B) _
  exact OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel
    (q.contractionMap A P B d)

/-- The pullback kernel is quasicoherent by its proved finite line decomposition. -/
theorem contractionKernelPullback_isQuasicoherent
    (p : q.target.scheme.left ⟶ Spec (.of ℂ))
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d : ℕ) :
    ((Scheme.Modules.pullback q.map.hom.left).obj (q.contractionKernel A P B d)).IsQuasicoherent := by
  let L := fun a : Sym (Fin n) (d+1) => (q.contractionMonomialLine A B a).sheaf
  have hsum : (⨁ L).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent D.scheme.left.ringCatSheaf).prop_of_iso
      (biproduct.isoCoproduct L).symm
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct
        L (fun a => (q.contractionMonomialLine A B a).isQuasicoherent))
  exact (SheafOfModules.isQuasicoherent D.scheme.left.ringCatSheaf).prop_of_iso
    (q.contractionKernelPullbackSplitting p A P B d).symm hsum

/-- Vanishing of the actual monomial-line summands gives vanishing of the
upstairs pullback kernel under the native cohomology functor. -/
theorem contractionKernelPullback_cohomology_zero
    (p : q.target.scheme.left ⟶ Spec (.of ℂ))
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d j : ℕ)
    (hz : ∀ a : Sym (Fin n) (d+1),
      IsZero (H (q.map.hom.left ≫ p) (q.contractionMonomialLine A B a).sheaf j)) :
    IsZero (H (q.map.hom.left ≫ p)
      ((Scheme.Modules.pullback q.map.hom.left).obj (q.contractionKernel A P B d)) j) := by
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap (q.map.hom.left ≫ p)) j
  exact cohomology_vanishes_of_finite_split F
    (fun a : Sym (Fin n) (d+1) => (q.contractionMonomialLine A B a).sheaf)
    (q.contractionKernelPullbackSplitting p A P B d) hz

/-- The canonical finite-flat trace descends vanishing of the monomial-line
summands to the genuine contraction kernel downstairs. -/
theorem contractionKernel_cohomology_zero
    [q.target.scheme.left.IsSeparated]
    (p : q.target.scheme.left ⟶ Spec (.of ℂ))
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left) (d j : ℕ)
    (hz : ∀ a : Sym (Fin n) (d+1),
      IsZero (H (q.map.hom.left ≫ p) (q.contractionMonomialLine A B a).sheaf j)) :
    IsZero (H p (q.contractionKernel A P B d) j) := by
  let _ := q.contractionKernel_isQuasicoherent A P B d
  let _ := q.contractionKernelPullback_isQuasicoherent p A P B d
  exact cohomology_zero_of_finiteFlat_pullback_complex q.map.hom.left q.degree p
    (Nat.pos_of_ne_zero (NeZero.ne n)) (q.contractionKernel A P B d) j
    (q.contractionKernelPullback_cohomology_zero p A P B d j hz)

end SteinerGeometry.CyclicEtaleIsogeny
