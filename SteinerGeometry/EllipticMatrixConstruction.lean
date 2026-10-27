import SteinerGeometry.CyclicMatrixWitness
import SteinerGeometry.CyclicCurvePresentation
import SteinerGeometry.CurvePushforwardEvaluation
import SteinerGeometry.PresentationEuler
import SteinerGeometry.TorsionReferenceLine
import SteinerGeometry.TorsionLineChoice
import SteinerGeometry.EllipticFamilyVanishing
import SteinerGeometry.CyclicMonomialDegree
import Steiner.CriticalGap

/-! Assembly of the elliptic matrix from actual line bundles and the finite
critical-degree exclusion. The rectangular construction supplies the curve
invariants and torsion infinitude used here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Steiner
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

variable {D : EllipticScheme} {n : ℕ} [NeZero n]
    (q : CyclicEtaleIsogeny D n)
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [IsIntegral q.target.scheme.left] [IsNoetherian q.target.scheme.left]
    [CurveCohomologyFinite D.scheme.hom]
    [CurveCohomologyFinite q.target.scheme.hom]
    [Infinite (TorsionLineClasses.TorsionClass D.scheme.left)]
    [Infinite (TorsionLineClasses.TorsionClass q.target.scheme.left)]

theorem genericMatrixConclusion_of_elliptic_cover
    {K : Type*} [Field K] [CharZero K] {t r : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : n < r)
    (hdD : topologicalKrullDim D.scheme.left ≤ 1)
    (hdC : topologicalKrullDim q.target.scheme.left ≤ 1)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0) :
    GenericMatrixConclusion K n t r := by
  let c := criticalFloor n t r
  let forbidden := fun (A : Line.Bundles.LineBundle D.scheme.left)
      (a : Sym (Fin n) c) => monomialLineBundle (q.contractionPrimalLineFamily A) a
  obtain ⟨A, B, hA, hB, hPB, hav⟩ :=
    TorsionLineChoice.exists_lineBundles_with_degrees_avoiding q hdD hdC hOD hOC r t forbidden
  let HD := TorsionLineChoice.identityPointLine D
  let HC := TorsionLineChoice.identityPointLine q.target
  have hHD : χ D.scheme.hom HD.sheaf = 1 := by
    exact PointEuler.rationalPointLine_euler D.scheme.hom hdD
      η[D.scheme].left η[D.scheme].w hOD
  have hHC : χ q.target.scheme.hom HC.sheaf = 1 := by
    exact PointEuler.rationalPointLine_euler q.target.scheme.hom hdC
      η[q.target.scheme].left η[q.target.scheme].w hOC
  obtain ⟨PD, hPD, hPDne⟩ := TorsionReferenceLine.exists_zero_euler_nontrivial_line
    D.scheme.hom hdD hOD HD (by omega)
  obtain ⟨PC, hPC, hPCne⟩ := TorsionReferenceLine.exists_zero_euler_nontrivial_line
    q.target.scheme.hom hdC hOC HC (by omega)
  have hAn : (n : ℤ) < χ D.scheme.hom A.sheaf := by
    rw [hA]
    exact_mod_cast hr
  obtain ⟨P⟩ := q.exists_curvePresentation A hdC
    (q.linePushforward_evaluation_surjective hdD hOD PD hPD hPDne hOC A hAn)
  let L := DualEvaluation.targetLine P.relationLine
  have hLT := q.presentationTarget_euler hdC hOC A P B (r : ℤ) (t : ℤ) hA hB
  have hLB : χ q.target.scheme.hom (L.tensor B).sheaf = (r : ℤ) + t := hLT.2
  have hBp : 0 < χ q.target.scheme.hom B.sheaf := by
    rw [hB]
    exact_mod_cast (show 0 < t by omega)
  have hLBp : 0 < χ q.target.scheme.hom (L.tensor B).sheaf := by
    rw [hLB]
    have : (0 : ℤ) < t := by exact_mod_cast (show 0 < t by omega)
    omega
  let : Module.Finite ℂ ((sectionFunctor q.target.scheme.hom).obj B.sheaf) :=
    line_sectionFunctor_finite q.target.scheme.hom B
  let : Module.Finite ℂ ((sectionFunctor q.target.scheme.hom).obj (L.tensor B).sheaf) :=
    line_sectionFunctor_finite q.target.scheme.hom (L.tensor B)
  have hBdim : Module.finrank ℂ ((sectionFunctor q.target.scheme.hom).obj B.sheaf) = t := by
    have hh := positive_euler_sectionFunctor_finrank q.target.scheme.hom hdC hOC
      HC (by omega) PC hPC hPCne B hBp
    rw [hB] at hh
    exact_mod_cast hh
  have hLBdim : Module.finrank ℂ ((sectionFunctor q.target.scheme.hom).obj
      (L.tensor B).sheaf) = t + r := by
    have hh := positive_euler_sectionFunctor_finrank q.target.scheme.hom hdC hOC
      HC (by omega) PC hPC hPCne (L.tensor B) hLBp
    rw [hLB] at hh
    have hh' : (Module.finrank ℂ ((sectionFunctor q.target.scheme.hom).obj
        (L.tensor B).sheaf) : ℤ) = (t + r : ℕ) := by
      push_cast
      omega
    exact_mod_cast hh'
  have hnontrivial (s : ℕ) (a : Sym (Fin n) s)
      (hz : (n : ℤ) * t - (r : ℤ) * s = 0) :
      ¬ Nonempty ((q.contractionMonomialLine A B a).sheaf ≅
        Line.Bundles.structureModule D.scheme.left) := by
    have hs : s = c := degree_eq_criticalFloor_of_gap_zero (by omega) hz
    subst s
    exact q.contractionMonomialLine_nontrivial A B a (hav a)
  apply q.genericMatrixConclusion_of_monomial_line_vanishing hn ht (by omega)
    A P B hBdim hLBdim
  intro d
  apply equal_euler_line_family_vanishing D.scheme.hom hdD hOD HD (by omega)
    PD hPD hPDne (fun a : Sym (Fin n) (d+1) => q.contractionMonomialLine A B a)
    ((n : ℤ) * t - (r : ℤ) * (d+1))
  · intro a
    have he := q.contractionMonomialLine_euler hdD hOD HD (by omega) A B
      (r : ℤ) (t : ℤ) hA hPB a
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using he
  · intro hz a
    exact hnontrivial (d+1) a hz

end SteinerGeometry.CyclicEtaleIsogeny
