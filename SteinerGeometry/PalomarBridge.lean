module

public import SteinerGeometry.PalomarBridgeLemmas

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxRecDepth 1024
set_option maxHeartbeats 20000
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective

namespace PalomarSteiner
universe uDirect
variable {K : Type uDirect} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial extraction determines the actual dense-chart scalar. -/
theorem coefficient_eq_chartValueAt (n : ℕ) (j : Fin (n+1))
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := K) j 1 ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := K) j 0)
    (p : MvPolynomial.homogeneousSubmodule (Fin (n+1)) K 1)
    (hp : (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
      (R := K) j 1 0 (by omega) f).val =
      MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom p.val) :
    SteinerGeometry.FrameMapCoefficient.coefficient f
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) j)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := K) j j 1)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := K) j j 0) =
      PalomarChartBridge.chartValueAt j p := by
  have hv := PalomarChartBridge.chartValue_laurent
    (PalomarCoefficient.singleIndex.{uDirect} j).1 p
  refine PalomarCoefficient.coefficient_eq_of_laurent.{uDirect} (K := K) j f
    (PalomarChartBridge.chartValueAt j p) ?_
  conv_rhs => rw [hp]
  exact hv
end PalomarSteiner

set_option maxRecDepth 1024
namespace PalomarSteiner
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe uBinding
variable {K : Type uBinding} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance (X : Scheme.{uBinding}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

set_option maxHeartbeats 20000 in
/-- The displayed dense-chart entries of the actual normalized presentation are precisely its input linear forms. -/
theorem normalizedMap_represents (n t r : ℕ) (M : Steiner.LinearMatrix K n t (t+r)) :
    RepresentsMatrix K n t r (normalizedMap (SteinerGeometry.linearPresentation K M)) M := by
  intro a b
  let j : Fin (n+1) := 0
  let i := SteinerGeometry.linearPresentation K M
  let f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := K) j 1 ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := K) j 0 :=
    SteinerGeometry.PolynomialTopRank.originalComponent i a b
  obtain ⟨s, hs, hfs⟩ := FrameNormalize.exists_generator (R := K) j f
  have hcomp := normalizedMap_component i a b
  have hcompVal := congrArg
    (fun (φ : ideal K n ⟶ SheafOfModules.unit (SteinerGeometry.projectiveSpace K n).ringCatSheaf) =>
      φ.val.app (op (chartOpen K n)) s) hcomp
  have hp := PalomarHP.coefficient_polynomial n t r M a b
  have hp' : (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
      (R := K) j 1 0 (by omega) f).val =
      MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom (M a b).val := by
    simpa only [f, i, j] using hp
  have hval := coefficient_eq_chartValueAt n j f (M a b) hp'
  have hchart : PalomarChartBridge.chartValueAt j (M a b) = chartValue (M a b) := rfl
  exact ⟨s, hs, hcompVal.trans (hfs.trans (hval.trans hchart))⟩

theorem chart_binding : ChartBinding.{uBinding} := by
  intro K _ n t r M
  exact normalizedMap_represents n t r M
end PalomarSteiner

namespace PalomarSteiner
universe uMain
/-- Theorem 1.1, in the independent concrete formulation used for comparison. -/
theorem main_result : Statement.{uMain} :=
  main_result_of_chart_binding chart_binding
end PalomarSteiner
