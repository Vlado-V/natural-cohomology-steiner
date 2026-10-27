import SteinerGeometry.FiniteSumMapNaturality
import SteinerGeometry.ProjectiveNegativeTensorComparison
import SteinerGeometry.NegativeTensorMap
import SteinerGeometry.SteinerCohomologyCriterion
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleRightTensorMap

/-! Scalar components of the actual tensor-twisted Steiner presentations. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace SteinerGeometry.ProjectiveSteinerComponents
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveSteinerBundle PolynomialTopRank SteinerCohomologyCriterion
open LaurentResidueHomology
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI
attribute [local instance] PolynomialTopRank.polynomialTopBiproducts

/-- Normalize the two endpoint sums in the actual tensor-twisted presentation. -/
def normalizedPresentationMap {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0) (b : ℤ) :
    projectiveTwistSum R n t (b-1) ⟶ projectiveTwistSum R n (t+r) b :=
  (presentationSourceIso i b).inv ≫ (presentation i b).f ≫ (presentationTargetIso i b).hom

/-- The canonical finite-sum comparisons conjugate each scalar component
by exactly the corresponding two line-twist isomorphisms. -/
theorem presentation_component {n t r : ℕ}
    (i : projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0)
    (b : ℤ) (a : Fin t) (c : Fin (t+r)) :
    lineComponent (normalizedPresentationMap i b) a c =
      (minusOneLineTwistIso (R := R) n b).inv ≫
        (twistEquivalence (R := R) n b).functor.map (originalComponent i a c) ≫
          (zeroLineTwistIso (R := R) n b).hom := by
  let F := (twistEquivalence (R := R) n b).functor
  let : F.Additive := F.additive_of_preserves_binary_products
  simpa only [normalizedPresentationMap, lineComponent, originalComponent,
    presentationSourceIso, presentationTargetIso, presentation, ShortComplex.map_f,
    ShortComplex.cokernelSequence_f, Category.assoc] using
    ProjectiveKernelBundle.finiteSumMapIso_conjugated_component F t (t+r)
      (fun _ => projectiveTwist R n (-1)) (fun _ => projectiveTwist R n 0)
      (fun _ => projectiveTwist R n (b-1)) (fun _ => projectiveTwist R n b)
      (fun _ => minusOneLineTwistIso (R := R) n b)
      (fun _ => zeroLineTwistIso (R := R) n b) i a c

private theorem lineComponent_precompose_cast {n t s : ℕ} {d d' e : ℤ}
    (h : d = d')
    (f : projectiveTwistSum R n t d' ⟶ projectiveTwistSum R n s e)
    (a : Fin t) (c : Fin s) :
    lineComponent (eqToHom (congrArg (projectiveTwistSum R n t) h) ≫ f) a c =
      eqToHom (congrArg (projectiveTwist R n) h) ≫ lineComponent f a c := by
  subst d'
  simp only [eqToHom_refl, Category.id_comp]

/-- The source cast in the deep presentation induces only the same scalar
source cast in each matrix component. -/
theorem deepMap_component {p t r : ℕ}
    (i : projectiveTwistSum R (p+1) t (-1) ⟶ projectiveTwistSum R (p+1) (t+r) 0)
    (m : ℕ) (a : Fin t) (c : Fin (t+r)) :
    lineComponent (deepMap i m) a c =
      eqToHom (show projectiveTwist R (p+1) (degree (p+1) (m+1)) =
        projectiveTwist R (p+1) ((degree (p+1) (m+1)+1)-1) by congr 1) ≫
      (minusOneLineTwistIso (R := R) (p+1) (degree (p+1) (m+1)+1)).inv ≫
        (twistEquivalence (R := R) (p+1) (degree (p+1) (m+1)+1)).functor.map
          (originalComponent i a c) ≫
          (zeroLineTwistIso (R := R) (p+1) (degree (p+1) (m+1)+1)).hom := by
  let d := degree (p+1) (m+1)
  have h : d = (d+1)-1 := by omega
  simp only [deepMap, deepSourceIso, Iso.trans_inv, eqToIso.inv, Category.assoc]
  change lineComponent (eqToHom (congrArg (projectiveTwistSum R (p+1) t) h) ≫
      normalizedPresentationMap i (d+1)) a c = _
  rw [lineComponent_precompose_cast h, presentation_component]

private theorem negativeLineMap_canonical (n k : ℕ)
    (f : projectiveTwist R n (-1) ⟶ projectiveTwist R n 0) :
    (minusOneLineTwistIso (R := R) n (Int.negSucc k)).inv ≫
        (twistEquivalence (R := R) n (Int.negSucc k)).functor.map f ≫
          (zeroLineTwistIso (R := R) n (Int.negSucc k)).hom =
      NegativeTensorMap.map (0 : Fin (n+1)) (k+1) f := by
  set_option backward.dsimp.proofs true in
    dsimp +instances only [NegativeTensorMap.map, NegativeTensorMap.sourceIso] at ⊢
  rw [lineMap_eq_conjugated, minusOneLineTwistIso_negSucc]
  set_option backward.dsimp.proofs true in
    dsimp +instances only [projectiveSpace, projectiveTwist, NegativeTensorMap.power,
      zeroLineTwistIso,
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist] at ⊢

private theorem negativeLineMap_normalized (n k : ℕ) (b : ℤ)
    (hb : b = Int.negSucc k)
    (f : projectiveTwist R n (-1) ⟶ projectiveTwist R n 0) :
    eqToHom (show NegativeTensorMap.power (R := R) (0 : Fin (n+1)) (k+2) =
      projectiveTwist R n (b-1) by rw [hb]; rfl) ≫
      (minusOneLineTwistIso (R := R) n b).inv ≫
        (twistEquivalence (R := R) n b).functor.map f ≫
          (zeroLineTwistIso (R := R) n b).hom ≫
            eqToHom (show projectiveTwist R n b =
              NegativeTensorMap.power (R := R) (0 : Fin (n+1)) (k+1) by rw [hb]; rfl) =
      NegativeTensorMap.map (0 : Fin (n+1)) (k+1) f := by
  subst b
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    negativeLineMap_canonical (R := R) n k f

private theorem negativeLineMap_eq_cast (n k : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (k+1)) (ht : d+1 = Int.negSucc k)
    (f : NegativeTensorMap.power (R := R) (0 : Fin (n+1)) 1 ⟶
      NegativeTensorMap.power (R := R) (0 : Fin (n+1)) 0) :
    eqToHom (show projectiveTwist R n d = projectiveTwist R n ((d+1)-1) by congr 1; omega) ≫
      (minusOneLineTwistIso (R := R) n (d+1)).inv ≫
        (twistEquivalence (R := R) n (d+1)).functor.map f ≫
          (zeroLineTwistIso (R := R) n (d+1)).hom =
      NegativeTwistCast.castMap (0 : Fin (n+1)) k d hs ht
        (NegativeTensorMap.map (0 : Fin (n+1)) (k+1) f) := by
  let u : NegativeTensorMap.power (R := R) (0 : Fin (n+1)) (k+2) ⟶
      projectiveTwist R n d := eqToHom (by rw [hs]; rfl)
  let v : projectiveTwist R n (d+1) ⟶
      NegativeTensorMap.power (R := R) (0 : Fin (n+1)) (k+1) := eqToHom (by rw [ht]; rfl)
  apply (cancel_mono v).mp
  apply (cancel_epi u).mp
  simpa only [u, v, NegativeTwistCast.castMap, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id] using
    negativeLineMap_normalized (R := R) n k (d+1) ht f

/-- Each deep negative component is exactly the actual tensor-conjugated
negative-power map, with its source and target degree casts. -/
theorem deepMap_component_eq_cast {p t r : ℕ}
    (i : projectiveTwistSum R (p+1) t (-1) ⟶ projectiveTwistSum R (p+1) (t+r) 0)
    (m : ℕ) (a : Fin t) (c : Fin (t+r)) :
    lineComponent (deepMap i m) a c =
      NegativeTwistCast.castMap (0 : Fin ((p+1)+1)) (m+p+1) (degree (p+1) (m+1))
        (by simp [degree]; omega) (by simp [degree]; omega)
        (NegativeTensorMap.map (0 : Fin ((p+1)+1)) (m+p+2) (originalComponent i a c)) := by
  rw [deepMap_component]
  exact negativeLineMap_eq_cast (p+1) (m+p+1) (degree (p+1) (m+1))
    (by simp [degree]; omega) (by simp [degree]; omega) (originalComponent i a c)

/-- The literal scalar coefficient of the original map is preserved in
every deep negative presentation of the same fixed cokernel. -/
theorem deepMap_chartCoefficient {p t r : ℕ}
    (i : projectiveTwistSum R (p+1) t (-1) ⟶ projectiveTwistSum R (p+1) (t+r) 0)
    (m : ℕ) (a : Fin t) (c : Fin (t+r)) :
    ActualNegativeTopMap.chartCoefficient (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1))
        (degree (p+1) (m+1)) (lineComponent (deepMap i m) a c) =
      FrameMapCoefficient.coefficient (originalComponent i a c)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (0 : Fin ((p+1)+1)))
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) 1)
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) 0) := by
  rw [deepMap_component_eq_cast]
  change FrameMapCoefficient.coefficient _ _ _ _ = _
  dsimp only [ActualNegativeTopMap.chartFrame]
  rw [NegativeTwistCast.coefficient_castMap
    (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) (m+p+1) (degree (p+1) (m+1))
    (by simp [degree]; omega) (by simp [degree]; omega)]
  exact NegativeTensorMap.coefficient_map (0 : Fin ((p+1)+1)) (m+p+2)
    (originalComponent i a c)

end SteinerGeometry.ProjectiveSteinerComponents
