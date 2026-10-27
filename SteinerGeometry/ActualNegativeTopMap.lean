module

public import SteinerGeometry.NegativeMapCoefficient
public import SteinerGeometry.NegativeTwistCast
public import SteinerGeometry.FrameMapCoefficient
public import SteinerGeometry.LaurentChartMultiplication
public import SteinerGeometry.LaurentCochainMap
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

set_option backward.privateInPublic true
@[expose] public section

/-! Normalization of actual line-sheaf maps on the top ordered Čech factor. -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ActualNegativeTopMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open LaurentCochainMap
universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The native geometric Čech complex in homogeneous Laurent coordinates. -/
def comparison (j : σ) (d : ℤ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) ≅
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d :=
  TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso
    (R := R) j d ≪≫
  TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso
    (R := R) j d

/-- Transport the actual sheaf map, with its genuine restrictions, to Laurent Čech coordinates. -/
def actualMap (j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1)) :
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d ⟶
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j (d+1) :=
  (comparison j d).inv ≫
    (OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).map f ≫
    (comparison j (d+1)).hom

abbrev unitFactor {q : ℕ} (a : Index (σ := σ) q) :=
  Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (Invertible.Scheme.Modules.unitObj (Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q a.1

abbrev twistFactor (j : σ) (d : ℤ) {q : ℕ} (a : Index (σ := σ) q) :=
  Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q a.1

/-- The factor comparison consists of the canonical twist frame followed by homogeneous reindexing. -/
def factorComparison (j : σ) (d : ℤ) {q : ℕ} (a : Index (σ := σ) q) :
    twistFactor (R := R) j d a ≅ Factor (R := R) d a :=
  TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
    (R := R) a.1 j d ≪≫
  (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
    (R := R) a.1 d).toModuleIso

@[reassoc] theorem comparison_projection (j : σ) (d : ℤ) (q : ℕ)
    (a : Index (σ := σ) q) :
    (comparison (R := R) j d).hom.f q ≫ projection d q a =
      Pi.π (fun b : Index (σ := σ) q => twistFactor (R := R) j d b) a ≫
        (factorComparison (R := R) j d a).hom := by
  have hw : (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d q).hom ≫ projection d q a =
      Pi.π (fun b : Index (σ := σ) q => unitFactor (R := R) b) a ≫
        (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
    exact LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso_hom_comp_π
      (R := R) d q a
  have ht : (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
      (R := R) j d q).hom ≫
      Pi.π (fun b : Index (σ := σ) q => unitFactor (R := R) b) a =
      Pi.π (fun b : Index (σ := σ) q => twistFactor (R := R) j d b) a ≫
        (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
          (R := R) a.1 j d).hom := by
    exact TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit_hom_comp_π
      (R := R) j d q a
  change ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
    (R := R) j d q).hom ≫
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d q).hom) ≫ _ = _
  rw [Category.assoc, hw, ← Category.assoc, ht, Category.assoc]
  rfl

@[reassoc] theorem sheafMap_projection (j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1))
    (q : ℕ) (a : Index (σ := σ) q) :
    ((OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).map f).f q ≫
      Pi.π (fun b : Index (σ := σ) q => twistFactor (R := R) j (d+1) b) a =
    Pi.π (fun b : Index (σ := σ) q => twistFactor (R := R) j d b) a ≫
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
          (op (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)) := by
  change Limits.Pi.map (fun b : Index (σ := σ) q =>
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
        (op (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) b.1))) ≫
      Pi.π (fun b : Index (σ := σ) q => twistFactor (R := R) j (d+1) b) a = _
  exact Pi.map_π _ a

/-- Checking an actual map after one factor comparison checks that projection of its transport. -/
theorem actualMap_projection_of_factor (j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1))
    (q : ℕ) (a : Index (σ := σ) q)
    (g : Factor (R := R) d a ⟶ Factor (R := R) (d+1) a)
    (hg : ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
          (op (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)) ≫
        (factorComparison (R := R) j (d+1) a).hom =
      (factorComparison (R := R) j d a).hom ≫ g) :
    (actualMap (R := R) j d f).f q ≫ projection (d+1) q a =
      projection d q a ≫ g := by
  apply (cancel_epi ((comparison (R := R) j d).hom.f q)).1
  simp only [actualMap, HomologicalComplex.comp_f, Category.assoc]
  have hi : (comparison (R := R) j d).hom.f q ≫
      (comparison (R := R) j d).inv.f q = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun z => z.f q) (comparison (R := R) j d).hom_inv_id
  rw [← Category.assoc, ← Category.assoc, hi, Category.id_comp]
  rw [comparison_projection, ← Category.assoc, sheafMap_projection,
    Category.assoc, hg, ← Category.assoc, ← comparison_projection]
  exact Category.assoc _ _ _

/-- The chart frame used by the geometric twist complex. -/
def chartFrame (i j : σ) (d : ℤ) :=
  Invertible.Scheme.Modules.overTrivializationOfRestrictIso
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j d)

/-- On any standard intersection the native twist frame is the restriction of its anchor frame. -/
theorem factorFrame_eq_restrict (j : σ) (d : ℤ) {q : ℕ} (a : Index (σ := σ) q) :
    Invertible.Scheme.Modules.overTrivializationOfRestrictIso
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
      (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)
      (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization
        (R := R) a.1 j d) =
    Dual.SheafOfModules.restrictOverTrivialization
      (Proj (MvPolynomial.homogeneousSubmodule σ R)).ringCatSheaf
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a.1 0).down)
      (chartFrame (R := R) (a.1 0).down j d)
      (Over.mk (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
        (R := R) a.1 0))) := by
  exact OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization _ _

/-- The scalar obtained by evaluating the actual map in its anchor chart. -/
def chartCoefficient (i j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1)) :=
  FrameMapCoefficient.coefficient f
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (chartFrame (R := R) i j d) (chartFrame (R := R) i j (d+1))

/-- The actual map acts in the native factor frames by the restricted chart scalar. -/
theorem map_factorCoefficient (j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1))
    {q : ℕ} (a : Index (σ := σ) q) :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
        (op (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)) ≫
      (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j (d+1)).hom =
    (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
      (R := R) a.1 j d).hom ≫
      TwistCechFactors.MvPolynomial.baseModulePresheafObjUnitScalar
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
            (R := R) a.1 0)).op (chartCoefficient (R := R) (a.1 0).down j d f)) := by
  unfold TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
  rw [factorFrame_eq_restrict, factorFrame_eq_restrict]
  exact FrameMapCoefficient.base_map_subopen _ f _ _ _ _

section LinearForm
variable [Fintype σ]

/-- A polynomial formula for the anchor coefficient identifies the actual factor map. -/
theorem factor_map_of_coefficient (j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1))
    {q : ℕ} (a : Index (σ := σ) q) (L : σ → Γ(Spec (.of R), ⊤))
    (hc : StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
        (R := R) a.1
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
            (R := R) a.1 0)).op (chartCoefficient (R := R) (a.1 0).down j d f)) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
        (fun l => (a.1 l).down) (LaurentChartMultiplication.linearPolynomial L)) :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map f).app
        (op (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1)) ≫
      (factorComparison (R := R) j (d+1) a).hom =
    (factorComparison (R := R) j d a).hom ≫ ModuleCat.ofHom
      (LaurentResidueShift.linearFormFactor (fun l => (a.1 l).down) d L) := by
  unfold factorComparison
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, map_factorCoefficient, Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change LaurentChartMultiplication.reindex (fun l => (a.1 l).down) (d+1)
      (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
        (R := R) a.1
        (TwistCechFactors.MvPolynomial.baseModulePresheafObjUnitScalar _ _ _ x)) = _
  rw [FrameMapCoefficient.base_scalar_apply]
  change LaurentChartMultiplication.reindex (fun l => (a.1 l).down) (d+1)
      (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv
        (R := R) a.1 (_ * _)) = _
  rw [map_mul]
  change LaurentChartMultiplication.reindex (fun l => (a.1 l).down) (d+1)
      (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
        (R := R) a.1 x *
      StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
        (R := R) a.1 _) = _
  erw [hc]
  exact LaurentChartMultiplication.reindex_mul_linearPolynomial _ d L _

/-- The actual transported map agrees with linear-form multiplication after the chosen projection. -/
theorem actualMap_projection_of_coefficient (j : σ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d+1))
    {q : ℕ} (a : Index (σ := σ) q) (L : σ → Γ(Spec (.of R), ⊤))
    (hc : StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
        (R := R) a.1
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
            (R := R) a.1 0)).op (chartCoefficient (R := R) (a.1 0).down j d f)) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
        (fun l => (a.1 l).down) (LaurentChartMultiplication.linearPolynomial L)) :
    (actualMap (R := R) j d f).f q ≫ projection (d+1) q a =
      linearFormTermMap d L q ≫ projection (d+1) q a := by
  rw [linearFormTermMap_projection]
  exact actualMap_projection_of_factor j d f q a _ (factor_map_of_coefficient j d f a L hc)

end LinearForm

/-- On the unique top intersection, the actual negative-twist map has precisely
its own polynomial encoding, with the native homogeneous Laurent normalization. -/
theorem negative_top_projection (n b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b+1)) (ht : d+1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
        (R := R) (0 : Fin (n+1)) (b+2) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
        (R := R) (0 : Fin (n+1)) (b+1))
    (L : Fin (n+1) → Γ(Spec (.of R), ⊤))
    (hpoly :
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) (0 : Fin (n+1)) (b+2) (b+1) (by omega) f).val =
      LaurentChartMultiplication.linearPolynomial L) :
    (actualMap (R := R) (0 : Fin (n+1)) d
      (NegativeTwistCast.castMap (0 : Fin (n+1)) b d hs ht f)).f n ≫
        projection (d+1) n (LaurentMultiplication.fullIndex n) =
      (linearFormMap (0 : Fin (n+1)) d L).f n ≫
        projection (d+1) n (LaurentMultiplication.fullIndex n) := by
  have hc := NegativeMapCoefficient.coefficient_on_intersection (R := R)
    (0 : Fin (n+1)) (b+2) (b+1) (by omega) f n
    (LaurentMultiplication.fullIndex n) rfl
  have hp := congrArg Subtype.val
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials_apply
      (R := R) (0 : Fin (n+1)) (b+2) (b+1) (by omega) f)
  rw [← hp, hpoly] at hc
  have hcast := NegativeTwistCast.coefficient_castMap (R := R)
    (0 : Fin (n+1)) (0 : Fin (n+1)) b d hs ht f
  change chartCoefficient (R := R) (0 : Fin (n+1)) (0 : Fin (n+1)) d
      (NegativeTwistCast.castMap (0 : Fin (n+1)) b d hs ht f) = _ at hcast
  apply actualMap_projection_of_coefficient (0 : Fin (n+1)) d _
    (LaurentMultiplication.fullIndex n) L
  change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
      (R := R) (LaurentMultiplication.fullIndex n).1
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
          (R := R) (LaurentMultiplication.fullIndex n).1 0)).op
        (chartCoefficient (R := R) (0 : Fin (n+1)) (0 : Fin (n+1)) d
          (NegativeTwistCast.castMap (0 : Fin (n+1)) b d hs ht f))) = _
  rw [hcast]
  exact hc

/-- The same normalization for a map already presented as a map of integer twists. -/
theorem negative_top_projection_uncast (n b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b+1)) (ht : d+1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist
        (R := R) (0 : Fin (n+1)) d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist
        (R := R) (0 : Fin (n+1)) (d+1))
    (L : Fin (n+1) → Γ(Spec (.of R), ⊤))
    (hpoly :
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) (0 : Fin (n+1)) (b+2) (b+1) (by omega)
          (NegativeTwistCast.uncastMap (0 : Fin (n+1)) b d hs ht f)).val =
      LaurentChartMultiplication.linearPolynomial L) :
    (actualMap (R := R) (0 : Fin (n+1)) d f).f n ≫
        projection (d+1) n (LaurentMultiplication.fullIndex n) =
      (linearFormMap (0 : Fin (n+1)) d L).f n ≫
        projection (d+1) n (LaurentMultiplication.fullIndex n) := by
  simpa only [NegativeTwistCast.castMap_uncastMap] using
    negative_top_projection n b d hs ht
      (NegativeTwistCast.uncastMap (0 : Fin (n+1)) b d hs ht f) L hpoly

/-- An actual twist map with the same chart scalar as an original linear
map has the original linear form on the unique top Čech factor. -/
theorem actual_top_projection_of_linear_coefficient (n : ℕ) (d : ℤ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist
        (R := R) (0 : Fin (n+1)) d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist
        (R := R) (0 : Fin (n+1)) (d+1))
    (f₀ : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
        (R := R) (0 : Fin (n+1)) 1 ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
        (R := R) (0 : Fin (n+1)) 0)
    (L : Fin (n+1) → Γ(Spec (.of R), ⊤))
    (hcoef : chartCoefficient (R := R) (0 : Fin (n+1)) (0 : Fin (n+1)) d f =
      FrameMapCoefficient.coefficient f₀
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (0 : Fin (n+1)))
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin (n+1)) (0 : Fin (n+1)) 1)
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin (n+1)) (0 : Fin (n+1)) 0))
    (hpoly :
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) (0 : Fin (n+1)) 1 0 (by omega) f₀).val =
      LaurentChartMultiplication.linearPolynomial L) :
    (actualMap (R := R) (0 : Fin (n+1)) d f).f n ≫
        projection (d+1) n (LaurentMultiplication.fullIndex n) =
      (linearFormMap (0 : Fin (n+1)) d L).f n ≫
        projection (d+1) n (LaurentMultiplication.fullIndex n) := by
  have hc := NegativeMapCoefficient.coefficient_on_intersection (R := R)
    (0 : Fin (n+1)) 1 0 (by omega) f₀ n (LaurentMultiplication.fullIndex n) rfl
  have hp := congrArg Subtype.val
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials_apply
      (R := R) (0 : Fin (n+1)) 1 0 (by omega) f₀)
  rw [← hp, hpoly] at hc
  apply actualMap_projection_of_coefficient (0 : Fin (n+1)) d f
    (LaurentMultiplication.fullIndex n) L
  change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
      (R := R) (LaurentMultiplication.fullIndex n).1
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
          (R := R) (LaurentMultiplication.fullIndex n).1 0)).op
        (chartCoefficient (R := R) (0 : Fin (n+1)) (0 : Fin (n+1)) d f)) = _
  rw [hcoef]
  exact hc

end SteinerGeometry.ActualNegativeTopMap
