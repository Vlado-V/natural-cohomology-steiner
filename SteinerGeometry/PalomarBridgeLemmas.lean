module

public import SteinerGeometry.PalomarStatement
public import SteinerGeometry.GeometricSteinerConclusion
public import SteinerGeometry.NegativeMapCoefficient
public import SteinerGeometry.NegativeTensorMap

set_option backward.privateInPublic true
set_option Elab.async false
set_option maxRecDepth 4096
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section
universe u
namespace PalomarSteiner
open OAI.AlgebraicGeometry.SheafCohomology.Projective MonoidalCategory
variable {X : Scheme.{u}}
local instance : MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

def tensorIso (M N : X.Modules) : M ⊗ N ≅ tensor M N :=
  TensorSections.monoidalTensorObjIso M N

def tensorCongr {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    tensor M N ≅ tensor M' N' :=
  Invertible.Scheme.Modules.tensorObjCongr e f

def powerIso (L : X.Modules) (F : ℕ → X.Modules)
    (h0 : F 0 ≅ 𝟙_ X.Modules) (hs : ∀ n, F (n+1) ≅ F n ⊗ L) :
    ∀ n, F n ≅ power L n
  | 0 => h0 ≪≫ TensorSections.monoidalUnitObjIso X
  | n+1 => hs n ≪≫ tensorIso (F n) L ≪≫
      tensorCongr (powerIso L F h0 hs n) (Iso.refl L)

def inverseIso {I : X.Modules} (hI : Invertible.Scheme.Modules.IsInvertible I) :
    tensor (Dual.Scheme.Modules.dualObj I) I ≅ SheafOfModules.unit X.ringCatSheaf :=
  OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso _ _ ≪≫
    InvertibleEvaluation.Scheme.Modules.invertibleEvaluationIso hI

theorem natural_iff_original (M : X.Modules) :
    HasNaturalCohomology M ↔ SteinerGeometry.SchemeModules.HasNaturalCohomology M := Iff.rfl

theorem natural_of_iso {M N : X.Modules} (e : M ≅ N)
    (h : HasNaturalCohomology M) : HasNaturalCohomology N := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun q hq => ?_⟩
  let eH := (Sheaf.functorH (Opens.grothendieckTopology X) q).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  exact (Equiv.subsingleton_congr (CategoryTheory.Iso.addCommGroupIsoToAddEquiv eH).toEquiv).1 (hd q hq)
end PalomarSteiner

namespace PalomarSteiner
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open CategoryTheory AlgebraicGeometry MonoidalCategory
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def polePowerIso (j : σ) (n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      power (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) n :=
  powerIso _ _ (Iso.refl _) (fun _ => Iso.refl _) n

def idealPowerIso (j : σ) (n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ≅
      power (IdealModule.idealModule
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) n :=
  powerIso _ _ (Iso.refl _) (fun _ => Iso.refl _) n

def lineTwistIso (j : σ) (b : ℤ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j b ≅
      lineTwist
        (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) b := by
  cases b with
  | ofNat n => exact polePowerIso j n
  | negSucc n => exact idealPowerIso j (n+1)

def steinerTwistIso {n : ℕ} (M : (SteinerGeometry.projectiveSpace R n).Modules) (b : ℤ) :
    SteinerGeometry.ProjectiveSteinerBundle.twist M b ≅
      twist
        (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) (0 : Fin (n+1))))
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) (0 : Fin (n+1))) M b :=
  tensorIso _ _ ≪≫ tensorCongr (Iso.refl M) (lineTwistIso _ b)
end PalomarSteiner

end
namespace PalomarSteiner
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe uNormalize
variable {X : Scheme.{uNormalize}}
local instance (Y : Scheme.{uNormalize}) : MonoidalCategory Y.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory Y
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type uNormalize} [CommRing R] {n t r : ℕ}

def negativeCopiesIso (R : Type uNormalize) [CommRing R] (n t : ℕ) :
    copies (ideal R n) t ≅ SteinerGeometry.projectiveTwistSum R n t (-1) :=
  Sigma.mapIso (fun _ : Fin t => (λ_ (ideal R n)).symm)

def zeroCopiesIso (R : Type uNormalize) [CommRing R] (n s : ℕ) :
    copies (SheafOfModules.unit (SteinerGeometry.projectiveSpace R n).ringCatSheaf) s ≅
      SteinerGeometry.projectiveTwistSum R n s 0 :=
  Sigma.mapIso (fun _ : Fin s =>
    (TensorSections.monoidalUnitObjIso (SteinerGeometry.projectiveSpace R n)).symm)

def normalizedMap
    (i : SteinerGeometry.projectiveTwistSum R n t (-1) ⟶
      SteinerGeometry.projectiveTwistSum R n (t+r) 0) :
    copies (ideal R n) t ⟶
      copies (SheafOfModules.unit (SteinerGeometry.projectiveSpace R n).ringCatSheaf) (t+r) :=
  (negativeCopiesIso R n t).hom ≫ i ≫ (zeroCopiesIso R n (t+r)).inv

def normalizedCokernelIso
    (i : SteinerGeometry.projectiveTwistSum R n t (-1) ⟶
      SteinerGeometry.projectiveTwistSum R n (t+r) 0) :
    cokernel (normalizedMap i) ≅ cokernel i :=
  cokernel.mapIso _ _ (negativeCopiesIso R n t) (zeroCopiesIso R n (t+r)) (by
    simp only [normalizedMap, Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem normalizedMap_shortExact
    (i : SteinerGeometry.projectiveTwistSum R n t (-1) ⟶
      SteinerGeometry.projectiveTwistSum R n (t+r) 0)
    (h : (ShortComplex.cokernelSequence i).ShortExact) :
    (ShortComplex.cokernelSequence (normalizedMap i)).ShortExact := by
  let : Mono i := h.mono_f
  let : Mono (normalizedMap i) := by dsimp [normalizedMap]; infer_instance
  exact { exact := ShortComplex.cokernelSequence_exact _
          mono_f := by change Mono (normalizedMap i); infer_instance }

theorem hasRank_of_iso {M N : X.Modules} (e : M ≅ N) {r : ℕ}
    (h : HasRank M r) : HasRank N r := by
  intro x
  obtain ⟨U, hx, ⟨i⟩⟩ := h x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ i⟩⟩

theorem normalizedMap_rank
    (i : SteinerGeometry.projectiveTwistSum R n t (-1) ⟶
      SteinerGeometry.projectiveTwistSum R n (t+r) 0)
    (h : SteinerGeometry.NaturalSteinerPresentation i) :
    HasRank (cokernel (normalizedMap i)) r :=
  hasRank_of_iso (normalizedCokernelIso i).symm h.rank
end PalomarSteiner


section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
namespace PalomarSteiner
universe u

/-- The concrete-chart representation of the original literal matrix is the
only interface step needed after the existing full geometric theorem. -/
def ChartBinding : Prop :=
  ∀ (K : Type u) [Field K] (n t r : ℕ) (M : Steiner.LinearMatrix K n t (t+r)),
    RepresentsMatrix K n t r (normalizedMap (SteinerGeometry.linearPresentation K M)) M

set_option maxHeartbeats 2000000
/-- Transport the full existing result through the concrete independently
specified sheaf constructions. -/
theorem main_result_of_chart_binding (hchart : ChartBinding.{u}) : Statement.{u} := by
  intro K _ _ n t r hn ht hr
  let j : Fin (n+1) := 0
  let P := HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j
  refine ⟨P, ⟨inverseIso (HyperplaneIdeal.MvPolynomial.coordinateHyperplaneIdealModule_isInvertible j)⟩, ?_⟩
  obtain ⟨D, hD, hM⟩ := Steiner.genericMatrixConclusion_charZero K n t r hn ht hr
  refine ⟨D, hD, ?_⟩
  intro a ha
  let M := Steiner.universalLinearMatrix K n t (t+r) a
  let i := SteinerGeometry.linearPresentation K M
  have h : SteinerGeometry.NaturalSteinerPresentation i :=
    SteinerGeometry.linearMatrix_naturalSteiner K hn ht (by omega) M (hM a ha)
  refine ⟨hM a ha, normalizedMap i, hchart K n t r M,
    normalizedMap_shortExact i h.shortExact, normalizedMap_rank i h, ?_⟩
  intro b
  exact natural_of_iso
    (steinerTwistIso (cokernel i) b ≪≫
      tensorCongr (normalizedCokernelIso i).symm (Iso.refl _))
    ((natural_iff_original _).2 (h.natural b))
end PalomarSteiner
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe uComponent vComponent
namespace GenericComponent
variable {C : Type uComponent} [Category.{vComponent} C] [Preadditive C] [HasFiniteBiproducts C]
def proj (A : C) {a : ℕ} (j : Fin a) : (∐ fun _ : Fin a => A) ⟶ A :=
  Sigma.desc (fun k => if k = j then 𝟙 A else 0)

theorem iso_inv_proj {A B : C} {a : ℕ} (e : A ≅ B) (j : Fin a) :
    (Sigma.mapIso (fun _ : Fin a => e)).inv ≫ proj A j = proj B j ≫ e.inv := by
  apply Sigma.hom_ext
  intro k
  simp only [Sigma.ι_mapIso_inv_assoc, proj, Sigma.ι_comp_desc,
    Sigma.ι_comp_desc_assoc]
  by_cases h : k = j
  · simp [h]
  · simp [h]

theorem component_conjugate {A B A' B' : C} {a b : ℕ} (eA : A ≅ A') (eB : B ≅ B')
    (f : (∐ fun _ : Fin a => A') ⟶ (∐ fun _ : Fin b => B')) (i : Fin a) (j : Fin b) :
    Sigma.ι (fun _ : Fin a => A) i ≫
      ((Sigma.mapIso (fun _ : Fin a => eA)).hom ≫ f ≫
        (Sigma.mapIso (fun _ : Fin b => eB)).inv) ≫ proj B j =
    eA.hom ≫ (Sigma.ι (fun _ : Fin a => A') i ≫ f ≫ proj B' j) ≫ eB.inv := by
  simp only [Category.assoc, Sigma.ι_mapIso_hom_assoc, iso_inv_proj]
theorem proj_eq_old (A : C) {a : ℕ} (j : Fin a) :
    proj A j = OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents.finiteCoproductProjection
      (fun _ : Fin a => A) j := by
  apply Sigma.hom_ext
  intro k
  simp only [proj,
    OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents.finiteCoproductProjection,
    biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  by_cases h : k = j
  · subst j; simp
  · simp [h]
end GenericComponent

namespace PalomarSteiner
universe uComponentScheme
variable {X : Scheme.{uComponentScheme}}
local instance (Y : Scheme.{uComponentScheme}) : MonoidalCategory Y.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory Y
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type uComponentScheme} [CommRing R] {n t r : ℕ}
theorem projection_eq_old (M : X.Modules) {a : ℕ} (j : Fin a) :
    projection M j = CoproductMatrixComponents.finiteCoproductProjection (fun _ : Fin a => M) j :=
  GenericComponent.proj_eq_old M j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem normalizedMap_component
    (i : SteinerGeometry.projectiveTwistSum R n t (-1) ⟶
      SteinerGeometry.projectiveTwistSum R n (t+r) 0)
    (a : Fin t) (b : Fin (t+r)) :
    component (normalizedMap i) a b =
      (λ_ (ideal R n)).inv ≫
      SteinerGeometry.PolynomialTopRank.originalComponent i a b ≫
      (TensorSections.monoidalUnitObjIso (SteinerGeometry.projectiveSpace R n)).hom := by
  unfold component
  rw [projection_eq_old]
  have h := GenericComponent.component_conjugate
    (A := ideal R n)
    (B := SheafOfModules.unit (SteinerGeometry.projectiveSpace R n).ringCatSheaf)
    (A' := SteinerGeometry.projectiveTwist R n (-1))
    (B' := SteinerGeometry.projectiveTwist R n 0)
    (a := t) (b := t+r)
    (λ_ (ideal R n)).symm
    (TensorSections.monoidalUnitObjIso (SteinerGeometry.projectiveSpace R n)).symm
    i a b
  simpa only [normalizedMap, negativeCopiesIso, zeroCopiesIso,
    GenericComponent.proj_eq_old, Iso.symm_hom, Iso.symm_inv,
    SteinerGeometry.PolynomialTopRank.originalComponent,
    SteinerGeometry.PolynomialTopRank.lineComponent] using h
end PalomarSteiner


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
namespace PalomarChartBridge
universe u
variable {K : Type u} [CommRing K] {σ : Type} [Fintype σ]
local instance : DecidableEq σ := Classical.decEq σ
attribute [local instance] MvPolynomial.gradedAlgebra

theorem chart_exponent (a : Fin 1 → σ) (k : σ) (hk : k ≠ a 0) :
    (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)).toAddMonoidHom
        (Finsupp.single (⟨k, hk⟩ : {j : σ // j ≠ a 0}) 1) =
    PolynomialChartMap.MvPolynomial.polynomialChartExponent a (Finsupp.single k 1) := by
  apply Subtype.ext
  ext j
  simp [LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap_apply,
    PolynomialChartMap.MvPolynomial.polynomialChartExponent, Finsupp.single_apply,
    Subtype.ext_iff]

theorem chart_dehomogenize (a : Fin 1 → σ) (p : MvPolynomial σ K) :
    AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
      (AddMonoidAlgebra.mapDomain
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)).toAddMonoidHom
        (SpaceChart.MvPolynomial.dehomogenizeAux K (a 0) p)) =
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of K), ⊤) a
      (MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom p) := by
  let L : MvPolynomial σ K →+* _ :=
    (AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm).toRingHom.comp
      ((AddMonoidAlgebra.mapDomainRingHom K
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)).toAddMonoidHom).comp
        (SpaceChart.MvPolynomial.dehomogenizeAux K (a 0)))
  let T : MvPolynomial σ K →+* _ :=
    (PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of K), ⊤) a).comp
      (MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom)
  have h : L = T := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change AddMonoidAlgebra.mapRingEquiv _ _
        (AddMonoidAlgebra.mapDomain _ (SpaceChart.MvPolynomial.dehomogenizeAux K (a 0) (MvPolynomial.C r))) =
        PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _
          (MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom (MvPolynomial.C r))
      rw [SpaceChart.MvPolynomial.dehomogenizeAux_C, MvPolynomial.map_C]
      change AddMonoidAlgebra.mapRingEquiv _ _
        (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single 0 r)) =
        PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _ (MvPolynomial.monomial 0 _)
      rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapRingEquiv_single,
        PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial]
      congr 1
      simp only [map_zero]
    · intro k
      change AddMonoidAlgebra.mapRingEquiv _ _
        (AddMonoidAlgebra.mapDomain _ (SpaceChart.MvPolynomial.dehomogenizeAux K (a 0) (MvPolynomial.X k))) =
        PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _
          (MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom (MvPolynomial.X k))
      rw [MvPolynomial.map_X]
      by_cases hk : k = a 0
      · subst k
        rw [SpaceChart.MvPolynomial.dehomogenizeAux_X_self, AddMonoidAlgebra.mapDomain_one, map_one]
        change 1 = PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _ (MvPolynomial.monomial _ _)
        rw [PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial]
        have hz : PolynomialChartMap.MvPolynomial.polynomialChartExponent a (Finsupp.single (a 0) 1) = 0 := by
          apply Subtype.ext
          ext j
          simp [PolynomialChartMap.MvPolynomial.polynomialChartExponent, Finsupp.single_apply, Ne.symm j.property]
        rw [hz]
        rfl
      · rw [SpaceChart.MvPolynomial.dehomogenizeAux_X_ne K (a 0) hk]
        change AddMonoidAlgebra.mapRingEquiv _ _
          (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ (1 : K))) =
          PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _ (MvPolynomial.monomial _ _)
        rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapRingEquiv_single,
          PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, map_one]
        rw [chart_exponent a k hk]
  exact DFunLike.congr_fun h p

def chartValueAt (i : σ)
    (p : MvPolynomial.homogeneousSubmodule σ K 1) :
    Γ(Proj (MvPolynomial.homogeneousSubmodule σ K),
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule σ K)
    (MvPolynomial.X i)
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one K i) one_pos).hom.hom
      (HomogeneousLocalization.Away.mk _
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one K i) 1 p.val (by simpa using p.property))

theorem chartRingEquiv_apply_eq (i : σ)
    (x : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X i)) :
    SpaceChart.MvPolynomial.chartRingEquiv K i x =
      SpaceChart.MvPolynomial.dehomogenizeAt K i x := rfl

set_option maxHeartbeats 300000 in
theorem chartValue_laurent (a : Fin 1 → ULift.{u} σ)
    (p : MvPolynomial.homogeneousSubmodule σ K 1) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K) (n := 0) a
      (((Proj (MvPolynomial.homogeneousSubmodule σ K)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := K) a 0)).op).hom
        (chartValueAt (a 0).down p)) =
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of K), ⊤)
      (fun k => (a k).down)
      (MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom p.val) := by
  let q := HomogeneousLocalization.Away.mk _
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one K (a 0).down)
    1 p.val (by simpa using p.property)
  let z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ K)
      (StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := K) (fun k => (a k).down)) :=
    HomogeneousLocalization.awayMap _
      (StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := K)
        (fun k => (a k).down)) rfl q
  let e := StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := K) (n := 0) a
  have hs := ConcreteCategory.congr_hom
    (StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso_naturality_firstChart
      (R := K) a) q
  change e.hom.hom z =
    (((Proj (MvPolynomial.homogeneousSubmodule σ K)).presheaf.map
      (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := K) a 0)).op).hom
      (chartValueAt (a 0).down p)) at hs
  rw [← hs]
  have hundo : e.inv.hom (e.hom.hom z) = z := by
    exact ConcreteCategory.congr_hom e.hom_inv_id z
  change AddMonoidAlgebra.mapRingEquiv _
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
    (LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv K
      (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (n := 0) (fun k => (a k).down))
      (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := K) (n := 0) (fun k => (a k).down)
        (e.inv.hom (e.hom.hom z)))) = _
  rw [hundo]
  have hl := StandardIntersectionRing.MvPolynomial.coordinateProductAwayLaurentRingEquiv_awayMap
    (R := K) (fun k => (a k).down) q
  change LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv K
    (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (n := 0) (fun k => (a k).down))
    (StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := K) (n := 0) (fun k => (a k).down) z) = _ at hl
  refine (congrArg (AddMonoidAlgebra.mapRingEquiv _
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm) hl).trans ?_
  have hd := SpaceChart.MvPolynomial.dehomogenizeAt_mk K (a 0).down (n := 1) (p := p.val)
    (by simpa using p.property : p.val ∈ MvPolynomial.homogeneousSubmodule σ K (1 • 1))
  have hd' : SpaceChart.MvPolynomial.chartRingEquiv K (a 0).down q =
      SpaceChart.MvPolynomial.dehomogenizeAux K (a 0).down p.val :=
    (chartRingEquiv_apply_eq (a 0).down q).trans hd
  exact (congrArg (fun v : MvPolynomial {j : σ // j ≠ (a 0).down} K =>
    AddMonoidAlgebra.mapRingEquiv _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
      (AddMonoidAlgebra.mapDomain
        (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap
          (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (n := 0) (fun k => (a k).down))).toAddMonoidHom v)) hd').trans
    (chart_dehomogenize (fun k => (a k).down) p.val)

end PalomarChartBridge

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PalomarCoefficient
universe u
variable {K : Type u} [CommRing K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def singleIndex (j : σ) : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 :=
  ⟨fun _ => ULift.up j, by intro a b hab; omega⟩

omit [Fintype σ] in
lemma single_intersection (j : σ) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := K) (singleIndex.{u} j).1 =
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) j := by
  rw [show StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := K) (singleIndex.{u} j).1 =
      ⨅ k : Fin 1, StandardCech.MvPolynomial.coordinateOpenCover (R := K) ((singleIndex.{u} j).1 k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Preorder.isLimitIInf _)).to_eq]
  simp only [singleIndex, iInf_const, StandardCech.MvPolynomial.coordinateOpenCover]

/-- Scalar frame equality follows by the actual Laurent comparison on the one-chart intersection. -/
theorem coefficient_eq_of_laurent (j : σ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := K) j 1 ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := K) j 0)
    (v : Γ(Proj (MvPolynomial.homogeneousSubmodule σ K),
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) j))
    (hv : StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K)
        (singleIndex.{u} j).1
        ((Proj (MvPolynomial.homogeneousSubmodule σ K)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
            (R := K) (singleIndex.{u} j).1 0)).op v) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of K), ⊤)
        (fun l => ((singleIndex.{u} j).1 l).down)
        (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
          (R := K) j 1 0 (by omega) f).val) :
    SteinerGeometry.FrameMapCoefficient.coefficient f
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) j)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := K) j j 1)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := K) j j 0) = v := by
  have h := SteinerGeometry.NegativeMapCoefficient.coefficient_on_intersection
    (R := K) j 1 0 (by omega) f 0 (singleIndex.{u} j) rfl
  rw [← NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials_apply] at h
  change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := K)
      (singleIndex.{u} j).1 _ = _ at h
  have heq := (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv
    (R := K) (singleIndex.{u} j).1).injective (h.trans hv.symm)
  have hiso : IsIso (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
      (R := K) (singleIndex.{u} j).1 0)) := by
    have he : homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
        (R := K) (singleIndex.{u} j).1 0) = eqToHom (single_intersection.{u} (K := K) j) := Subsingleton.elim _ _
    rw [he]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso
    ((Proj (MvPolynomial.homogeneousSubmodule σ K)).presheaf.map
      (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
        (R := K) (singleIndex.{u} j).1 0)).op)).injective heq
end PalomarCoefficient


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
set_option linter.defProp false

namespace PalomarSteiner.FrameNormalize
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI

theorem unit_image (X : Scheme.{u}) (U : X.Opens) :
    (TensorSections.monoidalUnitObjIso X).hom.val.app (op U)
      (PowerCancellationPairing.localMonoidalUnitSection X U) = (1 : Γ(X,U)) :=
  SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT
    (TensorSections.monoidalUnitObjIso X) (op U) (show Γ(X,U) from 1)

theorem unit_image_of_eq {X : Scheme.{u}} (U : X.Opens)
    (x : Γ(𝟙_ X.Modules,U)) (c : Γ(X,U))
    (hx : x = c • PowerCancellationPairing.localMonoidalUnitSection X U) :
    (TensorSections.monoidalUnitObjIso X).hom.val.app (op U) x = c := by
  rw [hx, map_smul, unit_image]
  exact mul_one c

theorem unitor_inv_generator {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (q : Γ(M,U)) :
    (λ_ M).inv.val.app (op U) q =
      TensorSections.tensorSection (𝟙_ X.Modules) M U
        (PowerCancellationPairing.localMonoidalUnitSection X U) q := by
  calc
    _ = (λ_ M).inv.val.app (op U)
        ((λ_ M).hom.val.app (op U)
          (TensorSections.tensorSection (𝟙_ X.Modules) M U
            (PowerCancellationPairing.localMonoidalUnitSection X U) q)) :=
      congrArg _ (SteinerGeometry.LocalTensorLeftUnitor.leftUnitor_tensorSection M U q).symm
    _ = _ := SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT
      (λ_ M).symm (op U) _

theorem normalized_generator {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (q : Γ(M,U)) (a : Γ(𝟙_ X.Modules ⊗ M,U))
    (ha : a = TensorSections.tensorSection (𝟙_ X.Modules) M U
      (PowerCancellationPairing.localMonoidalUnitSection X U) q)
    (f : 𝟙_ X.Modules ⊗ M ⟶ 𝟙_ X.Modules) :
    ((λ_ M).inv ≫ f ≫ (TensorSections.monoidalUnitObjIso X).hom).val.app (op U) q =
      (TensorSections.monoidalUnitObjIso X).hom.val.app (op U) (f.val.app (op U) a) := by
  change (TensorSections.monoidalUnitObjIso X).hom.val.app (op U)
      (f.val.app (op U) ((λ_ M).inv.val.app (op U) q)) = _
  rw [unitor_inv_generator, ← ha]

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ideal (j : σ) :=
  IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
abbrev chart (j : σ) := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
abbrev power (j : σ) (d : ℕ) :=
  TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j d

def generator (j : σ) :=
  FrameSections.overTrivializationSection (ideal (R := R) j) (chart j)
    (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization
      (R := R) j j) 1

theorem generator_one (j : σ) :
    DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j 1 =
    TensorSections.tensorSection (𝟙_ (Proj (MvPolynomial.homogeneousSubmodule σ R)).Modules)
      (ideal j) (chart j)
      (PowerCancellationPairing.localMonoidalUnitSection
        (Proj (MvPolynomial.homogeneousSubmodule σ R)) (chart j)) (generator j) := rfl

def unit_coefficient (j : σ) (x : Γ(power (R := R) j 0, chart j)) :=
  unit_image_of_eq (chart j) x
    (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j 0 x)
    (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates
      (R := R) j 0 x)

def normalizedMap (j : σ) (f : power (R := R) j 1 ⟶ power (R := R) j 0) :=
  (λ_ (ideal j)).inv ≫ f ≫
    (TensorSections.monoidalUnitObjIso (Proj (MvPolynomial.homogeneousSubmodule σ R))).hom

def normalizedMap_generator (j : σ) (f : power (R := R) j 1 ⟶ power (R := R) j 0) :=
  (normalized_generator (ideal j) (chart j) (generator j)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j 1) (generator_one j) f).trans
    ((unit_coefficient j (f.val.app (op (chart j))
      (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
        (R := R) j 1))).trans
      (SteinerGeometry.NegativeMapCoefficient.coefficient_eq_negativeChartCoefficient
        (R := R) j 1 0 f).symm)

theorem inclusion_generator (j : σ) :
    (IdealModule.idealModuleToUnit
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).val.app
        (op (chart j)) (generator j) = (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), chart j)) := by
  let X := Proj (MvPolynomial.homogeneousSubmodule σ R)
  let U := chart (R := R) j
  have h := HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization_inv_comp
    (R := R) j j
  have h' := congrArg
    (fun k => (k.val.app (op (Over.mk (𝟙 U)))) (show Γ(X,U) from 1)) h
  change (IdealModule.idealModuleToUnit
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).val.app
        (op U) (generator j) =
      (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
        (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) j j)).val.app
          (op (Over.mk (𝟙 U))) (show Γ(X,U) from 1) at h'
  rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self,
    Dual.SheafOfModules.overUnitScalarEnd_app_apply] at h'
  simpa only [map_one, one_mul] using h'

theorem exists_generator (j : σ) (f : power (R := R) j 1 ⟶ power (R := R) j 0) :
    ∃ s : Γ(ideal (R := R) j, chart j),
      (IdealModule.idealModuleToUnit
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).val.app (op (chart j)) s =
          (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), chart j)) ∧
      (normalizedMap j f).val.app (op (chart j)) s =
        SteinerGeometry.FrameMapCoefficient.coefficient f (chart j)
          (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j 1)
          (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j 0) := by
  exact ⟨generator j, inclusion_generator j, normalizedMap_generator j f⟩

end PalomarSteiner.FrameNormalize

noncomputable section
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 1500
namespace PalomarHP
universe uHP
variable {K : Type uHP} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coefficient_polynomial (n t r : ℕ) (M : Steiner.LinearMatrix K n t (t+r))
    (a : Fin t) (b : Fin (t+r)) :
    (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
      (R := K) (0 : Fin (n+1)) 1 0 (by omega)
      (SteinerGeometry.PolynomialTopRank.originalComponent
        (SteinerGeometry.linearPresentation K M) a b)).val =
      MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom (M a b).val := by
  letI := SteinerGeometry.coefficientField K
  have hraw := SteinerGeometry.LiteralSteinerPolynomial.originalComponent_polynomial
    (R := K) (Steiner.linearMatrixExtend (SteinerGeometry.specCoefficientMap K) M) a b
  have hval : (Steiner.linearMatrixExtend (SteinerGeometry.specCoefficientMap K) M a b).val =
      MvPolynomial.map (Scheme.ΓSpecIso (.of K)).inv.hom (M a b).val := rfl
  exact hraw.trans hval
end PalomarHP
