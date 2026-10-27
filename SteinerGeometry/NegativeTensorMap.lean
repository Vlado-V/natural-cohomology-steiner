module

public import SteinerGeometry.NegativeMapCoefficient
public import SteinerGeometry.LocalTensorCoherence
public import SteinerGeometry.LocalTensorLeftUnitor
public import SteinerGeometry.LocalTensorSwapUnit
public import SteinerGeometry.TensorSwapUnitIso
public import SteinerGeometry.NegativePowerTensorIso
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorConjugatedMapSections

set_option backward.privateInPublic true
@[expose] public section

/-! Negative tensor twists preserve the chart coefficient of a linear map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
set_option linter.defProp false
namespace SteinerGeometry.NegativeTensorMap
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI
local instance negativeTensorSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

/-- Use the native negative-power monoidal presentation before specializing the scheme. -/
private theorem tensorConjugatedMap_section_native {X : Scheme.{u}}
    {A B T P Q : X.Modules} (e : A ⊗ T ≅ P) (d : B ⊗ T ≅ Q) (f : A ⟶ B)
    (U : X.Opens) (a : Γ(A,U)) (b : Γ(B,U)) (t : Γ(T,U))
    (p : Γ(P,U)) (q : Γ(Q,U)) (c : Γ(X,U))
    (he : e.hom.val.app (op U) (TensorSections.tensorSection A T U a t) = p)
    (hd : d.hom.val.app (op U) (TensorSections.tensorSection B T U b t) = q)
    (hf : f.val.app (op U) a = c • b) :
    (TensorConjugatedMapSections.tensorConjugatedMap e d f).val.app (op U) p = c • q := by
  exact TensorConjugatedMapSections.tensorConjugatedMap_section e d f U a b t p q c he hd hf

private theorem tensorConjugatedMap_section_native_of_eq {X : Scheme.{u}}
    {A B T P Q : X.Modules} (e : A ⊗ T ≅ P) (d : B ⊗ T ≅ Q) (f : A ⟶ B)
    (g : P ⟶ Q) (hg : g = TensorConjugatedMapSections.tensorConjugatedMap e d f)
    (U : X.Opens) (a : Γ(A,U)) (b : Γ(B,U)) (t : Γ(T,U))
    (p : Γ(P,U)) (q : Γ(Q,U)) (c : Γ(X,U))
    (he : e.hom.val.app (op U) (TensorSections.tensorSection A T U a t) = p)
    (hd : d.hom.val.app (op U) (TensorSections.tensorSection B T U b t) = q)
    (hf : f.val.app (op U) a = c • b) :
    g.val.app (op U) p = c • q := by
  rw [hg]
  exact tensorConjugatedMap_section_native e d f U a b t p q c he hd hf

private theorem swapUnitIso_tensorSection_of_generators {X : Scheme.{u}}
    (M N : X.Modules) (U : X.Opens) (q : Γ(M, U))
    (g0 : Γ(𝟙_ X.Modules, U)) (g1 : Γ(𝟙_ X.Modules ⊗ M, U))
    (gN : Γ(N, U)) (gS : Γ(N ⊗ M, U))
    (h0 : g0 = PowerCancellationPairing.localMonoidalUnitSection X U)
    (h1 : g1 = TensorSections.tensorSection (𝟙_ X.Modules) M U g0 q)
    (hS : gS = TensorSections.tensorSection N M U gN q) :
    (TensorSwapUnitIso.iso M N).hom.val.app (op U)
      (TensorSections.tensorSection (𝟙_ X.Modules ⊗ M) N U g1 gN) = gS := by
  rw [h1, h0, hS]
  exact LocalTensorSwapUnit.iso_tensorSection M N U q gN

abbrev power (j : σ) (d : ℕ) :=
  TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j d

def sourceIso (j : σ) (d : ℕ) :=
  NegativePowerTensorIso.iso (R := R) j d

def map (j : σ) (d : ℕ) (f : power (R := R) j 1 ⟶ power (R := R) j 0) :=
  TensorConjugatedMapSections.tensorConjugatedMap (sourceIso j d) (λ_ (power j d)) f

def rawMap (j : σ) (d : ℕ) (f : power (R := R) j 1 ⟶ power (R := R) j 0) :=
  TensorConjugatedMapSections.tensorConjugatedMap
    (TensorSwapUnitIso.iso
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (power (R := R) j d))
    (λ_ (power (R := R) j d)) f

theorem map_eq_raw (j : σ) (d : ℕ)
    (f : power (R := R) j 1 ⟶ power (R := R) j 0) :
    map j d f = rawMap j d f := rfl

def coefficientFor (j : σ) (d : ℕ)
    (h : power (R := R) j (d+1) ⟶ power (R := R) j d) :=
  FrameMapCoefficient.coefficient h
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
      (R := R) j j (d+1))
    (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
      (R := R) j j d)

theorem coefficientFor_eq_chart (j : σ) (d : ℕ)
    (h : power (R := R) j (d+1) ⟶ power (R := R) j d) :
    coefficientFor j d h =
      NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j d
        (h.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
          (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
            (R := R) j (d+1))) :=
  NegativeMapCoefficient.coefficient_eq_negativeChartCoefficient (R := R) j (d+1) d h

theorem coefficient_map_eq_raw (j : σ) (d : ℕ)
    (f : power (R := R) j 1 ⟶ power (R := R) j 0) :
    coefficientFor j d (map j d f) = coefficientFor j d (rawMap j d f) :=
  congrArg (coefficientFor j d) (map_eq_raw j d f)



private theorem generator_zero (j : σ) :
    DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j 0 = PowerCancellationPairing.localMonoidalUnitSection
        (Proj (MvPolynomial.homogeneousSubmodule σ R))
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) := rfl

private theorem generator_succ (j : σ) (d : ℕ) :
    DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j (d + 1) =
      TensorSections.tensorSection _ _ _
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
          (R := R) j d)
        (FrameSections.overTrivializationSection
          (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
          (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization
            (R := R) j j) 1) := rfl

/-- The canonical negative-twist generators are preserved by the source isomorphism.
The inferred proof type preserves the native module presentations. -/
def sourceIso_generator (j : σ) (d : ℕ) :=
  swapUnitIso_tensorSection_of_generators
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (power (R := R) j d)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (FrameSections.overTrivializationSection
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization
        (R := R) j j) 1)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j 0)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j 1)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j d)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j (d + 1))
    (generator_zero j) (generator_succ j 0) (generator_succ j d)



def map_generator (j : σ) (d : ℕ)
    (f : power (R := R) j 1 ⟶ power (R := R) j 0) :
    let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    let g (n : ℕ) :=
      DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
        (R := R) j n
    let c := NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j 0
      (f.val.app (op U) (g 1))
    (map j d f).val.app (op U) (g (d + 1)) = c • g d := by
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let g (n : ℕ) := DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
    (R := R) j n
  let c := NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j 0
    (f.val.app (op U) (g 1))
  have hd := LocalTensorLeftUnitor.leftUnitor_tensorSection (power (R:=R) j d) U (g d)
  have hf := NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates
      (R := R) j 0 (f.val.app (op U) (g 1))
  exact tensorConjugatedMap_section_native_of_eq
    (TensorSwapUnitIso.iso
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R:=R) j))
      (power (R:=R) j d))
    (λ_ (power j d)) f (map j d f) (map_eq_raw j d f) U
    (g 1) (g 0) (g d) (g (d + 1)) (g d) c
    (sourceIso_generator j d) hd hf


private theorem coefficient_smul_generator (j : σ) (d : ℕ)
    (c : Γ(Proj (MvPolynomial.homogeneousSubmodule σ R),
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j d
      (c • DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
        (R := R) j d) = c := by
  rw [NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient_smul,
    NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient_generator,
    mul_one]

def scalar_generator (j : σ) (d : ℕ)
    (f : power (R := R) j 1 ⟶ power (R := R) j 0) :=
  (congrArg
    (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j d)
    (map_generator j d f)).trans
    (coefficient_smul_generator (R := R) j d
      (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j 0
        (f.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
          (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
            (R := R) j 1))))


/-- Negative tensor twisting preserves the coefficient in the canonical chart frames. -/
def coefficient_map (j : σ) (d : ℕ)
    (f : power (R := R) j 1 ⟶ power (R := R) j 0) :=
  (coefficientFor_eq_chart (R := R) j d (map j d f)).trans
    ((scalar_generator j d f).trans
      (coefficientFor_eq_chart (R := R) j 0 f).symm)

end SteinerGeometry.NegativeTensorMap
