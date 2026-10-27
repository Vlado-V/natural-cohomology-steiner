import SteinerGeometry.CoproductMatrix
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectIso

/-! Actual projective module morphisms encoded by matrices of linear forms. -/

noncomputable section
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective

namespace SteinerGeometry

universe u v


section Projective
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance polynomialPresentationFiniteBiproducts
    (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual finite sum of negative twists on projective space. -/
abbrev negativeTwistSum (j : σ) {r : ℕ} (d : Fin r → ℕ) :=
  ∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)

/-- Matrices of homogeneous forms are in bijection with actual morphisms between
finite sums of ordered negative twists. -/
def negativeTwistPolynomialMatrixEquiv (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k) :
    (negativeTwistSum (R := R) j e ⟶ negativeTwistSum (R := R) j d) ≃
      (∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i)) :=
  finiteCoproductEncodedMatrixEquiv _ _ fun i k =>
    NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
      j (e k) (d i) (hde i k)

/-- Actual sheaf morphism associated with a homogeneous polynomial matrix. -/
def negativeTwistPolynomialMap (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k)
    (P : ∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i)) :
    negativeTwistSum (R := R) j e ⟶ negativeTwistSum (R := R) j d :=
  (negativeTwistPolynomialMatrixEquiv j d e hde).symm P

/-- The encoding assembles the component maps into the actual finite sum map. -/
theorem negativeTwistPolynomialMap_eq_finiteCoproduct (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k)
    (P : ∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i)) :
    negativeTwistPolynomialMap j d e hde P =
      finiteCoproductFromMatrix
        (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
          (R := R) j (e k))
        (fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
          (R := R) j (d i))
        (fun i k => (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
          (R := R) j (e k) (d i) (hde i k)).symm (P i k)) :=
  finiteCoproductEncodedMatrixEquiv_symm_apply _ _ _ _

@[reassoc]
theorem negativeTwistPolynomialMap_component (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k)
    (P : ∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i))
    (k : Fin s) (i : Fin r) :
    Sigma.ι (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
      (R := R) j (e k)) k ≫ negativeTwistPolynomialMap (R := R) j d e hde P ≫
      CoproductMatrixComponents.finiteCoproductProjection
        (fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
          (R := R) j (d i)) i =
    (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
      (R := R) j (e k) (d i) (hde i k)).symm (P i k) := by
  rw [negativeTwistPolynomialMap_eq_finiteCoproduct]
  exact finiteCoproductFromMatrix_component _ _ _ k i

@[simp]
theorem negativeTwistPolynomialMap_matrix (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k)
    (P : ∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i)) :
    NegativeTwistPolynomialMatrix.MvPolynomial.coordinateNegativeTwistPolynomialMatrix j d e hde
      (negativeTwistPolynomialMap j d e hde P) = P :=
  (negativeTwistPolynomialMatrixEquiv j d e hde).apply_symm_apply P

/-- Twisted global sections of the geometric presentation really are multiplication
by the supplied matrix of polynomials. -/
theorem negativeTwistPolynomialMap_sections (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k)
    (P : ∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i))
    (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence
        (R := R) j n).functor.obj (negativeTwistSum (R := R) j e))) (i : Fin r) :
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j d n hd).hom
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence
          (R := R) j n).functor.map (negativeTwistPolynomialMap j d e hde P)) x)).val i =
      ∑ k, (P i k).val *
        ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j e n he).hom x).val k := by
  have h := TwistedCoproductPolynomialMap.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso_map_component
    j d e hde n hd he (negativeTwistPolynomialMap j d e hde P) x i
  simpa only [negativeTwistPolynomialMap_matrix] using h

/-- The homogeneous polynomial source and target spaces for a twist. -/
abbrev weightedPolynomialPiece {r : ℕ} (d : Fin r → ℕ) (n : ℕ) :=
  OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading
    (σ := σ) Γ(Spec (CommRingCat.of R), ⊤) (fun i => (d i : ℤ)) (n : ℤ)

/-- Eventual surjectivity of the literal polynomial matrices gives an epimorphism
of actual module sheaves. The hypothesis is only about homogeneous polynomial
vectors; no stalk or sheaf surjectivity is assumed. -/
theorem negativeTwistPolynomialMap_epi [IsNoetherianRing R]
    (j : σ) {r s : ℕ} (d : Fin r → ℕ) (e : Fin s → ℕ)
    (hde : ∀ i k, d i ≤ e k)
    (P : ∀ i k, MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i))
    (b : ℕ) (hd : ∀ i, d i ≤ b) (he : ∀ k, e k ≤ b)
    (hsurj : ∀ n : ℕ, b ≤ n → ∀ y : weightedPolynomialPiece (R := R) (σ := σ) d n,
      ∃ x : weightedPolynomialPiece (R := R) (σ := σ) e n,
        ∀ i, y.val i = ∑ k, (P i k).val * x.val k) :
    Epi (negativeTwistPolynomialMap j d e hde P) := by
  let src := fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)
  let tgt := fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  have hsrc (k) : (src k).IsFinitePresentation :=
    InvertibleFinitePresentation.invertible_finitePresentation
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (e k))
  have htgt (i) : (tgt i).IsFinitePresentation :=
    InvertibleFinitePresentation.invertible_finitePresentation
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (d i))
  let : (negativeTwistSum (R := R) j e).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct src (fun k => by let := hsrc k; infer_instance)
  let : (negativeTwistSum (R := R) j d).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct tgt (fun i => by let := htgt i; infer_instance)
  let : (negativeTwistSum (R := R) j d).IsFiniteType :=
    Quasicoherent.Scheme.Modules.isFiniteType_fin_coproduct tgt
      (fun i => by let := htgt i; infer_instance) (fun i => by let := htgt i; infer_instance)
  apply TwistedSectionsDetectIso.MvPolynomial.finiteType_epi_of_eventually_twistedSections_surjective
    (negativeTwistPolynomialMap j d e hde P) j b
  intro n hn y
  have hdn : ∀ i, d i ≤ n := fun i => (hd i).trans hn
  have hen : ∀ k, e k ≤ n := fun k => (he k).trans hn
  let es := TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso
    (R := R) j e n hen
  let et := TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso
    (R := R) j d n hdn
  obtain ⟨x, hx⟩ := hsurj n hn (et.hom y)
  refine ⟨es.inv x, ?_⟩
  apply et.toLinearEquiv.injective
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  change (et.hom _).val i = (et.hom y).val i
  have hmap := negativeTwistPolynomialMap_sections j d e hde P n hdn hen (es.inv x) i
  calc
    _ = ∑ k, (P i k).val * (es.hom (es.inv x)).val k := hmap
    _ = (et.hom y).val i := by
      simpa only [Iso.inv_hom_id_apply] using (hx i).symm

end Projective
end SteinerGeometry
