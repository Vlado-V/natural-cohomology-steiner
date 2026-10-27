import SteinerGeometry.CurveFiberCoordinates
import SteinerGeometry.CurveOpenFiber

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {K : Type} [Field K] {C U : Scheme}

local instance curveLocalCoordinatesBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The fiber coordinates of a locally framed bundle, computed by first
restricting the bundle to a neighbourhood of the selected point. -/
def localFiberCoordinates (p : C ⟶ Spec (.of K)) (j : U ⟶ C)
    (b : Spec (.of K) ⟶ U) (h : b ≫ (j ≫ p) = 𝟙 _)
    (E : C.Modules) (n : ℕ)
    (frame : (Scheme.Modules.pullback j).obj E ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit U.ringCatSheaf) :
    (sectionFunctor ((b ≫ j) ≫ p)).obj
      ((Scheme.Modules.pullback (b ≫ j)).obj E) ≃ₗ[K] (Fin n → K) := by
  let F := sectionFunctor ((b ≫ j) ≫ p)
  exact ((F.mapIso ((Scheme.Modules.pullbackComp b j).symm.app E)).toLinearEquiv).trans
    (fiberFrameCoordinates (j ≫ p) b h _ n frame)

/-- The regular coefficients of an ambient section in a frame on a chart. -/
def localRegularCoordinates (p : C ⟶ Spec (.of K)) (j : U ⟶ C)
    (E : C.Modules) (n : ℕ)
    (frame : (Scheme.Modules.pullback j).obj E ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit U.ringCatSheaf)
    (s : (sectionFunctor p).obj E) : Fin n → Γ(U, ⊤) :=
  biproductCoordinates (sectionFunctor (j ≫ p)) _ (Fin n)
    ((sectionFunctor (j ≫ p)).map frame.hom (sectionEvaluation p E j s))

/-- The local frame compares canonical fiber evaluations with the same
regular coefficient functions used to form the rank-minor matrix. -/
theorem localFiberCoordinates_evaluation (p : C ⟶ Spec (.of K)) (j : U ⟶ C)
    (b : Spec (.of K) ⟶ U) (h : b ≫ (j ≫ p) = 𝟙 _)
    (E : C.Modules) (n : ℕ)
    (frame : (Scheme.Modules.pullback j).obj E ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit U.ringCatSheaf)
    (s : (sectionFunctor p).obj E) :
    localFiberCoordinates p j b h E n frame (sectionEvaluation p E (b ≫ j) s) =
      fun i => (Scheme.ΓSpecIso (.of K)).hom
        (b.appTop (localRegularCoordinates p j E n frame s i)) := by
  change fiberFrameCoordinates (j ≫ p) b h _ n frame
    (((Scheme.Modules.pullbackComp b j).inv.app E).app ⊤
      (sectionEvaluation p E (b ≫ j) s)) = _
  rw [← sectionEvaluation_comp]
  exact fiberFrameCoordinates_evaluation (j ≫ p) b h _ n frame _

/-- Rewrite a local fiber frame along the point's factorization identity. -/
def localFiberCoordinatesAt (p : C ⟶ Spec (.of K)) (j : U ⟶ C)
    (b : Spec (.of K) ⟶ U) (h : b ≫ (j ≫ p) = 𝟙 _)
    (a : Spec (.of K) ⟶ C) (ha : b ≫ j = a)
    (E : C.Modules) (n : ℕ)
    (frame : (Scheme.Modules.pullback j).obj E ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit U.ringCatSheaf) :
    (sectionFunctor (a ≫ p)).obj ((Scheme.Modules.pullback a).obj E) ≃ₗ[K]
      (Fin n → K) :=
  ha ▸ localFiberCoordinates p j b h E n frame

theorem localFiberCoordinatesAt_evaluation (p : C ⟶ Spec (.of K)) (j : U ⟶ C)
    (b : Spec (.of K) ⟶ U) (h : b ≫ (j ≫ p) = 𝟙 _)
    (a : Spec (.of K) ⟶ C) (ha : b ≫ j = a)
    (E : C.Modules) (n : ℕ)
    (frame : (Scheme.Modules.pullback j).obj E ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit U.ringCatSheaf)
    (s : (sectionFunctor p).obj E) :
    localFiberCoordinatesAt p j b h a ha E n frame (sectionEvaluation p E a s) =
      fun i => (Scheme.ΓSpecIso (.of K)).hom
        (b.appTop (localRegularCoordinates p j E n frame s i)) := by
  subst a
  exact localFiberCoordinates_evaluation p j b h E n frame s

end
end SteinerGeometry
