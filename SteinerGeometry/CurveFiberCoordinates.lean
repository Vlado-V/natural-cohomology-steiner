module

public import SteinerGeometry.CurveSectionFunctor
public import SteinerGeometry.CurveFrameNaturality
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {K : Type} [Field K] {C : Scheme}

local instance curveFiberCoordinatesBiproducts (C : Scheme) : HasFiniteBiproducts C.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Global functions on the field point, viewed over that same field. -/
def pointUnitCoordinates (q : Spec (.of K) ⟶ Spec (.of K)) (h : q = 𝟙 _) :
    (sectionFunctor q).obj
      (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) ≃ₗ[K] K where
  toFun := (Scheme.ΓSpecIso (.of K)).hom
  invFun := (Scheme.ΓSpecIso (.of K)).inv
  left_inv s := by
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of K)) (show Γ(Spec (.of K), ⊤) from s)
  right_inv s := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of K)) s
  map_add' := map_add _
  map_smul' r s := by
    subst q
    change (Scheme.ΓSpecIso (.of K)).hom
      (((Scheme.ΓSpecIso (.of K)).inv r) * (show Γ(Spec (.of K), ⊤) from s)) =
        r * (Scheme.ΓSpecIso (.of K)).hom s
    simp

/-- The fiber of the structure sheaf at a rational point has its canonical
one-dimensional coordinate over the ground field. -/
def fiberUnitCoordinates (p : C ⟶ Spec (.of K)) (a : Spec (.of K) ⟶ C)
    (h : a ≫ p = 𝟙 _) :
    (sectionFunctor (a ≫ p)).obj
      ((Scheme.Modules.pullback a).obj (SheafOfModules.unit C.ringCatSheaf)) ≃ₗ[K] K :=
  ((sectionFunctor (a ≫ p)).mapIso (Line.Bundles.structureModulePullbackIso a)).toLinearEquiv.trans
    (pointUnitCoordinates (a ≫ p) h)

theorem fiberUnitCoordinates_evaluation (p : C ⟶ Spec (.of K))
    (a : Spec (.of K) ⟶ C) (h : a ≫ p = 𝟙 _)
    (s : (sectionFunctor p).obj (SheafOfModules.unit C.ringCatSheaf)) :
    fiberUnitCoordinates p a h (sectionEvaluation p _ a s) =
      (Scheme.ΓSpecIso (.of K)).hom (a.appTop s) := by
  have he := congrArg (fun f => f.app ⊤ s)
    (Tensor.PullbackUnits.structureModulePullbackIso_unit a)
  change (Scheme.ΓSpecIso (.of K)).hom
    ((Line.Bundles.structureModulePullbackIso a).hom.app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app _).app ⊤ s)) = _
  exact congrArg (fun z => (Scheme.ΓSpecIso (.of K)).hom z) he

/-- A bundle frame induces actual linear coordinates on every rational fiber. -/
def fiberFrameCoordinates (p : C ⟶ Spec (.of K)) (a : Spec (.of K) ⟶ C)
    (h : a ≫ p = 𝟙 _) (E : C.Modules) (n : ℕ)
    (frame : E ≅ ⨁ fun _ : Fin n => SheafOfModules.unit C.ringCatSheaf) :
    (sectionFunctor (a ≫ p)).obj ((Scheme.Modules.pullback a).obj E) ≃ₗ[K]
      (Fin n → K) := by
  let G := Scheme.Modules.pullback a ⋙ sectionFunctor (a ≫ p)
  exact (G.mapIso frame).toLinearEquiv.trans
    ((biproductCoordinates G _ (Fin n)).trans
      (LinearEquiv.piCongrRight fun _ => fiberUnitCoordinates p a h))

/-- In a genuine global frame, taking the fiber evaluates each regular
coefficient by the point's map on functions. -/
theorem fiberFrameCoordinates_evaluation (p : C ⟶ Spec (.of K))
    (a : Spec (.of K) ⟶ C) (h : a ≫ p = 𝟙 _) (E : C.Modules) (n : ℕ)
    (frame : E ≅ ⨁ fun _ : Fin n => SheafOfModules.unit C.ringCatSheaf)
    (s : (sectionFunctor p).obj E) :
    fiberFrameCoordinates p a h E n frame (sectionEvaluation p E a s) =
      fun i => (Scheme.ΓSpecIso (.of K)).hom
        (a.appTop (biproductCoordinates (sectionFunctor p) _ (Fin n)
          ((sectionFunctor p).map frame.hom s) i)) := by
  let G := Scheme.Modules.pullback a ⋙ sectionFunctor (a ≫ p)
  have he := frameCoordinates_semilinear_natural (sectionFunctor p) G (RingHom.id K)
    (fun M => sectionEvaluation p M a)
    (fun f s => sectionEvaluation_natural p f a s) _ E (Fin n) frame s
  change (fun i => fiberUnitCoordinates p a h
      (biproductCoordinates G _ (Fin n) (G.map frame.hom (sectionEvaluation p E a s)) i)) = _
  funext i
  exact (congrArg (fun z => fiberUnitCoordinates p a h (z i)) he).trans
    (fiberUnitCoordinates_evaluation p a h _)

end
end SteinerGeometry
