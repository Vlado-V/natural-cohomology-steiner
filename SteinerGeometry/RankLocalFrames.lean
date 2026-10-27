module

public import SteinerGeometry.FiniteLocalFrames
public import SteinerGeometry.CurveBundleRankLocus
public import Mathlib.Data.Fintype.EquivFin

set_option backward.privateInPublic true
@[expose] public section

/-! # Prescribed finite rank on rational-point neighborhoods -/
noncomputable section
namespace SteinerGeometry
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

variable {K : Type} [Field K] {C : Scheme}

local instance rankLocalFrames_hasFiniteBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Reindex a finite free sheaf by the standard finite set of its cardinality. -/
def freeFinFrame (X : Scheme) (I : Type) [Fintype I] :
    (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ⨁ fun _ : Fin (Fintype.card I) => SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso (Fintype.equivFin I).toIso ≪≫
    (biproduct.isoCoproduct (C := X.Modules)
      (fun _ : Fin (Fintype.card I) => SheafOfModules.unit X.ringCatSheaf)).symm

/-- A finite frame near a rational point has the rank of the actual fiber.
This supplies the precise `Fin n` frame required by the curve generator theorem. -/
theorem finiteFrame_of_fiber_finrank
    (p : C ⟶ Spec (.of K)) (M : C.Modules)
    (D : TildeFiniteProjective.FiniteGeometricFrameCover M)
    (a : Spec (.of K) ⟶ C) (ha : a ≫ p = 𝟙 _) (n : ℕ)
    (hn : Module.finrank K ((sectionFunctor (a ≫ p)).obj
      ((Scheme.Modules.pullback a).obj M)) = n) :
    ∃ U : C.Opens, a (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  classical
  obtain ⟨i, hi⟩ := (IsOpenCover.mk D.covers).exists_mem (a (⊥ : PrimeSpectrum K))
  let := D.finite i
  let : Fintype (D.Q i) := Fintype.ofFinite _
  let m := Fintype.card (D.Q i)
  let e : (Scheme.Modules.pullback (D.U i).ι).obj M ≅
      ⨁ fun _ : Fin m => SheafOfModules.unit (D.U i).toScheme.ringCatSheaf :=
    D.frame i ≪≫ freeFinFrame _ _
  have hb : pointInOpen a (D.U i) hi ≫ ((D.U i).ι ≫ p) = 𝟙 _ := by
    rw [← Category.assoc, pointInOpen_fac, ha]
  let ef := localFiberCoordinatesAt p (D.U i).ι (pointInOpen a (D.U i) hi) hb a
    (pointInOpen_fac a (D.U i) hi) M m e
  have hm : m = n := by
    have hdim := ef.finrank_eq
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    exact hdim.symm.trans hn
  refine ⟨D.U i, hi, ?_⟩
  rw [← hm]
  exact ⟨e⟩

end SteinerGeometry
