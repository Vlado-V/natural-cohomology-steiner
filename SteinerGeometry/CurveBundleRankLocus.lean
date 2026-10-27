import SteinerGeometry.CurveLocalCoordinates
import SteinerGeometry.CurveMatrixRankOpen

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {K : Type} [Field K] {C : Scheme} {X : Type}

local instance curveBundleRankLocusBiproducts (Y : Scheme) : HasFiniteBiproducts Y.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The unique lift of a rational point to an open containing it. -/
def pointInOpen (a : Spec (.of K) ⟶ C) (U : C.Opens)
    (hx : a (⊥ : PrimeSpectrum K) ∈ U) : Spec (.of K) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι a (by
    rintro _ ⟨z, rfl⟩
    have hz : a z ∈ U := by
      simpa only [Subsingleton.elim z (⊥ : PrimeSpectrum K)] using hx
    exact ⟨⟨a z, hz⟩, rfl⟩)

theorem pointInOpen_fac (a : Spec (.of K) ⟶ C) (U : C.Opens)
    (hx : a (⊥ : PrimeSpectrum K) ∈ U) : pointInOpen a U hx ≫ U.ι = a :=
  IsOpenImmersion.lift_fac _ _ _

/-- Actual local bundle frames supply the regular matrices used in the curve
rank-locus argument; no rank-open or genericity hypothesis is assumed. -/
def bundleLocalSectionMatrix
    (p : C ⟶ Spec (.of K)) (E : C.Modules)
    (a : X → (Spec (.of K) ⟶ C)) (ha : ∀ x, a x ≫ p = 𝟙 _)
    (U : C.Opens) (n : ℕ)
    (frame : (Scheme.Modules.pullback U.ι).obj E ≅
      ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf)
    {k : ℕ} (s : Fin k → (sectionFunctor p).obj E) :
    LocalSectionMatrix C (fun x => a x (⊥ : PrimeSpectrum K))
      (fun x => sectionEvaluation p E (a x)) s := by
  let b (x : X) (hx : a x (⊥ : PrimeSpectrum K) ∈ U) := pointInOpen (a x) U hx
  have hb (x : X) (hx : a x (⊥ : PrimeSpectrum K) ∈ U) :
      b x hx ≫ (U.ι ≫ p) = 𝟙 _ := by
    rw [← Category.assoc, pointInOpen_fac, ha]
  let c (x : X) (hx : a x (⊥ : PrimeSpectrum K) ∈ U) :=
    localFiberCoordinatesAt p U.ι (b x hx) (hb x hx) (a x)
      (pointInOpen_fac (a x) U hx) E n frame
  refine LocalSectionMatrix.of_frame_coordinates _ _ s U
    (localRegularCoordinates p U.ι E n frame) b ?_ c ?_
  · intro x hx
    exact congrArg (fun f : Spec (.of K) ⟶ C => f (⊥ : PrimeSpectrum K))
      (pointInOpen_fac (a x) U hx)
  · intro x hx v
    exact localFiberCoordinatesAt_evaluation p U.ι (b x hx) (hb x hx) (a x)
      (pointInOpen_fac (a x) U hx) E n frame v

/-- Finite rank drop for canonical sections of a genuine vector bundle on
an integral Noetherian curve. Local triviality is stated using actual
pullbacks and actual finite free sheaves. -/
theorem bundle_hasFiniteRankDrop [IsIntegral C] [IsNoetherian C]
    (hd : topologicalKrullDim C ≤ 1)
    (p : C ⟶ Spec (.of K)) (E : C.Modules)
    (a : X → (Spec (.of K) ⟶ C)) (ha : ∀ x, a x ≫ p = 𝟙 _)
    (hinj : Function.Injective (fun x => a x (⊥ : PrimeSpectrum K)))
    (hframe : ∀ x : X, ∃ (U : C.Opens) (n : ℕ),
      a x (⊥ : PrimeSpectrum K) ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
          ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    HasFiniteRankDrop (fun x => sectionEvaluation p E (a x)) := by
  apply hasFiniteRankDrop_of_local_section_matrices hd _ hinj
  intro k s x _
  obtain ⟨U, n, hx, ⟨frame⟩⟩ := hframe x
  exact ⟨bundleLocalSectionMatrix p E a ha U n frame s, hx⟩

/-- A globally generated rank-`n` algebraic vector bundle on an integral
Noetherian curve has one fixed `n+1` tuple of actual global sections spanning
every rational fiber. The sections and evaluations are the genuine sheaf
objects; rank-drop finiteness is proved from local regular matrices. -/
theorem exists_bundle_rank_succ_generators [Infinite K]
    [IsIntegral C] [IsNoetherian C] [Nonempty X]
    (hd : topologicalKrullDim C ≤ 1)
    (p : C ⟶ Spec (.of K)) (E : C.Modules)
    (a : X → (Spec (.of K) ⟶ C)) (ha : ∀ x, a x ≫ p = 𝟙 _)
    (hinj : Function.Injective (fun x => a x (⊥ : PrimeSpectrum K)))
    (n : ℕ) (hn : 0 < n)
    (hframe : ∀ x : X, ∃ U : C.Opens,
      a x (⊥ : PrimeSpectrum K) ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
          ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hgenerated : ∀ x, Function.Surjective (sectionEvaluation p E (a x))) :
    ∃ s : Fin (n + 1) → (sectionFunctor p).obj E,
      ∀ x, Submodule.span K (Set.range (fun i => sectionEvaluation p E (a x) (s i))) = ⊤ := by
  classical
  let e (x : X) : (sectionFunctor (a x ≫ p)).obj
      ((Scheme.Modules.pullback (a x)).obj E) ≃ₗ[K] (Fin n → K) := Classical.choice (by
    obtain ⟨U, hx, ⟨frame⟩⟩ := hframe x
    have hb : pointInOpen (a x) U hx ≫ (U.ι ≫ p) = 𝟙 _ := by
      rw [← Category.assoc, pointInOpen_fac, ha]
    exact ⟨localFiberCoordinatesAt p U.ι (pointInOpen (a x) U hx) hb (a x)
      (pointInOpen_fac (a x) U hx) E n frame⟩)
  let : ∀ x, FiniteDimensional K ((sectionFunctor (a x ≫ p)).obj
      ((Scheme.Modules.pullback (a x)).obj E)) :=
    fun x => FiniteDimensional.of_injective (e x).toLinearMap (e x).injective
  have hdim (x : X) : Module.finrank K ((sectionFunctor (a x ≫ p)).obj
      ((Scheme.Modules.pullback (a x)).obj E)) = n := by
    rw [(e x).finrank_eq]
    simp
  exact exists_rank_succ_generators (fun x => sectionEvaluation p E (a x))
    hgenerated n hn hdim
    (bundle_hasFiniteRankDrop hd p E a ha hinj (fun x => by
      obtain ⟨U, hx, hf⟩ := hframe x
      exact ⟨U, n, hx, hf⟩)) (Classical.choice inferInstance)

end
end SteinerGeometry
