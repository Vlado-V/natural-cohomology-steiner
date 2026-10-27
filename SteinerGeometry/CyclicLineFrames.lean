module

public import SteinerGeometry.CyclicFiberSplitting
public import SteinerGeometry.RankLocalFrames
public import SteinerGeometry.SectionFunctorComparison

set_option backward.privateInPublic true
@[expose] public section

/-! Exact rank-n local frames of the actual cyclic-isogeny direct image. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance cyclicLineFramesBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]
    [IsLocallyNoetherian q.target.scheme.left]

omit [NeZero n] in
/-- The actual direct image is locally free. -/
theorem linePushforward_locallyFree (A : Line.Bundles.LineBundle D.scheme.left) :
    (q.linePushforward A).IsLocallyFree :=
  SteinerGeometry.linePushforward_locallyFree q.map.hom.left A

/-- At every rational point the direct image has a local frame indexed by Fin n. -/
theorem linePushforward_rankFrames {K : Type} [Field K] [IsAlgClosed K]
    (A : Line.Bundles.LineBundle D.scheme.left)
    (p : q.target.scheme.left ⟶ Spec (.of K))
    (a : Spec (.of K) ⟶ q.target.scheme.left) (ha : a ≫ p = 𝟙 _) :
    ∃ U : q.target.scheme.left.Opens, a (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (q.linePushforward A) ≅
        ⨁ (fun _ : Fin n => (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules))) := by
  apply finiteFrame_of_fiber_finrank p (q.linePushforward A)
    (linePushforward_finiteFrames q.map.hom.left A) a ha n
  have h := (sectionFunctorCoefficientEquiv (a ≫ p)
    ((Scheme.Modules.pullback a).obj (q.linePushforward A))).finrank_eq
  rw [ha] at h ⊢
  exact h.trans (q.linePushforward_geometricFiber_finrank A a)

end SteinerGeometry.CyclicEtaleIsogeny
