import SteinerGeometry.CyclicSubgroup
import SteinerGeometry.DisjointPushforward
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.ProductLabels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison

/-! The finite direct-sum decomposition on the actual self-fiber product of a
cyclic étale isogeny. The direct image and inverse image here are the actual
scheme module-sheaf functors. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry.CyclicEtaleIsogeny

variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ} (q : CyclicEtaleIsogeny D n)

/-- The self-fiber-product torsor isomorphism on underlying schemes. -/
def torsorSchemeIso : (D.scheme ⊗ (cyclicGroup n).X).left ≅
    pullback q.map.hom.left q.map.hom.left :=
  (Over.forget S).mapIso q.torsorIso ≪≫
    OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison.overSelfPullbackIso q.map.hom

@[reassoc]
theorem torsorSchemeIso_fst :
    q.torsorSchemeIso.hom ≫ pullback.fst q.map.hom.left q.map.hom.left =
      pullback.fst D.scheme.hom (cyclicGroup n).X.hom := by
  have h : (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison.overSelfPullbackIso q.map.hom).hom ≫
      pullback.fst q.map.hom.left q.map.hom.left = (pullback.fst q.map.hom q.map.hom).left :=
    ((IsPullback.of_hasPullback q.map.hom q.map.hom).map (Over.forget S)).isoPullback_hom_fst
  change (q.torsorIso.hom.left ≫ _ ) ≫ _ = _
  rw [Category.assoc, h]
  exact congrArg Over.Hom.left q.torsorIso_hom_fst

/-- Literal cyclic labels index all sheets of the self-fiber-product. -/
def splitSelfPullbackIso : (∐ fun _ : Multiplicative (ZMod n) => D.scheme.left) ≅
    pullback q.map.hom.left q.map.hom.left :=
  ConstantScheme.Product.constantSchemeProductIso D.scheme (Multiplicative (ZMod n)) ≪≫
    q.torsorSchemeIso

@[reassoc]
theorem splitSelfPullbackIso_fst :
    q.splitSelfPullbackIso.hom ≫ pullback.fst q.map.hom.left q.map.hom.left =
      Sigma.desc (fun _ : Multiplicative (ZMod n) => 𝟙 D.scheme.left) := by
  change (_ ≫ q.torsorSchemeIso.hom) ≫ _ = _
  rw [Category.assoc, torsorSchemeIso_fst]
  exact ConstantScheme.Product.constantSchemeProductIso_fst D.scheme (Multiplicative (ZMod n))

/-- The actual base-valued point of the isogeny kernel with the specified label. -/
def kernelLabelPoint (i : Multiplicative (ZMod n)) : 𝟙_ (Over S) ⟶ D.scheme :=
  ConstantScheme.Morphisms.constantSchemeLabelPoint S (Multiplicative (ZMod n)) i ≫
    q.kernelIso.hom ≫ q.map.kernelInclusion

/-- Translation by the actual labeled kernel point. -/
def deckTranslation (i : Multiplicative (ZMod n)) : D.scheme.left ⟶ D.scheme.left :=
  (D.basePointTranslation (q.kernelLabelPoint i)).left

/-- Every deck translation is an isomorphism of schemes. -/
def deckTranslationIso (i : Multiplicative (ZMod n)) : D.scheme.left ≅ D.scheme.left :=
  (Over.forget S).mapIso (D.basePointTranslationIso (q.kernelLabelPoint i))

@[reassoc]
theorem splitSelfPullbackIso_label_snd (i : Multiplicative (ZMod n)) :
    Sigma.ι (fun _ : Multiplicative (ZMod n) => D.scheme.left) i ≫
      q.splitSelfPullbackIso.hom ≫ pullback.snd q.map.hom.left q.map.hom.left =
        q.deckTranslation i := by
  let j := Constant.ProductLabels.constantProductLabel D.scheme (Multiplicative (ZMod n)) i
  have hjf : j ≫ fst D.scheme (cyclicGroup n).X = 𝟙 D.scheme := lift_fst _ _
  have hjs : j ≫ (snd D.scheme (cyclicGroup n).X ≫ q.kernelIso.hom ≫ q.map.kernelInclusion) =
      toUnit D.scheme ≫ q.kernelLabelPoint i := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ q.kernelIso.hom ≫ q.map.kernelInclusion)
        (lift_snd (𝟙 D.scheme) (toUnit D.scheme ≫
          ConstantScheme.Morphisms.constantSchemeLabelPoint S (Multiplicative (ZMod n)) i))).trans
        (Category.assoc _ _ _))
  have hlabel : j ≫ q.torsorIso.hom ≫ pullback.snd q.map.hom q.map.hom =
      D.basePointTranslation (q.kernelLabelPoint i) := by
    rw [q.torsorIso_hom_snd, MonObj.comp_mul, hjf, hjs]
    exact mul_comm _ _
  have hs : (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison.overSelfPullbackIso q.map.hom).hom ≫
      pullback.snd q.map.hom.left q.map.hom.left = (pullback.snd q.map.hom q.map.hom).left :=
    ((IsPullback.of_hasPullback q.map.hom q.map.hom).map (Over.forget S)).isoPullback_hom_snd
  have he : q.splitSelfPullbackIso.hom ≫ pullback.snd q.map.hom.left q.map.hom.left =
      (ConstantScheme.Product.constantSchemeProductIso D.scheme (Multiplicative (ZMod n))).hom ≫
        (q.torsorIso.hom.left ≫ (pullback.snd q.map.hom q.map.hom).left) := by
    dsimp [splitSelfPullbackIso, torsorSchemeIso]
    simp only [Category.assoc, hs]
  rw [he, ← Category.assoc,
    Constant.ProductLabels.constantSchemeProductIso_label D.scheme (Multiplicative (ZMod n)) i]
  exact congrArg Over.Hom.left hlabel

/-- These translations are actual deck transformations of the specified isogeny. -/
@[reassoc]
theorem deckTranslation_comp (i : Multiplicative (ZMod n)) :
    q.deckTranslation i ≫ q.map.hom.left = q.map.hom.left := by
  rw [← q.splitSelfPullbackIso_label_snd i]
  simp only [Category.assoc, ← pullback.condition]
  rw [q.splitSelfPullbackIso_fst_assoc]
  simp

/-- The translated summands are actual line bundles. -/
def translatedLineBundle (A : Line.Bundles.LineBundle D.scheme.left)
    (i : Multiplicative (ZMod n)) : Line.Bundles.LineBundle D.scheme.left :=
  A.pullback (q.deckTranslation i)

/-- On the self-fiber-product, direct image along the first projection splits
as the finite direct sum of translates of the original line bundle. -/
def selfFiberPushforwardSplitting [NeZero n] (A : Line.Bundles.LineBundle D.scheme.left) :
    (Scheme.Modules.pushforward (pullback.fst q.map.hom.left q.map.hom.left)).obj
      ((Scheme.Modules.pullback (pullback.snd q.map.hom.left q.map.hom.left)).obj A.sheaf) ≅
        ∐ (fun i : Multiplicative (ZMod n) => (Scheme.Modules.pullback (q.deckTranslation i)).obj A.sheaf) :=
  splitIsoProjectionPushforwardCoproductIso
      (pullback.fst q.map.hom.left q.map.hom.left) q.splitSelfPullbackIso
      q.splitSelfPullbackIso_fst
      ((Scheme.Modules.pullback (pullback.snd q.map.hom.left q.map.hom.left)).obj A.sheaf) ≪≫
    Sigma.mapIso (fun i =>
      (Scheme.Modules.pullbackComp
        (Sigma.ι (fun _ : Multiplicative (ZMod n) => D.scheme.left) i ≫ q.splitSelfPullbackIso.hom)
        (pullback.snd q.map.hom.left q.map.hom.left)).app A.sheaf ≪≫
      (Scheme.Modules.pullbackCongr ((Category.assoc _ _ _).trans
        (q.splitSelfPullbackIso_label_snd i))).app A.sheaf)

end SteinerGeometry.CyclicEtaleIsogeny
