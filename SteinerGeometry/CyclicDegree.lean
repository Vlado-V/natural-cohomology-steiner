import SteinerGeometry.PointEuler
import SteinerGeometry.CyclicComplexBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiniteFlatTrace
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny

/-! Euler degree of the point line under the actual cyclic étale isogeny. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.CyclicDegree

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction
open EllipticCohomology EulerDegree PointEuler
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {D : EllipticScheme} {n : ℕ} [NeZero n] (q : CyclicEtaleIsogeny D n)

/-- Normalized trace makes the structure pullback unit a monomorphism. -/
theorem structure_pullbackUnit_mono [IsLocallyNoetherian q.target.scheme.left] :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction q.map.hom.left).unit.app
      (Line.Bundles.structureModule q.target.scheme.left)) := by
  have hdegree : IsUnit (n : Γ(q.target.scheme.left, ⊤)) := by
    have hn : IsUnit (n : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast NeZero.ne n)
    simpa only [map_natCast] using
      hn.map (Coefficient.ModulePresheaf.schemeCoefficientMap q.target.scheme.hom)
  obtain ⟨u, hu⟩ := hdegree
  have := LocallyNoetherian.FiniteFlatTrace.locallyNoetherianFiniteFlat_pullbackStructureUnit_splitMono
    q.map.hom.left q.degree u hu
  exact inferInstance

/-- The actual zero fiber has Euler characteristic equal to the cyclic degree. -/
theorem kernel_structure_euler :
    χ q.map.kernelScheme.hom (Line.Bundles.structureModule q.map.kernelScheme.left) = n := by
  have : q.map.kernelScheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from q.map.kernelScheme.hom]
    infer_instance⟩
  have h := EulerIso.coefficientEulerCharacteristic_overIso q.kernelIso
    (Line.Bundles.LineBundle.trivial q.map.kernelScheme.left)
    (Line.Bundles.LineBundle.trivial (cyclicGroup (S := complexBase) n).X.left)
    (Line.Bundles.structureModulePullbackIso q.kernelIso.hom.left)
  exact h.symm.trans (by
    simpa only [cyclicGroup, etaleGroupScheme, Line.Bundles.LineBundle.trivial,
      ZMod.card, Fintype.card_multiplicative] using
      constantScheme_structure_euler (Multiplicative (ZMod n)))

/-- Replacing the rational zero point by its closed image gives the same
scheme-theoretic kernel, with its original projection to the source. -/
theorem kernelPointImagePullback
    [SmoothOfRelativeDimension 1 q.target.scheme.hom] :
    IsPullback
      (q.map.kernelScheme.hom ≫
        (rationalPointImageIso q.target.scheme.hom η[q.target.scheme].left η[q.target.scheme].w).hom)
      q.map.kernelInclusion.left
      η[q.target.scheme].left.ker.subschemeι q.map.hom.left := by
  let e := rationalPointImageIso q.target.scheme.hom η[q.target.scheme].left η[q.target.scheme].w
  have H : IsPullback q.map.kernelScheme.hom q.map.kernelInclusion.left
      η[q.target.scheme].left q.map.hom.left :=
    (IsPullback.of_hasPullback q.map.hom.left η[q.target.scheme].left).flip
  refine H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [e]
  · simp
  · change η[q.target.scheme].left ≫ 𝟙 _ =
      η[q.target.scheme].left.toImage ≫ η[q.target.scheme].left.imageι
    simp
  · simp

/-- The quotient appearing after pulling back the point ideal is the actual
finite kernel, and has Euler characteristic n. -/
theorem pulledPoint_quotient_euler
    [SmoothOfRelativeDimension 1 q.target.scheme.hom] :
    χ D.scheme.hom
      ((Scheme.Modules.pushforward
        (pullback.snd η[q.target.scheme].left.ker.subschemeι q.map.hom.left)).obj
        (Line.Bundles.structureModule
          (pullback η[q.target.scheme].left.ker.subschemeι q.map.hom.left))) = n := by
  have : D.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.scheme.hom]
    infer_instance⟩
  let H := kernelPointImagePullback q
  let P := pullback η[q.target.scheme].left.ker.subschemeι q.map.hom.left
  let b : P ⟶ D.scheme.left := pullback.snd _ _
  have : P.IsSeparated := ⟨by
    rw [← terminal.comp_from b]
    infer_instance⟩
  let E : Over.mk q.map.kernelScheme.hom ≅ Over.mk (b ≫ D.scheme.hom) :=
    Over.isoMk H.isoPullback (by
      change H.isoPullback.hom ≫ (b ≫ D.scheme.hom) = q.map.kernelScheme.hom
      rw [← Category.assoc, H.isoPullback_hom_snd]
      exact q.map.kernelInclusion.w)
  have : (Over.mk (b ≫ D.scheme.hom)).left.IsSeparated := inferInstanceAs P.IsSeparated
  have : (Line.Bundles.structureModule P).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial P).isQuasicoherent
  have hiso := EulerIso.coefficientEulerCharacteristic_overIso E
    (Line.Bundles.LineBundle.trivial P)
    (Line.Bundles.LineBundle.trivial q.map.kernelScheme.left)
    (Line.Bundles.structureModulePullbackIso E.hom.left)
  exact (Affine.PushforwardEuler.coefficientEulerCharacteristic_affinePushforward
    b D.scheme.hom (Line.Bundles.structureModule P)).symm.trans
    (hiso.symm.trans (kernel_structure_euler q))

/-- Pullback of the actual rational point ideal has degree minus n. -/
theorem pulledPointIdeal_euler [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [CurveCohomologyFinite D.scheme.hom]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0) :
    χ D.scheme.hom
      ((rationalPointIdealLineBundle q.target.scheme.hom
        η[q.target.scheme].left η[q.target.scheme].w).pullback q.map.hom.left).sheaf = -(n : ℤ) := by
  have := structure_pullbackUnit_mono q
  have : CurveCohomologyFinite (q.map.hom.left ≫ q.target.scheme.hom) := by
    simpa only [q.map.hom.w] using (inferInstance : CurveCohomologyFinite D.scheme.hom)
  have hp := pullback_pointIdeal_euler q.target.scheme.hom
    η[q.target.scheme].left η[q.target.scheme].w q.map.hom.left hd hOC
    (by simpa only [q.map.hom.w] using hOD) n
    (by simpa only [q.map.hom.w] using pulledPoint_quotient_euler q)
  simpa only [q.map.hom.w] using hp

/-- The point line itself pulls back with exactly degree n. -/
theorem pulledPointLine_euler [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [CurveCohomologyFinite D.scheme.hom]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0) :
    χ D.scheme.hom
      ((rationalPointIdealLineBundle q.target.scheme.hom
        η[q.target.scheme].left η[q.target.scheme].w).reciprocalFrameBundle.pullback
          q.map.hom.left).sheaf = n := by
  let I := rationalPointIdealLineBundle q.target.scheme.hom
    η[q.target.scheme].left η[q.target.scheme].w
  let s := OAI.MaximalSeshadri.IdealModule.inclusion η[q.target.scheme].left.ker.subschemeι
  have := structure_pullbackUnit_mono q
  have hs : s ≠ 0 := rationalPointIdeal_inclusion_ne_zero q.target.scheme.hom
    η[q.target.scheme].left η[q.target.scheme].w hOC
  have hp : (Scheme.Modules.pullback q.map.hom.left).map s ≠ 0 :=
    by
      have : Mono ((Scheme.Modules.pullbackPushforwardAdjunction q.map.hom.left).unit.app
        (OAI.MaximalSeshadri.IdealModule.unit q.target.scheme.left)) :=
        inferInstanceAs (Mono ((Scheme.Modules.pullbackPushforwardAdjunction q.map.hom.left).unit.app
          (Line.Bundles.structureModule q.target.scheme.left)))
      exact pullback_map_ne_zero_of_mono_unit q.map.hom.left s hs
  let t : (I.pullback q.map.hom.left).sheaf ⟶ Line.Bundles.structureModule D.scheme.left :=
    (Scheme.Modules.pullback q.map.hom.left).map s ≫
      (Line.Bundles.structureModulePullbackIso q.map.hom.left).hom
  have ht : t ≠ 0 := by
    intro hz
    apply hp
    apply (cancel_mono (Line.Bundles.structureModulePullbackIso q.map.hom.left).hom).mp
    simpa only [t, zero_comp] using hz
  have hrec := reciprocal_euler_of_map_to_structure D.scheme.hom hd hOD
    (I.pullback q.map.hom.left) t ht
  have hc : Line.Bundles.LineBundle.classOf
      (I.reciprocalFrameBundle.pullback q.map.hom.left) =
      Line.Bundles.LineBundle.classOf
        (I.pullback q.map.hom.left).reciprocalFrameBundle := by
    change (Line.Bundles.LineBundle.pullbackClassMonoidHom q.map.hom.left)
      (Line.Bundles.LineBundle.classOf I.reciprocalFrameBundle) = _
    rw [Line.Bundles.LineBundle.classOf_reciprocalFrameBundle, map_inv,
      Line.Bundles.LineBundle.classOf_reciprocalFrameBundle]
    rfl
  have he := congrArg (EulerIso.lineBundleClassEuler D.scheme.hom) hc
  change χ D.scheme.hom (I.reciprocalFrameBundle.pullback q.map.hom.left).sheaf = n
  change χ D.scheme.hom (I.reciprocalFrameBundle.pullback q.map.hom.left).sheaf =
    χ D.scheme.hom (I.pullback q.map.hom.left).reciprocalFrameBundle.sheaf at he
  rw [he, hrec, pulledPointIdeal_euler q hd hOC hOD]
  simp


/-- Translation commutes with the homomorphism in the expected direction. -/
theorem translation_naturality (d : 𝟙_ (Over complexBase) ⟶ D.scheme) :
    D.basePointTranslation d ≫ q.map.hom =
      q.map.hom ≫ q.target.basePointTranslation (d ≫ q.map.hom) := by
  simp [Abelian.Schemes.AbelianScheme.basePointTranslation, MonObj.mul_comp,
    MonObj.comp_mul, Category.assoc]

/-- Every rational fiber is a translate of the literal kernel. -/
theorem translatedKernelPointImagePullback
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme)
    (d : 𝟙_ (Over complexBase) ⟶ D.scheme) (hd : d ≫ q.map.hom = y) :
    IsPullback
      (q.map.kernelScheme.hom ≫ (rationalPointImageIso q.target.scheme.hom y.left y.w).hom)
      (q.map.kernelInclusion ≫ D.basePointTranslation d).left
      y.left.ker.subschemeι q.map.hom.left := by
  let e := rationalPointImageIso q.target.scheme.hom y.left y.w
  let eD := (Over.forget complexBase).mapIso (D.basePointTranslationIso d)
  let eC := (Over.forget complexBase).mapIso (q.target.basePointTranslationIso y)
  have H : IsPullback q.map.kernelScheme.hom q.map.kernelInclusion.left
      η[q.target.scheme].left q.map.hom.left :=
    (IsPullback.of_hasPullback q.map.hom.left η[q.target.scheme].left).flip
  refine H.of_iso (Iso.refl _) e eD eC ?_ ?_ ?_ ?_
  · simp [e]
  · simp [eD, Abelian.Schemes.AbelianScheme.basePointTranslationIso]
  · have ht : η[q.target.scheme] ≫ q.target.basePointTranslation y = y := by
      simp [Abelian.Schemes.AbelianScheme.basePointTranslation, MonObj.comp_mul,
        Hom.one_def, toUnit_unit]
    change η[q.target.scheme].left ≫ (q.target.basePointTranslation y).left =
      y.left.toImage ≫ y.left.imageι
    rw [y.left.toImage_imageι]
    exact congrArg Over.Hom.left ht
  · have ht := translation_naturality q d
    rw [hd] at ht
    exact (congrArg Over.Hom.left ht).symm

/-- Every closed complex point has a fiber of the same Euler length n; the
lift to the source is obtained from the actual finite surjective morphism. -/
theorem pulledPoint_quotient_euler_at
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme) :
    χ D.scheme.hom
      ((Scheme.Modules.pushforward (pullback.snd y.left.ker.subschemeι q.map.hom.left)).obj
        (Line.Bundles.structureModule (pullback y.left.ker.subschemeι q.map.hom.left))) = n := by
  obtain ⟨d, hd⟩ :=
    OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective
      q.map (𝟙 complexBase) y
  change d ≫ q.map.hom = y at hd
  have : D.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.scheme.hom]
    infer_instance⟩
  let H := translatedKernelPointImagePullback q y d hd
  let P := pullback y.left.ker.subschemeι q.map.hom.left
  let b : P ⟶ D.scheme.left := pullback.snd _ _
  have : P.IsSeparated := ⟨by
    rw [← terminal.comp_from b]
    infer_instance⟩
  let E : Over.mk q.map.kernelScheme.hom ≅ Over.mk (b ≫ D.scheme.hom) :=
    Over.isoMk H.isoPullback (by
      change H.isoPullback.hom ≫ (b ≫ D.scheme.hom) = q.map.kernelScheme.hom
      rw [← Category.assoc, H.isoPullback_hom_snd]
      exact (q.map.kernelInclusion ≫ D.basePointTranslation d).w)
  have : (Over.mk (b ≫ D.scheme.hom)).left.IsSeparated := inferInstanceAs P.IsSeparated
  have : (Line.Bundles.structureModule P).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial P).isQuasicoherent
  have hiso := EulerIso.coefficientEulerCharacteristic_overIso E
    (Line.Bundles.LineBundle.trivial P)
    (Line.Bundles.LineBundle.trivial q.map.kernelScheme.left)
    (Line.Bundles.structureModulePullbackIso E.hom.left)
  exact (Affine.PushforwardEuler.coefficientEulerCharacteristic_affinePushforward
    b D.scheme.hom (Line.Bundles.structureModule P)).symm.trans
    (hiso.symm.trans (kernel_structure_euler q))

/-- Pullback multiplies the degree of every rational point ideal by n. -/
theorem pulledPointIdeal_euler_at [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [CurveCohomologyFinite D.scheme.hom]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme)
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0) :
    χ D.scheme.hom
      ((rationalPointIdealLineBundle q.target.scheme.hom y.left y.w).pullback
        q.map.hom.left).sheaf = -(n : ℤ) := by
  have := structure_pullbackUnit_mono q
  have : CurveCohomologyFinite (q.map.hom.left ≫ q.target.scheme.hom) := by
    simpa only [q.map.hom.w] using (inferInstance : CurveCohomologyFinite D.scheme.hom)
  have hp := pullback_pointIdeal_euler q.target.scheme.hom y.left y.w q.map.hom.left hd hOC
    (by simpa only [q.map.hom.w] using hOD) n
    (by simpa only [q.map.hom.w] using pulledPoint_quotient_euler_at q y)
  simpa only [q.map.hom.w] using hp

/-- Pullback multiplies the degree of the positive line of any rational point
by n, not just the identity point. -/
theorem pulledPointLine_euler_at [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [CurveCohomologyFinite D.scheme.hom]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0) :
    χ D.scheme.hom
      ((rationalPointIdealLineBundle q.target.scheme.hom y.left y.w).reciprocalFrameBundle.pullback
        q.map.hom.left).sheaf = n := by
  let I := rationalPointIdealLineBundle q.target.scheme.hom y.left y.w
  let s := OAI.MaximalSeshadri.IdealModule.inclusion y.left.ker.subschemeι
  have := structure_pullbackUnit_mono q
  have hs : s ≠ 0 := rationalPointIdeal_inclusion_ne_zero q.target.scheme.hom y.left y.w hOC
  have hp : (Scheme.Modules.pullback q.map.hom.left).map s ≠ 0 :=
    by
      have : Mono ((Scheme.Modules.pullbackPushforwardAdjunction q.map.hom.left).unit.app
        (OAI.MaximalSeshadri.IdealModule.unit q.target.scheme.left)) :=
        inferInstanceAs (Mono ((Scheme.Modules.pullbackPushforwardAdjunction q.map.hom.left).unit.app
          (Line.Bundles.structureModule q.target.scheme.left)))
      exact pullback_map_ne_zero_of_mono_unit q.map.hom.left s hs
  let t : (I.pullback q.map.hom.left).sheaf ⟶ Line.Bundles.structureModule D.scheme.left :=
    (Scheme.Modules.pullback q.map.hom.left).map s ≫
      (Line.Bundles.structureModulePullbackIso q.map.hom.left).hom
  have ht : t ≠ 0 := by
    intro hz
    apply hp
    apply (cancel_mono (Line.Bundles.structureModulePullbackIso q.map.hom.left).hom).mp
    simpa only [t, zero_comp] using hz
  have hrec := reciprocal_euler_of_map_to_structure D.scheme.hom hd hOD
    (I.pullback q.map.hom.left) t ht
  have hc : Line.Bundles.LineBundle.classOf (I.reciprocalFrameBundle.pullback q.map.hom.left) =
      Line.Bundles.LineBundle.classOf (I.pullback q.map.hom.left).reciprocalFrameBundle := by
    change (Line.Bundles.LineBundle.pullbackClassMonoidHom q.map.hom.left)
      (Line.Bundles.LineBundle.classOf I.reciprocalFrameBundle) = _
    rw [Line.Bundles.LineBundle.classOf_reciprocalFrameBundle, map_inv,
      Line.Bundles.LineBundle.classOf_reciprocalFrameBundle]
    rfl
  have he := congrArg (EulerIso.lineBundleClassEuler D.scheme.hom) hc
  change χ D.scheme.hom (I.reciprocalFrameBundle.pullback q.map.hom.left).sheaf = n
  change χ D.scheme.hom (I.reciprocalFrameBundle.pullback q.map.hom.left).sheaf =
    χ D.scheme.hom (I.pullback q.map.hom.left).reciprocalFrameBundle.sheaf at he
  rw [he, hrec, pulledPointIdeal_euler_at q y hd hOC hOD]
  simp

end SteinerGeometry.CyclicDegree
