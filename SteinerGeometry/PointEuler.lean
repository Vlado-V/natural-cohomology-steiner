import SteinerGeometry.EulerDegree
import SteinerGeometry.PointLineBundle
import SteinerGeometry.PointEulerCore
import SteinerGeometry.RightExactPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismStructureBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismQuasicoherentPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Degree

/-! The native Euler characteristic of a rational point ideal and its inverse. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.PointEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology EulerDegree

/-- A finite constant scheme has one unit of Euler characteristic per label. -/
theorem constantScheme_structure_euler (J : Type) [Fintype J] :
    χ (ConstantScheme.Iff.constantScheme (Spec (.of ℂ)) J).hom
      (Line.Bundles.structureModule
        (ConstantScheme.Iff.constantScheme (Spec (.of ℂ)) J).left) = Fintype.card J := by
  let R := J → ℂ
  let b : Spec (.of R) ⟶ Spec (.of ℂ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  have hr : χ b (Line.Bundles.structureModule (Spec (.of R))) = Fintype.card J :=
    finiteProductSpec_structure_euler J
  let e : (ConstantScheme.Iff.constantScheme (Spec (.of ℂ)) J).left ≅ Spec (.of R) :=
    asIso (sigmaSpec (fun _ : J => CommRingCat.of ℂ))
  let eover : ConstantScheme.Iff.constantScheme (Spec (.of ℂ)) J ≅ Over.mk b :=
    Over.isoMk e (ConstantScheme.Degree.constantScheme_spec_structure ℂ J).symm
  have : (Over.mk b).left.IsSeparated := inferInstanceAs ((Spec (.of R)).IsSeparated)
  exact (EulerIso.coefficientEulerCharacteristic_overIso eover
    (Line.Bundles.LineBundle.trivial (Spec (.of R)))
    (Line.Bundles.LineBundle.trivial _)
    (Line.Bundles.structureModulePullbackIso e.hom)).trans hr

/-- The quotient in the actual ideal sequence is a one-dimensional point. -/
theorem rationalPoint_quotient_euler {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    χ f ((Scheme.Modules.pushforward p.ker.subschemeι).obj
      (Line.Bundles.structureModule p.ker.subscheme)) = 1 := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let e := rationalPointImageIso f p hp
  have he : e.hom ≫ p.ker.subschemeι ≫ f = 𝟙 _ := by
    change p.toImage ≫ p.imageι ≫ f = _
    rw [p.toImage_imageι_assoc, hp]
  have heinv : e.inv = p.ker.subschemeι ≫ f := by
    apply (cancel_epi e.hom).mp
    rw [e.hom_inv_id, he]
  have hi := EulerIso.coefficientEulerCharacteristic_pullback_iso e.inv
    (𝟙 (Spec (.of ℂ))) (Line.Bundles.LineBundle.trivial (Spec (.of ℂ)))
  have hecomp : e.inv ≫ 𝟙 (Spec (.of ℂ)) = p.ker.subschemeι ≫ f := by
    simpa only [Category.comp_id] using heinv
  rw [hecomp] at hi
  have hunit := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso
    (p.ker.subschemeι ≫ f) (Line.Bundles.structureModulePullbackIso e.inv)
  have heuler : χ (p.ker.subschemeι ≫ f)
      (Line.Bundles.structureModule p.ker.subscheme) = 1 := by
    exact hunit.symm.trans (hi.trans complexPoint_structure_euler)
  have : (Line.Bundles.structureModule p.ker.subscheme).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial _).isQuasicoherent
  exact (Affine.PushforwardEuler.coefficientEulerCharacteristic_affinePushforward
    p.ker.subschemeι f (Line.Bundles.structureModule p.ker.subscheme)).symm.trans heuler

/-- The point ideal Euler formula does not require a genus assumption. -/
theorem rationalPointIdeal_euler_general {X : Scheme.{0}} [IsNoetherian X]
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f] [CurveCohomologyFinite f]
    (hd : topologicalKrullDim X ≤ 1)
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    χ f (rationalPointIdealLineBundle f p hp).sheaf =
      χ f (Line.Bundles.structureModule X) - 1 := by
  let I := rationalPointIdealLineBundle f p hp
  let Q := (Scheme.Modules.pushforward p.ker.subschemeι).obj
    (Line.Bundles.structureModule p.ker.subscheme)
  have : I.sheaf.IsQuasicoherent := I.isQuasicoherent
  have : I.sheaf.IsFiniteType := I.isFiniteType
  have : (Line.Bundles.structureModule p.ker.subscheme).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial _).isQuasicoherent
  have : (Line.Bundles.structureModule p.ker.subscheme).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial _).isFiniteType
  have : (Line.Bundles.structureModule X).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial _).isQuasicoherent
  have : (Line.Bundles.structureModule X).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial _).isFiniteType
  have : Q.IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent
      p.ker.subschemeι (Line.Bundles.structureModule p.ker.subscheme)
  have : Q.IsFiniteType := Finite.ImageType.finite_directImage_finiteType
    p.ker.subschemeι (Line.Bundles.structureModule p.ker.subscheme)
  let S := ShortComplex.mk (OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι)
    (OAI.MaximalSeshadri.IdealModule.structureMap p.ker.subschemeι) (kernel.condition _)
  have hS : S.ShortExact := rationalPointIdealLineBundle_exact f p hp
  have : S.X₁.IsQuasicoherent := I.isQuasicoherent
  have : S.X₁.IsFiniteType := I.isFiniteType
  have : S.X₂.IsQuasicoherent := (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have : S.X₂.IsFiniteType := (Line.Bundles.LineBundle.trivial X).isFiniteType
  have : S.X₃.IsQuasicoherent := inferInstanceAs Q.IsQuasicoherent
  have : S.X₃.IsFiniteType := inferInstanceAs Q.IsFiniteType
  have h := CurveEulerAdditivity.coherent_euler_additive f hd hS
  have hq := rationalPoint_quotient_euler f p hp
  change χ f (Line.Bundles.structureModule X) = χ f I.sheaf + χ f Q at h
  change χ f Q = 1 at hq
  change χ f I.sheaf = χ f (Line.Bundles.structureModule X) - 1
  omega

/-- The ideal inclusion is nonzero because its invertible source is nonzero,
without first using its Euler characteristic. -/
theorem rationalPointIdeal_inclusion_ne_zero_general {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι ≠ 0 := by
  intro hz
  have : Nonempty X := ⟨p default⟩
  apply lineBundle_not_isZero (rationalPointIdealLineBundle f p hp)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι)).mp
  rw [hz]
  simp

/-- The positive point line has Euler characteristic χ(O)+1 on every smooth
proper integral curve. -/
theorem rationalPointLine_euler_general {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f] [CurveCohomologyFinite f]
    (hd : topologicalKrullDim X ≤ 1)
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    χ f (rationalPointIdealLineBundle f p hp).reciprocalFrameBundle.sheaf =
      χ f (Line.Bundles.structureModule X) + 1 := by
  have h := reciprocal_euler_of_map_to_structure_general f hd
    (rationalPointIdealLineBundle f p hp)
    (OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι)
    (rationalPointIdeal_inclusion_ne_zero_general f p hp)
  rw [rationalPointIdeal_euler_general f hd p hp] at h
  omega

/-- The canonical effective positive-degree reference exists before genus is
computed, so the general tensor Euler law is available without circularity. -/
theorem exists_effective_positiveDegreeLine {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f] [CurveCohomologyFinite f]
    (hd : topologicalKrullDim X ≤ 1)
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ∃ (H : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ H.sheaf),
      s ≠ 0 ∧ χ f (Line.Bundles.structureModule X) < χ f H.sheaf := by
  let I := rationalPointIdealLineBundle f p hp
  let t := OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι
  refine ⟨I.reciprocalFrameBundle, reciprocalSection I t,
    reciprocalSection_ne_zero I t (rationalPointIdeal_inclusion_ne_zero_general f p hp), ?_⟩
  have h := rationalPointLine_euler_general f hd p hp
  change χ f I.reciprocalFrameBundle.sheaf = χ f (Line.Bundles.structureModule X) + 1 at h
  change χ f (Line.Bundles.structureModule X) < χ f I.reciprocalFrameBundle.sheaf
  omega

/-- The invertible ideal of one rational point has degree minus one. -/
theorem rationalPointIdeal_euler {X : Scheme.{0}} [IsNoetherian X]
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [CurveCohomologyFinite f] (hd : topologicalKrullDim X ≤ 1)
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hO : χ f (Line.Bundles.structureModule X) = 0) :
    χ f (rationalPointIdealLineBundle f p hp).sheaf = -1 := by
  simpa only [hO, zero_sub] using rationalPointIdeal_euler_general f hd p hp

/-- The actual point ideal inclusion is nonzero. -/
theorem rationalPointIdeal_inclusion_ne_zero {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (_hO : χ f (Line.Bundles.structureModule X) = 0) :
    OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι ≠ 0 :=
  rationalPointIdeal_inclusion_ne_zero_general f p hp

/-- The pullback of the point ideal has minus the Euler characteristic of the
actual fiber. Right exactness of pullback suffices: the pulled-back inclusion
is monic because it is a nonzero map of line bundles on an integral scheme. -/
theorem pullback_pointIdeal_euler {X Y : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (q : Y ⟶ X) [IsFinite q] [CurveCohomologyFinite (q ≫ f)]
    (hd : topologicalKrullDim Y ≤ 1)
    [Mono ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      (Line.Bundles.structureModule X))]
    (hOX : χ f (Line.Bundles.structureModule X) = 0)
    (hOY : χ (q ≫ f) (Line.Bundles.structureModule Y) = 0)
    (m : ℤ)
    (hfiber : χ (q ≫ f)
      ((Scheme.Modules.pushforward (pullback.snd p.ker.subschemeι q)).obj
        (Line.Bundles.structureModule (pullback p.ker.subschemeι q))) = m) :
    χ (q ≫ f) ((rationalPointIdealLineBundle f p hp).pullback q).sheaf = -m := by
  let I := rationalPointIdealLineBundle f p hp
  let Q := (Scheme.Modules.pushforward p.ker.subschemeι).obj
    (Line.Bundles.structureModule p.ker.subscheme)
  let S := ShortComplex.mk (OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι)
    (OAI.MaximalSeshadri.IdealModule.structureMap p.ker.subschemeι) (kernel.condition _)
  let F := Scheme.Modules.pullback q
  have hS : S.ShortExact := rationalPointIdealLineBundle_exact f p hp
  have : Mono ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app S.X₂) :=
    inferInstanceAs (Mono ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      (Line.Bundles.structureModule X)))
  have hn : F.map S.f ≠ 0 := pullback_map_ne_zero_of_mono_unit q S.f
    (rationalPointIdeal_inclusion_ne_zero f p hp hOX)
  have : Mono (F.map S.f) := lineMap_mono_of_ne_zero (I.pullback q)
    ((Line.Bundles.LineBundle.trivial X).pullback q) (F.map S.f) hn
  have hsmap : (S.map F).ShortExact := pullback_shortExact_of_mono q hS
  have : (Line.Bundles.structureModule p.ker.subscheme).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial _).isQuasicoherent
  have : (Line.Bundles.structureModule p.ker.subscheme).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial _).isFiniteType
  have : (Line.Bundles.structureModule X).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial _).isQuasicoherent
  have : (Line.Bundles.structureModule X).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial _).isFiniteType
  have : Q.IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent
      p.ker.subschemeι (Line.Bundles.structureModule p.ker.subscheme)
  have : Q.IsFiniteType := Finite.ImageType.finite_directImage_finiteType
    p.ker.subschemeι (Line.Bundles.structureModule p.ker.subscheme)
  have : (F.obj Q).IsQuasicoherent :=
    Affine.MorphismQuasicoherentPullback.quasicoherent_pullback_of_isAffineHom q Q
  have : (F.obj Q).IsFiniteType :=
    Quasicoherent.PullbackFiniteType.module_pullback_finiteType q Q
  have : (I.pullback q).sheaf.IsQuasicoherent := (I.pullback q).isQuasicoherent
  have : (I.pullback q).sheaf.IsFiniteType := (I.pullback q).isFiniteType
  have : ((Line.Bundles.LineBundle.trivial X).pullback q).sheaf.IsQuasicoherent :=
    ((Line.Bundles.LineBundle.trivial X).pullback q).isQuasicoherent
  have : ((Line.Bundles.LineBundle.trivial X).pullback q).sheaf.IsFiniteType :=
    ((Line.Bundles.LineBundle.trivial X).pullback q).isFiniteType
  have : (S.map F).X₁.IsQuasicoherent := (I.pullback q).isQuasicoherent
  have : (S.map F).X₁.IsFiniteType := (I.pullback q).isFiniteType
  have : (S.map F).X₂.IsQuasicoherent :=
    ((Line.Bundles.LineBundle.trivial X).pullback q).isQuasicoherent
  have : (S.map F).X₂.IsFiniteType :=
    ((Line.Bundles.LineBundle.trivial X).pullback q).isFiniteType
  have : (S.map F).X₃.IsQuasicoherent := inferInstanceAs (F.obj Q).IsQuasicoherent
  have : (S.map F).X₃.IsFiniteType := inferInstanceAs (F.obj Q).IsFiniteType
  have hadd := CurveEulerAdditivity.coherent_euler_additive (q ≫ f) hd hsmap
  have hmid := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso (q ≫ f)
    (Line.Bundles.structureModulePullbackIso q)
  have hright := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso (q ≫ f)
    (Affine.MorphismStructureBaseChange.affineMorphismStructureBaseChangeIso
      (IsPullback.of_hasPullback p.ker.subschemeι q))
  change χ (q ≫ f) (F.obj (Line.Bundles.structureModule X)) =
    χ (q ≫ f) (Line.Bundles.structureModule Y) at hmid
  change χ (q ≫ f) (F.obj Q) =
    χ (q ≫ f) ((Scheme.Modules.pushforward (pullback.snd p.ker.subschemeι q)).obj
      (Line.Bundles.structureModule (pullback p.ker.subschemeι q))) at hright
  change χ (q ≫ f) (F.obj (Line.Bundles.structureModule X)) =
    χ (q ≫ f) (I.pullback q).sheaf + χ (q ≫ f) (F.obj Q) at hadd
  change χ (q ≫ f) (I.pullback q).sheaf = -m
  omega

/-- The reciprocal of the point ideal is a degree-one line bundle, with an
actual nonzero section given by its ideal inclusion. -/
theorem rationalPointLine_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] [SmoothOfRelativeDimension 1 f] [CurveCohomologyFinite f]
    (hd : topologicalKrullDim X ≤ 1)
    (p : Spec (.of ℂ) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hO : χ f (Line.Bundles.structureModule X) = 0) :
    χ f (rationalPointIdealLineBundle f p hp).reciprocalFrameBundle.sheaf = 1 := by
  have hincl := rationalPointIdeal_inclusion_ne_zero f p hp hO
  have h := reciprocal_euler_of_map_to_structure f hd hO
    (rationalPointIdealLineBundle f p hp)
    (OAI.MaximalSeshadri.IdealModule.inclusion p.ker.subschemeι) hincl
  rw [rationalPointIdeal_euler f hd p hp hO] at h
  simpa using h

end SteinerGeometry.PointEuler
