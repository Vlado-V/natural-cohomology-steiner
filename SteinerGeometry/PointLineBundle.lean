module

public import SteinerGeometry.PointKernelLocal
public import OAI.AlgebraicGeometry.Seshadri.Sheaves.ClosedModuleExact
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.MaximalSeshadri

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem regular_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (t : R) (ht : IsRegular t) : IsRegular (e t) := by
  have hl : IsLeftRegular (e t) := by
    intro a b h
    apply e.symm.injective
    have he := congrArg e.symm h
    rw [map_mul, map_mul, e.symm_apply_apply] at he
    exact ht.left he
  exact ⟨hl, fun a b h => hl ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩

/-- An affine open chart on which the specified ideal has one regular equation. -/
structure RegularIdealFrame {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) where
  source : Scheme.{0}
  [affine : IsAffine source]
  map : source ⟶ X
  [openImmersion : IsOpenImmersion map]
  point : source
  map_point : map point = x
  equation : Γ(source, ⊤)
  regular : IsRegular equation
  ideal_eq : (I.comap map).ideal ⟨⊤, isAffineOpen_top source⟩ = Ideal.span {equation}

attribute [instance] RegularIdealFrame.affine RegularIdealFrame.openImmersion

private theorem point_specIdeal_support {R : Type} [CommRing R] (I : Ideal R) :
    ((IdealPullback.specIdeal I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  rw [IdealPullback.specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  congr 1
  change ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
    (Scheme.ΓSpecIso (.of R)).inv.hom : Set R) = _
  rw [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

private theorem point_specMap_ker {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (Spec.map (CommRingCat.ofHom f)).ker = IdealPullback.specIdeal (RingHom.ker f) := by
  rw [Scheme.ker_of_isAffine, IdealPullback.specIdeal]
  congr 1
  apply Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)]
  ext r
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  have he := CategoryTheory.congr_fun
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r
  change (Scheme.ΓSpecIso (.of S)).inv (f r) =
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) at he
  rw [← he]
  exact map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).inv).1

/-- The ideal of a rational section on a smooth curve is an actual invertible
ideal. The affine chart, its regular generator and all identifications are
constructed from smoothness. -/
theorem rational_point_regular_frames {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ∀ x : X, Nonempty (RegularIdealFrame p.ker x) := by
  let point : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  let := isClosedImmersion_of_comp_eq_id f p hp
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) (p point)
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f (p point) := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst U
  let A := Γ(X, V)
  let g : CommRingCat.of K ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V e
  have hng : RingHom.IsStandardSmoothOfRelativeDimension 1 g.hom := by
    let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
      RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    rfl
  algebraize [g.hom]
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 K A := hng.toAlgebra
  let j := hV.fromSpec
  have hmap : Spec.map g = j ≫ f := by
    dsimp only [g]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  have hps : Set.range p ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rw [show z = point from Subsingleton.elim _ _]
    rwa [hV.range_fromSpec]
  let l := IsOpenImmersion.lift j p hps
  have hlj : l ≫ j = p := IsOpenImmersion.lift_fac j p hps
  let q := Spec.preimage l
  have hq : Spec.map q = l := Spec.map_preimage l
  have hqg : g ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hmap, ← Category.assoc, hlj, hp, Spec.map_id]
  let ρ : A →ₐ[K] K :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hqg c }
  have hker : p.ker.comap j = IdealPullback.specIdeal (RingHom.ker ρ) := by
    have sq := IsOpenImmersion.isPullback_lift_id p j hps
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion p j,
      ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
      sq.isoPullback_hom_fst]
    change l.ker = _
    rw [← hq]
    exact point_specMap_ker q.hom
  obtain ⟨s, hs, t, ht, hIt⟩ := smooth_curve_point_kernel_local ρ
  let a := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))
  let j' := a ≫ j
  let E := Scheme.ΓSpecIso (CommRingCat.of (Localization.Away s))
  have hregular : IsRegular (E.inv t) :=
    regular_ringEquiv E.commRingCatIsoToRingEquiv.symm t ht
  have hideal : (p.ker.comap j').ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {E.inv t} := by
    dsimp only [j']
    rw [Scheme.IdealSheafData.comap_comp, hker, IdealPullback.specIdeal_comap,
      IdealPullback.specIdeal_top, hIt, Ideal.map_span, Set.image_singleton]
  intro x
  by_cases hx : x ∈ (p.ker.support : Set X)
  · obtain ⟨y, hy⟩ := hps (by
      rwa [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq] at hx)
    have hyI : y ∈ ((p.ker.comap j).support : Set (Spec A)) := by
      rw [Scheme.IdealSheafData.support_comap]
      change j y ∈ (p.ker.support : Set X)
      simpa only [hy] using hx
    rw [hker, point_specIdeal_support] at hyI
    have hle : RingHom.ker ρ ≤ y.asIdeal := (PrimeSpectrum.mem_zeroLocus y _).mp hyI
    have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ
      (fun c => ⟨algebraMap K A c, by simp⟩)
    have hyq : y.asIdeal = RingHom.ker ρ := (hmax.eq_of_le y.isPrime.ne_top hle).symm
    have hyn : s ∉ y.asIdeal := by simpa only [hyq, RingHom.mem_ker] using hs
    have hyr : y ∈ Set.range a := by
      change y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away s)))
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
      exact hyn
    obtain ⟨z, hz⟩ := hyr
    exact ⟨{ source := Spec (.of (Localization.Away s))
             affine := inferInstance
             map := j'
             openImmersion := inferInstance
             point := z
             map_point := (congrArg j hz).trans hy
             equation := E.inv t
             regular := hregular
             ideal_eq := hideal }⟩
  · let W : X.Opens := p.ker.support.compl
    obtain ⟨T, hT, hxT, hTW⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W from hx)
    have he : p.ker.comap T.ι = ⊤ := by
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      rw [Scheme.IdealSheafData.support_comap]
      ext z
      exact iff_false_intro (hTW z.property)
    let : IsAffine T.toScheme := hT
    refine ⟨{ source := T.toScheme
              affine := inferInstance
              map := T.ι
              openImmersion := inferInstance
              point := ⟨x, hxT⟩
              map_point := rfl
              equation := 1
              regular := isRegular_one
              ideal_eq := ?_ }⟩
    rw [he]
    simp

/-- The actual invertible ideal of a rational point of a smooth curve. -/
def rationalPointIdealLineBundle {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := IdealModule.closedModule p.ker
  locallyTrivial x := by
    let D := (rational_point_regular_frames f p hp x).some
    obtain ⟨e⟩ := IdealModule.frame_restriction p.ker D.map D.equation D.ideal_eq D.regular.left
    refine ⟨D.map.opensRange, ⟨D.point, D.map_point⟩, ⟨?_⟩⟩
    exact (Scheme.Modules.restrictFunctorIsoPullback D.map.opensRange.ι).symm.app _ ≪≫
      IdealModule.frameOnRange _ D.map e

/-- The ideal inclusion and quotient are the native exact sequence of the
closed point image. Its quotient scheme is isomorphic to the ground-field point. -/
theorem rationalPointIdealLineBundle_exact {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of K) ⟶ X) (_hp : p ≫ f = 𝟙 _) :
    (ShortComplex.mk (IdealModule.inclusion p.ker.subschemeι)
      (IdealModule.structureMap p.ker.subschemeι) (kernel.condition _)).ShortExact :=
  IdealModule.closedSequence_exact p.ker.subschemeι

/-- The closed point used in the ideal sequence is the actual ground-field point. -/
def rationalPointImageIso {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) : Spec (.of K) ≅ p.ker.subscheme := by
  let := isClosedImmersion_of_comp_eq_id f p hp
  exact asIso p.toImage

end
end SteinerGeometry
