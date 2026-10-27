module

public import SteinerGeometry.CyclicLabels
public import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalDegree
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelTorsor

set_option backward.privateInPublic true
@[expose] public section

/-! Actual cyclic subgroup schemes and their exact-kernel and torsor comparisons. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry
open AbelianModuli.HilbertConstruction
open AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

namespace SteinerGeometry

variable {S : Scheme}

abbrev cyclicGroup (n : ℕ) := etaleGroupScheme S (Multiplicative (ZMod n))
abbrev planeGroup (n : ℕ) := etaleGroupScheme S (Multiplicative (Fin 2 → ZMod n))

/-- Full level identifies the represented constant plane with actual torsion. -/
def planeTorsionIso (A : Abelian.Schemes.AbelianScheme 1 S) {n : ℕ} (level : A.FullLevel n) :
    planeGroup n ≅ Grp.mk (A.torsionScheme n) :=
  (yonedaGrpFullyFaithful (C := Over S)).preimageIso
    (etaleGroupPointIso S (Multiplicative (Fin 2 → ZMod n)) ≪≫
      level ≪≫ (A.torsionSchemeYonedaIso n).symm)

/-- The represented torsion inclusion preserves its group law. -/
private theorem torsionInclusion_isMonHom (A : Abelian.Schemes.AbelianScheme 1 S) (n : ℕ) :
    IsMonHom (A.torsionInclusion n) where
  one_hom := by
    have h := congrArg (fun x : A.torsionPoints n (𝟙_ (Over S)) => x.val)
      (((A.torsionSchemeYonedaIso n).hom.app (Opposite.op (𝟙_ (Over S)))).hom.map_one)
    change (1 : 𝟙_ (Over S) ⟶ A.torsionScheme n) ≫ A.torsionInclusion n = 1 at h
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h
  mul_hom := by
    let T := A.torsionScheme n
    let i := A.torsionInclusion n
    have h := congrArg (fun x : A.torsionPoints n (T ⊗ T) => x.val)
      (((A.torsionSchemeYonedaIso n).hom.app (Opposite.op (T ⊗ T))).hom.map_mul (fst T T) (snd T T))
    change (fst T T * snd T T) ≫ i = (fst T T ≫ i) * (snd T T ≫ i) at h
    have hp : lift (fst T T ≫ i) (snd T T ≫ i) = i ⊗ₘ i := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, tensorHom_fst]; rfl
      · simp only [lift_snd, tensorHom_snd]; rfl
    exact (congrArg (fun f => f ≫ i) (MonObj.mul_eq_mul (M := T))).trans
      (h.trans (congrArg (fun f => f ≫ μ[A.scheme]) hp))

/-- An actual closed cyclic subgroup in the original elliptic curve. -/
def cyclicInclusion (A : Abelian.Schemes.AbelianScheme 1 S) {n : ℕ} (level : A.FullLevel n) :
    (cyclicGroup n).X ⟶ A.scheme :=
  (etaleGroupMap S (cyclicLabels n)).hom.hom ≫
    (planeTorsionIso A level).hom.hom.hom ≫ A.torsionInclusion n

instance cyclicInclusion_isMonHom (A : Abelian.Schemes.AbelianScheme 1 S) {n : ℕ} (level : A.FullLevel n) :
    IsMonHom (cyclicInclusion A level) := by
  let := torsionInclusion_isMonHom A n
  unfold cyclicInclusion
  infer_instance

theorem cyclicInclusion_closed (A : Abelian.Schemes.AbelianScheme 1 S) {n : ℕ} [NeZero n]
    (level : A.FullLevel n) : IsClosedImmersion (cyclicInclusion A level).left := by
  let : IsClosedImmersion (etaleGroupMap S (cyclicLabels n)).hom.hom.left :=
    etaleGroupMap_closed S (cyclicLabels n) (cyclicLabels_injective n)
  let e := (Grp.forget (Over S)).mapIso (planeTorsionIso A level)
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have h₁ : IsClosedImmersion e.hom.left := inferInstance
  have h₂ : IsClosedImmersion (A.torsionInclusion n).left := inferInstance
  have h₃ : IsClosedImmersion (e.hom.left ≫ (A.torsionInclusion n).left) :=
    @IsClosedImmersion.comp _ _ _ e.hom.left (A.torsionInclusion n).left h₁ h₂
  exact @IsClosedImmersion.comp _ _ _ (etaleGroupMap S (cyclicLabels n)).hom.hom.left
    (e.hom.left ≫ (A.torsionInclusion n).left) inferInstance h₃

theorem cyclicInclusion_killed (A : Abelian.Schemes.AbelianScheme 1 S) {n : ℕ} (level : A.FullLevel n) :
    cyclicInclusion A level ^ n = 1 := by
  unfold cyclicInclusion
  rw [← MonObj.comp_pow, ← MonObj.comp_pow, A.torsionInclusion_pow,
    MonObj.comp_one, MonObj.comp_one]

/-- A specified exact kernel is isomorphic to the literal zero-fiber kernel. -/
def exactKernelIso {S : Scheme} {g h : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (q : A.Isogeny B) (H : Over S) (i : H ⟶ A.scheme) [Mono i]
    (hk : ∀ (T : Over S) (a : T ⟶ A.scheme),
      a ≫ q.hom = 1 ↔ ∃! x : T ⟶ H, x ≫ i = a) : H ≅ q.kernelScheme := by
  have hiq : i ≫ q.hom = 1 := (hk H i).mpr
    ⟨𝟙 H, Category.id_comp i, fun x hx => (cancel_mono i).mp (hx.trans (Category.id_comp i).symm)⟩
  let f : H ⟶ q.kernelScheme := (q.kernelSchemePointsEquiv H).symm ⟨i, hiq⟩
  have hf : f ≫ q.kernelInclusion = i :=
    congrArg Subtype.val ((q.kernelSchemePointsEquiv H).apply_symm_apply ⟨i, hiq⟩)
  let hjExists := (hk q.kernelScheme q.kernelInclusion).mp q.kernelInclusion_comp
  let j := Classical.choose hjExists
  have hj : j ≫ i = q.kernelInclusion := (Classical.choose_spec hjExists).1
  have hm : Mono q.kernelInclusion :=
    Functor.mono_of_mono_map (Over.forget S) (inferInstanceAs (Mono q.kernelInclusion.left))
  refine ⟨f, j, ?_, ?_⟩
  · apply (cancel_mono i).mp
    simp only [Category.assoc, hj, hf, Category.id_comp]
  · apply (cancel_mono q.kernelInclusion).mp
    simp only [Category.assoc, hf, hj, Category.id_comp]

/-- The kernel identification retains the specified subgroup inclusion. -/
theorem exactKernelIso_comp {S : Scheme} {g h : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (q : A.Isogeny B) (H : Over S) (i : H ⟶ A.scheme) [Mono i]
    (hk : ∀ (T : Over S) (a : T ⟶ A.scheme),
      a ≫ q.hom = 1 ↔ ∃! x : T ⟶ H, x ≫ i = a) :
    (exactKernelIso q H i hk).hom ≫ q.kernelInclusion = i := by
  unfold exactKernelIso
  dsimp only
  exact congrArg Subtype.val ((q.kernelSchemePointsEquiv H).apply_symm_apply _)

/-- On a connected target, the order of the constant kernel is the degree everywhere. -/
theorem isogeny_degree_of_cyclicKernel {D C : Abelian.Schemes.AbelianScheme 1 S}
    {n : ℕ} [NeZero n] (q : D.Isogeny C) [Etale q.hom.left]
    [PreconnectedSpace C.scheme.left] (e : (cyclicGroup (S := S) n).X ≅ q.kernelScheme)
    (s : S) (c : C.scheme.left) : q.hom.left.finrank c = n := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have hd : q.kernelScheme.hom.finrank s = n := by
    have hh : (cyclicGroup (S := S) n).X.hom.finrank s = n :=
      (ConstantScheme.GlobalDegree.constantScheme_finrank
        (Multiplicative (ZMod n)) s).trans (by simp)
    rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso] at hh
    exact hh
  exact (q.hom.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace
    c (η[C.scheme].left s)).trans ((q.kernelScheme_finrank s).symm.trans hd)

/-- The degree and kernel refer to the actual finite-flat map. -/
structure CyclicEtaleIsogeny (D : Abelian.Schemes.AbelianScheme 1 S) (n : ℕ) where
  target : Abelian.Schemes.AbelianScheme 1 S
  map : D.Isogeny target
  etale : Etale map.hom.left
  degree : ∀ c : target.scheme.left, map.hom.left.finrank c = n
  kernelIso : (cyclicGroup n).X ≅ map.kernelScheme
  kernelIso_isMonHom : IsMonHom (kernelIso.hom ≫ map.kernelInclusion)

attribute [instance] CyclicEtaleIsogeny.etale CyclicEtaleIsogeny.kernelIso_isMonHom

namespace CyclicEtaleIsogeny

/-- Assemble an actual cyclic quotient from its exact subgroup-kernel equality. -/
def ofExactKernel [Nonempty S] {D C : Abelian.Schemes.AbelianScheme 1 S}
    {n : ℕ} [NeZero n] [PreconnectedSpace C.scheme.left]
    (level : D.FullLevel n) (q : D.Isogeny C) [Etale q.hom.left]
    (hk : ∀ (T : Over S) (a : T ⟶ D.scheme),
      a ≫ q.hom = 1 ↔ ∃! x : T ⟶ (cyclicGroup n).X, x ≫ cyclicInclusion D level = a) :
    CyclicEtaleIsogeny D n := by
  have : Mono (cyclicInclusion D level) := by
    let : IsClosedImmersion (cyclicInclusion D level).left := cyclicInclusion_closed D level
    exact Over.mono_of_mono_left _
  let e := exactKernelIso q (cyclicGroup n).X (cyclicInclusion D level) hk
  refine ⟨C, q, inferInstance, ?_, e, ?_⟩
  · exact fun c => isogeny_degree_of_cyclicKernel q e (Classical.choice inferInstance) c
  · change IsMonHom ((exactKernelIso q (cyclicGroup n).X (cyclicInclusion D level) hk).hom ≫ q.kernelInclusion)
    rw [exactKernelIso_comp]
    infer_instance


variable {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ} (q : CyclicEtaleIsogeny D n)

/-- The actual self-fiber-product is the source times the constant cyclic group. -/
def torsorIso : D.scheme ⊗ (cyclicGroup n).X ≅ Limits.pullback q.map.hom q.map.hom :=
  whiskerLeftIso D.scheme q.kernelIso ≪≫ q.map.kernelTorsorIso

@[reassoc (attr := simp)]
theorem torsorIso_hom_fst :
    q.torsorIso.hom ≫ Limits.pullback.fst q.map.hom q.map.hom =
      fst D.scheme (cyclicGroup n).X := by
  simp only [torsorIso, Iso.trans_hom, whiskerLeftIso_hom,
    Abelian.Schemes.AbelianScheme.Isogeny.kernelTorsorIso, Category.assoc,
    Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_fst, whiskerLeft_fst]

/-- The second projection translates the source by the literal kernel point. -/
theorem torsorIso_hom_snd :
    q.torsorIso.hom ≫ Limits.pullback.snd q.map.hom q.map.hom =
      fst D.scheme (cyclicGroup n).X *
        (snd D.scheme (cyclicGroup n).X ≫ q.kernelIso.hom ≫ q.map.kernelInclusion) := by
  simp only [torsorIso, Iso.trans_hom, whiskerLeftIso_hom,
    Abelian.Schemes.AbelianScheme.Isogeny.kernelTorsorIso, Category.assoc,
    Abelian.Schemes.AbelianScheme.Isogeny.kernelActionPair_snd, MonObj.comp_mul,
    whiskerLeft_fst, whiskerLeft_snd_assoc]

end CyclicEtaleIsogeny

end SteinerGeometry
