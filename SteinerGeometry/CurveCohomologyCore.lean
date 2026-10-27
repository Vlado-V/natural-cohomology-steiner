import SteinerGeometry.NativeCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic
import OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

abbrev χ {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) : ℤ :=
  CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M

theorem cohomology_isZero_of_flasque {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (hM : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (q : ℕ) : IsZero (H p M (q + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact OAI.AlgebraicGeometry.SheafCohomology.FlasqueVanishing.Projective.sheafH_subsingleton_of_flasque
    (TopCat.of X) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (fun i => hM.epi i.op) q

theorem curve_cohomology_above_one {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (M : X.Modules) (q : ℕ) (hq : 2 ≤ q) : IsZero (H p M q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing.Projective.GrothendieckVanishing
    (TopCat.of X) q (lt_of_le_of_lt hd (by exact_mod_cast (show 1 < q by omega)))
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)

theorem curve_euler_eq_h0_sub_h1 {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1) (M : X.Modules) :
    χ p M = (Module.finrank ℂ (H p M 0) : ℤ) - Module.finrank ℂ (H p M 1) := by
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M = _
  rw [CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sum p M 2
    (fun q hq => curve_cohomology_above_one p hd M q hq)]
  simp [Finset.sum_range_succ, sub_eq_add_neg]

theorem positive_euler_has_section {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1) (M : X.Modules)
    (hpos : 0 < χ p M) :
    ∃ s : Line.Bundles.structureModule X ⟶ M, s ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hsec : Subsingleton Γ(M, ⊤) := by
    constructor
    intro x y
    apply (Global.Sections.moduleSectionHomEquiv M).symm.injective
    exact (hn _).trans (hn _).symm
  have hzero : Subsingleton (H p M 0) :=
    (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M).toEquiv.subsingleton_congr.mpr hsec
  let _ := hzero
  have he := curve_euler_eq_h0_sub_h1 p hd M
  rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero] at he
  have hn0 : (0 : ℤ) ≤ Module.finrank ℂ (H p M 1) := Nat.cast_nonneg _
  omega

theorem flasqueModule_isZero_of_sections {X : Scheme.{0}} (M : X.Modules)
    (hf : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (h0 : Subsingleton Γ(M, ⊤)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  have he := hf.epi (homOfLE (show U ≤ ⊤ from le_top)).op
  obtain ⟨t, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).mp he s
  have ht : t = 0 := h0.elim _ _
  simp only [ht, map_zero]
  rfl

theorem h0_isZero_of_sections_zero {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (hs : ∀ s : Line.Bundles.structureModule X ⟶ M, s = 0) :
    IsZero (H p M 0) := by
  have hsec : Subsingleton Γ(M, ⊤) := by
    constructor
    intro x y
    apply (Global.Sections.moduleSectionHomEquiv M).symm.injective
    exact (hs _).trans (hs _).symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M).toEquiv.subsingleton_congr.mpr hsec


end SteinerGeometry.EllipticCohomology
