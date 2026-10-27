module

public import SteinerGeometry.CurveCohomologyCore
public import SteinerGeometry.NativeCohomologyAdditive
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorBiproductDimension
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance curveEulerBiproduct_hasFiniteBiproducts (X : Scheme.{0}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite direct sums add Euler characteristics on a curve. Only finiteness
of H⁰ and H¹ is needed, since higher cohomology already vanishes. -/
theorem curve_biproduct_euler
    {X : Scheme.{0}} [IsNoetherian X] (p : X ⟶ Spec (.of ℂ))
    (hd : topologicalKrullDim X ≤ 1) {I : Type} [Fintype I]
    (M : I → X.Modules)
    (h0 : ∀ i, Module.Finite ℂ (H p (M i) 0))
    (h1 : ∀ i, Module.Finite ℂ (H p (M i) 1)) :
    χ p (⨁ M) = ∑ i, χ p (M i) := by
  rw [curve_euler_eq_h0_sub_h1 p hd]
  rw [Additive.FunctorBiproductDimension.additive_functor_biproduct_finrank
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) 0) M h0]
  rw [Additive.FunctorBiproductDimension.additive_functor_biproduct_finrank
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) 1) M h1]
  simp_rw [curve_euler_eq_h0_sub_h1 p hd]
  simp only [Nat.cast_sum, Finset.sum_sub_distrib]

/-- Euler characteristic is unchanged under an actual sheaf isomorphism. -/
theorem curve_euler_eq_of_iso
    {X : Scheme.{0}} [IsNoetherian X] (p : X ⟶ Spec (.of ℂ))
    (hd : topologicalKrullDim X ≤ 1) {M N : X.Modules} (e : M ≅ N) :
    χ p M = χ p N := by
  rw [curve_euler_eq_h0_sub_h1 p hd, curve_euler_eq_h0_sub_h1 p hd]
  have h0 := ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) 0).mapIso e).toLinearEquiv.finrank_eq
  have h1 := ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) 1).mapIso e).toLinearEquiv.finrank_eq
  rw [h0, h1]

/-- Affine direct image preserves the actual cohomological Euler characteristic. -/
theorem affine_pushforward_euler
    {X Y : Scheme.{0}} [Y.IsSeparated] (f : X ⟶ Y) [IsAffineHom f]
    (p : Y ⟶ Spec (.of ℂ)) (M : X.Modules) [M.IsQuasicoherent] :
    χ (f ≫ p) M = χ p ((Scheme.Modules.pushforward f).obj M) := by
  unfold χ CohomologyEulerCharacteristic.coefficientEulerCharacteristic
  apply finsum_congr
  intro q
  exact congrArg (fun n : ℕ => (-1 : ℤ)^q * (n : ℤ))
    (Affine.PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso f p M q).toLinearEquiv.finrank_eq

/-- A nontrivial finite self-cover whose character summands have the structure
Euler characteristic forces χ(O)=0. This is the arithmetic end of the character argument. -/
theorem structure_euler_zero_of_self_decomposition
    {X : Scheme.{0}} [IsNoetherian X] [X.IsSeparated]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (f : X ⟶ X) [IsAffineHom f] (hf : f ≫ p = p)
    {I : Type} [Fintype I] (hI : Fintype.card I ≠ 1)
    (M : I → X.Modules)
    (e : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) ≅ ⨁ M)
    (h0 : ∀ i, Module.Finite ℂ (H p (M i) 0))
    (h1 : ∀ i, Module.Finite ℂ (H p (M i) 1))
    (hχ : ∀ i, χ p (M i) = χ p (Line.Bundles.structureModule X)) :
    χ p (Line.Bundles.structureModule X) = 0 := by
  let _ : (Line.Bundles.structureModule X).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have ha := affine_pushforward_euler f p (Line.Bundles.structureModule X)
  rw [hf] at ha
  have he := curve_euler_eq_of_iso p hd e
  have hb := curve_biproduct_euler p hd M h0 h1
  have hx : (Fintype.card I : ℤ) * χ p (Line.Bundles.structureModule X) =
      χ p (Line.Bundles.structureModule X) := by
    rw [← ha, hb] at he
    simpa only [hχ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he.symm
  have hc : (Fintype.card I : ℤ) ≠ 1 := by exact_mod_cast hI
  have hz : ((Fintype.card I : ℤ) - 1) * χ p (Line.Bundles.structureModule X) = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

end SteinerGeometry.EllipticCohomology
