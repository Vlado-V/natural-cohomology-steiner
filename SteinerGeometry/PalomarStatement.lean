module

public import Mathlib

@[expose] public section

/-! # Natural cohomology of general Steiner bundles

Theorem 1.1 of the included paper, with actual projective space, the coordinate
hyperplane ideal `O(-1)`, its tensor inverse `O(1)`, and Ext-based sheaf
cohomology. All definitions needed to read the statement are given here;
this module imports only Mathlib. One principal open simultaneously controls
all homogeneous matrix ranks and every integer twist of each actual cokernel.
-/

noncomputable section

namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotient.HomogeneousIdeal

open _root_.HomogeneousIdeal





open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [CommRing A]
  [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The quotient map `A → A ⧸ I`, as a linear map over `R`. -/
abbrev mkL : A →ₗ[R] A ⧸ I.toIdeal :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

/-- The grading on `A ⧸ I` induced by a grading on `A` and a homogeneous ideal `I`:
the `n`-th piece is the image of `𝒜 n`. -/
def quotientGrading (n : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 n).map (mkL I)

lemma mk_mem_quotientGrading {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I.toIdeal a ∈ quotientGrading I n :=
  Submodule.mem_map.mpr ⟨a, ha, rfl⟩

instance : SetLike.GradedMonoid (quotientGrading I) where
  one_mem := Submodule.mem_map.mpr
    ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ R I.toIdeal)⟩
  mul_mem := by
    intro m n x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr
      ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mkₐ R I.toIdeal) a b⟩

/-- The componentwise map `⨁ n, 𝒜 n →+ ⨁ n, (𝒜 n).map mk` induced by the quotient
map. -/
def quotientDecomposeAux : (⨁ n, 𝒜 n) →+ ⨁ n, quotientGrading I n :=
  DFinsupp.mapRange.addMonoidHom fun n => ((mkL I).submoduleMap (𝒜 n)).toAddMonoidHom

lemma quotientDecomposeAux_apply (x : ⨁ n, 𝒜 n) (n : ι) :
    quotientDecomposeAux I x n = (mkL I).submoduleMap (𝒜 n) (x n) :=
  rfl

lemma quotientDecomposeAux_of (n : ι) (a : 𝒜 n) :
    quotientDecomposeAux I (DirectSum.of _ n a) =
      DirectSum.of _ n ((mkL I).submoduleMap (𝒜 n) a) := by
  classical
  exact DFinsupp.mapRange_single (hf := fun n => map_zero _)

lemma quotientDecomposeAux_coe (x : ⨁ n, 𝒜 n) :
    DirectSum.coeAddMonoidHom (quotientGrading I) (quotientDecomposeAux I x) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.coeAddMonoidHom 𝒜 x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n a =>
    rw [quotientDecomposeAux_of]
    exact (DirectSum.coeAddMonoidHom_of (quotientGrading I) n _).trans
      (congrArg (Ideal.Quotient.mk I.toIdeal) (DirectSum.coeAddMonoidHom_of 𝒜 n a)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The decomposition of the quotient ring: descend the decomposition of `A`.
Well-defined precisely because `I` is homogeneous. -/
def quotientDecompose (x : A ⧸ I.toIdeal) : ⨁ n, quotientGrading I n :=
  Quotient.liftOn' x (fun a => quotientDecomposeAux I (DirectSum.decompose 𝒜 a)) (by
    intro a b hab
    have hab' : a - b ∈ I.toIdeal := (Submodule.quotientRel_def _).mp hab
    ext n
    have hmem : ((DirectSum.decompose 𝒜 a n : A) - (DirectSum.decompose 𝒜 b n : A)) ∈
        I.toIdeal := by
      have h := (Submodule.IsHomogeneous.mem_iff 𝒜 I.isHomogeneous).mp hab' n
      rwa [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub] at h
    have key : Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n : A) =
        Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 b n : A) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    rw [quotientDecomposeAux_apply, quotientDecomposeAux_apply]
    exact key)

lemma quotientDecompose_mk (a : A) :
    quotientDecompose I (Ideal.Quotient.mk I.toIdeal a) =
      quotientDecomposeAux I (DirectSum.decompose 𝒜 a) :=
  rfl

lemma quotientDecompose_add (x y : A ⧸ I.toIdeal) :
    quotientDecompose I (x + y) = quotientDecompose I x + quotientDecompose I y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add, quotientDecompose_mk, quotientDecompose_mk, quotientDecompose_mk,
    DirectSum.decompose_add, map_add]

instance : DirectSum.Decomposition (quotientGrading I) where
  decompose' := quotientDecompose I
  left_inv x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotientDecompose_mk, quotientDecomposeAux_coe]
    congr 1
    exact (DirectSum.decompose 𝒜).symm_apply_apply a
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
      have h0 : (0 : A ⧸ I.toIdeal) = Ideal.Quotient.mk I.toIdeal 0 := by simp
      rw [map_zero, h0, quotientDecompose_mk]
      simp
    | of n a =>
      obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp a.2
      have h1 : (DirectSum.coeAddMonoidHom (quotientGrading I)) (DirectSum.of _ n a) =
          Ideal.Quotient.mk I.toIdeal b := by
        rw [DirectSum.coeAddMonoidHom_of, ← hba]; rfl
      rw [h1, quotientDecompose_mk, DirectSum.decompose_of_mem 𝒜 hb,
        quotientDecomposeAux_of]
      exact congrArg (DirectSum.of _ n) (Subtype.ext hba)
    | add x y hx hy =>
      rw [map_add, quotientDecompose_add, hx, hy]

/-- The quotient of a graded algebra by a homogeneous ideal is a graded algebra. -/
instance quotientGradingGradedAlgebra : GradedAlgebra (quotientGrading I) := ⟨⟩


/-- The quotient map `A → A ⧸ I` as a graded ring homomorphism onto the quotient
grading. -/
def quotientGradingHom : 𝒜 →+*ᵍ quotientGrading I where
  toRingHom := Ideal.Quotient.mk I.toIdeal
  map_mem := mk_mem_quotientGrading I

lemma quotientGradingHom_surjective :
    Function.Surjective (quotientGradingHom I) :=
  Ideal.Quotient.mk_surjective

@[simp]
lemma quotientGradingHom_apply (a : A) :
    quotientGradingHom I a = Ideal.Quotient.mk I.toIdeal a :=
  rfl

/-- Componentwise description of the quotient decomposition on classes. -/
lemma decompose_quotientGrading_mk_apply (a : A) (n : ι) :
    (DirectSum.decompose (quotientGrading I) (Ideal.Quotient.mk I.toIdeal a) n :
        A ⧸ I.toIdeal) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n) :=
  rfl

section Irrelevant

variable [PartialOrder ι] [CanonicallyOrderedAdd ι]

/-- The irrelevant ideal of the quotient grading is contained in the image of the
irrelevant ideal — the hypothesis of `Proj.map` for the quotient map. -/
lemma quotientGradingHom_irrelevant_le :
    HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      HomogeneousIdeal.map (quotientGradingHom I) (HomogeneousIdeal.irrelevant 𝒜) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    decompose_quotientGrading_mk_apply] at hx
  have hmem : a - (DirectSum.decompose 𝒜 a 0 : A) ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_sub]
    simp [DirectSum.sub_apply, DirectSum.decompose_coe, DirectSum.of_eq_same]
  have hval : Ideal.Quotient.mk I.toIdeal a =
      quotientGradingHom I (a - (DirectSum.decompose 𝒜 a 0 : A)) := by
    rw [quotientGradingHom_apply, map_sub, hx, sub_zero]
  rw [hval]
  exact Ideal.mem_map_of_mem _ hmem

end Irrelevant


end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotient.HomogeneousIdeal


namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial
open _root_.MvPolynomial
variable (R : Type*) {σ : Type*} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
lemma X_mem_homogeneousSubmodule_one (i : σ) :
    (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _)
end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial

namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial
noncomputable section
open _root_.MvPolynomial _root_.AlgebraicGeometry _root_.HomogeneousIdeal
universe u
variable {R : Type u} {σ : Type*} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The homogeneous ideal cutting out the coordinate hyperplane. -/
def coordinateHyperplaneIdeal (j : σ) :
    HomogeneousIdeal (homogeneousSubmodule σ R) :=
  ⟨Ideal.span {X j}, Ideal.homogeneous_span _ _ fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨1, SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R j⟩⟩
abbrev coordinateHyperplane (j : σ) :=
  Proj (GradedQuotient.HomogeneousIdeal.quotientGrading (coordinateHyperplaneIdeal (R := R) j))
def coordinateHyperplaneι (j : σ) :
    coordinateHyperplane (R := R) j ⟶ Proj (homogeneousSubmodule σ R) :=
  Proj.map (GradedQuotient.HomogeneousIdeal.quotientGradingHom (coordinateHyperplaneIdeal (R := R) j))
    (GradedQuotient.HomogeneousIdeal.quotientGradingHom_irrelevant_le (coordinateHyperplaneIdeal (R := R) j))
end
end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial

namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule
noncomputable section
open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
universe u
/-- The actual kernel of the structure sheaf map to the hyperplane's pushforward. -/
def idealModuleRaw {X Y : Scheme.{u}} (f : X ⟶ Y) : SheafOfModules Y.ringCatSheaf :=
  kernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
def idealModule {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Modules := idealModuleRaw f
end
end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule

namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial
open _root_.MvPolynomial _root_.AlgebraicGeometry
variable {R : Type*} {σ : Type*} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev coordinateOpen (i : σ) : (Proj (homogeneousSubmodule σ R)).Opens :=
  Proj.basicOpen (homogeneousSubmodule σ R) (X i)
end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial

namespace PalomarModel.SteinerGeometry
open CategoryTheory AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev projectiveSpace (R : Type u) [CommRing R] (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
end PalomarModel.SteinerGeometry

namespace PalomarSteiner
open CategoryTheory AlgebraicGeometry
open PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The standard affine chart where the i-th projective coordinate is nonzero. -/
abbrev coordinateOpen {n : ℕ} (i : Fin (n+1)) : (PalomarModel.SteinerGeometry.projectiveSpace R n).Opens :=
  MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
/-- The regular function X_k / X_i on the i-th affine chart, including k=i. -/
def coordinateRatio {n : ℕ} (i k : Fin (n+1)) :
    Γ(PalomarModel.SteinerGeometry.projectiveSpace R n, coordinateOpen (R := R) i) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)
    (MvPolynomial.X i)
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
      (HomogeneousLocalization.Away.mk _
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) 1 (MvPolynomial.X k)
        (by simpa using SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R k))
end PalomarSteiner

namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules
open _root_.AlgebraicGeometry
universe u
noncomputable def unitObj (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules
namespace PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule
open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
universe u
noncomputable def idealModuleToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    idealModule f ⟶ Invertible.Scheme.Modules.unitObj Y :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
end PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule

/-! Scalar parameters and the literal graded multiplication maps.
The `PalomarModel.Steiner` definitions below are repeated independently of the proof development. -/
noncomputable section
namespace PalomarModel.Steiner
open MvPolynomial Module
variable (K : Type*) [Field K] (n d : ℕ)
/-- The polynomial ring in `n` variables over the coefficient field. -/
abbrev Poly := MvPolynomial (Fin n) K
/-- Homogeneous polynomials of total degree `d`. -/
abbrev Forms := MvPolynomial.homogeneousSubmodule (Fin n) K d
/-- Degree-`d` monomials, indexed by multisets of variable indices. -/
def exponentEquiv : Sym (Fin n) d ≃ {e : Fin n →₀ ℕ // e.degree = d} :=
  Sym.equivNatSum (Fin n) d
/-- The usual monomial basis of the homogeneous polynomial space. -/
def formsBasis : Basis (Sym (Fin n) d) K (Forms K n d) := by
  rw [Forms, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (exponentEquiv n d).symm
variable (K : Type*) [Field K] (n : ℕ)
/-- An `a × c` matrix of linear forms in `n+1` variables. -/
abbrev LinearMatrix (a c : ℕ) := Matrix (Fin a) (Fin c) (Forms K (n+1) 1)
/-- Degree-`d` homogeneous vectors in the source. -/
abbrev MatrixSource (c d : ℕ) := Fin c → Forms K (n+1) d
/-- Degree-`d+1` homogeneous vectors in the target. -/
abbrev MatrixTarget (a d : ℕ) := Fin a → Forms K (n+1) (d+1)
variable {K n} {a c : ℕ}
/-- Multiplication by the matrix on homogeneous polynomial vectors. -/
def linearMatrixMap (L : LinearMatrix K n a c) (d : ℕ) :
    MatrixSource K n c d →ₗ[K] MatrixTarget K n a d where
  toFun v i := ⟨∑ j, (L i j).val * (v j).val, by
    apply IsHomogeneous.sum
    intro j _
    simpa only [Nat.add_comm] using (L i j).property.mul (v j).property⟩
  map_add' v w := by
    funext i
    apply Subtype.ext
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' k v := by
    funext i
    apply Subtype.ext
    simp [Finset.smul_sum]
/-- Maximal rank means image dimension equals the smaller endpoint dimension. -/
def LinearMatrixMaximalRank (L : LinearMatrix K n a c) (d : ℕ) : Prop :=
  finrank K (linearMatrixMap L d).range =
    min (finrank K (MatrixSource K n c d)) (finrank K (MatrixTarget K n a d))
/-- One parameter for every coefficient of every linear matrix entry. -/
abbrev LinearMatrixParameter (n a c : ℕ) := Fin a × Fin c × Sym (Fin (n+1)) 1
variable (K n)
/-- Specialize the universal matrix at its independent scalar coefficients. -/
def universalLinearMatrix (a c : ℕ) :
    (LinearMatrixParameter n a c → K) →ₗ[K] LinearMatrix K n a c where
  toFun u i j := ∑ b, u (i, j, b) • formsBasis K (n+1) 1 b
  map_add' u v := by
    funext i j
    change (∑ b, (u (i, j, b) + v (i, j, b)) • formsBasis K (n+1) 1 b) =
      (∑ b, u (i, j, b) • formsBasis K (n+1) 1 b) +
        (∑ b, v (i, j, b) • formsBasis K (n+1) 1 b)
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' k u := by
    funext i j
    change (∑ b, (k * u (i, j, b)) • formsBasis K (n+1) 1 b) =
      k • ∑ b, u (i, j, b) • formsBasis K (n+1) 1 b
    simp only [Finset.smul_sum, smul_smul]
end PalomarModel.Steiner
end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe uCore
namespace PalomarSteiner
variable {X : Scheme.{uCore}}

/-- The tensor product of sheaves of modules, obtained by sheafifying their sectionwise tensor product. -/
def tensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

/-- Nonnegative tensor powers, with the structure sheaf in degree zero. -/
def power (L : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => tensor (power L n) L

/-- The actual Ext-based cohomology of the underlying sheaf of abelian groups. -/
abbrev H (M : X.Modules) (q : ℕ) :=
  Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q

/-- At most one cohomological degree has a nonzero cohomology group. -/
def HasNaturalCohomology (M : X.Modules) : Prop :=
  ∃ d : ℕ, ∀ q : ℕ, q ≠ d → Subsingleton (H M q)
end PalomarSteiner


namespace PalomarSteiner
open CategoryTheory AlgebraicGeometry
universe uP
variable {X : Scheme.{uP}}
/-- Integer twists: positive powers of the inverse line P, negative powers of I. -/
def lineTwist (I P : X.Modules) : ℤ → X.Modules
  | .ofNat n => power P n
  | .negSucc n => power I (n+1)
/-- Twisting one fixed sheaf; no independent choice of a sheaf in each degree. -/
def twist (I P F : X.Modules) (b : ℤ) : X.Modules := tensor F (lineTwist I P b)
end PalomarSteiner

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open PalomarModel.OAI.AlgebraicGeometry.SheafCohomology.Projective
namespace PalomarSteiner
universe uChart
variable {K : Type uChart} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine chart D₊(X₀) of projective space. -/
def chartOpen (K : Type uChart) [CommRing K] (n : ℕ) :
    (PalomarModel.SteinerGeometry.projectiveSpace K n).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K)
    (MvPolynomial.X (0 : Fin (n+1)))

/-- Dehomogenization of a linear form: the section p/X₀ on D₊(X₀). -/
def chartValue
    (p : MvPolynomial.homogeneousSubmodule (Fin (n+1)) K 1) :
    Γ(PalomarModel.SteinerGeometry.projectiveSpace K n, chartOpen K n) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n+1)) K)
    (MvPolynomial.X (0 : Fin (n+1)))
    (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one K _) one_pos).hom.hom
      (HomogeneousLocalization.Away.mk _
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one K _) 1 p.val (by simpa using p.property))

/-- The ideal sheaf of the coordinate hyperplane X₀=0, a concrete O(-1). -/
abbrev ideal (K : Type uChart) [CommRing K] (n : ℕ) :=
  IdealModule.idealModule
    (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := K) (0 : Fin (n+1)))

/-- The canonical inclusion of the hyperplane ideal into the structure sheaf. -/
abbrev inclusion (K : Type uChart) [CommRing K] (n : ℕ) :=
  IdealModule.idealModuleToUnit
    (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := K) (0 : Fin (n+1)))

/-- The line map sends the uniquely normalized local generator of the actual
hyperplane ideal to the dehomogenization `p / X₀`. -/
def lineHasPolynomial
    (f : ideal K n ⟶ SheafOfModules.unit (PalomarModel.SteinerGeometry.projectiveSpace K n).ringCatSheaf)
    (p : MvPolynomial.homogeneousSubmodule (Fin (n+1)) K 1) : Prop :=
  ∃ s : Γ(ideal K n, chartOpen K n),
    (inclusion K n).val.app (op (chartOpen K n)) s =
      (show Γ(PalomarModel.SteinerGeometry.projectiveSpace K n, chartOpen K n) from 1) ∧
      f.val.app (op (chartOpen K n)) s = chartValue p

end PalomarSteiner
namespace PalomarSteiner
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe uStatement
variable {X : Scheme.{uStatement}}

/-- Finite direct sum of identical module sheaves. -/
abbrev copies (M : X.Modules) (a : ℕ) := ∐ fun _ : Fin a => M

/-- The projection to the `j`-th summand of a finite direct sum. -/
def projection (M : X.Modules) {a : ℕ} (j : Fin a) : copies M a ⟶ M :=
  Sigma.desc (fun k => if k = j then 𝟙 M else 0)

/-- The individual line-sheaf entry of a finite matrix of module morphisms. -/
def component {A B : X.Modules} {a b : ℕ}
    (f : copies A a ⟶ copies B b) (i : Fin a) (j : Fin b) : A ⟶ B :=
  Sigma.ι (fun _ : Fin a => A) i ≫ f ≫ projection B j

/-- Literal local freeness of rank `r`, stated using free module sheaves. -/
def HasRank (F : X.Modules) (r : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj F ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{uStatement} (Fin r)))

/-- The concrete module map has the given linear-form entries on the dense
standard chart. The normalized ideal generator and its image are specified
in `lineHasPolynomial`, rather than supplied as an unspecified encoding. -/
def RepresentsMatrix (K : Type uStatement) [Field K] (n t r : ℕ)
    (f : copies (ideal K n) t ⟶
      copies (SheafOfModules.unit (PalomarModel.SteinerGeometry.projectiveSpace K n).ringCatSheaf) (t+r))
    (M : PalomarModel.Steiner.LinearMatrix K n t (t+r)) : Prop :=
  ∀ i j, lineHasPolynomial (component f i j) (M i j)

/-- All assertions of Theorem 1.1 hold on one nonempty scalar principal open.
The sheaf `P`, fixed before the coefficients vary, is a tensor inverse of
`I = O(-1)`, hence an actual `O(1)`. Each coefficient matrix defines a single
cokernel sheaf; all integer twists of that same sheaf have natural cohomology. -/
def Statement : Prop :=
  ∀ (K : Type uStatement) [Field K] [CharZero K] (n t r : ℕ),
    1 ≤ n → 1 ≤ t → n ≤ r →
    ∃ P : (PalomarModel.SteinerGeometry.projectiveSpace K n).Modules,
      Nonempty (tensor P (ideal K n) ≅
        SheafOfModules.unit (PalomarModel.SteinerGeometry.projectiveSpace K n).ringCatSheaf) ∧
    ∃ D : MvPolynomial (PalomarModel.Steiner.LinearMatrixParameter n t (t+r)) K,
      (∃ a, MvPolynomial.eval a D ≠ 0) ∧
      ∀ a, MvPolynomial.eval a D ≠ 0 →
        (∀ d, PalomarModel.Steiner.LinearMatrixMaximalRank (PalomarModel.Steiner.universalLinearMatrix K n t (t+r) a) d) ∧
        ∃ f : copies (ideal K n) t ⟶
          copies (SheafOfModules.unit (PalomarModel.SteinerGeometry.projectiveSpace K n).ringCatSheaf) (t+r),
          RepresentsMatrix K n t r f (PalomarModel.Steiner.universalLinearMatrix K n t (t+r) a) ∧
          (ShortComplex.cokernelSequence f).ShortExact ∧
          HasRank (cokernel f) r ∧
          ∀ b : ℤ, HasNaturalCohomology (tensor (cokernel f) (lineTwist (ideal K n) P b))
end PalomarSteiner

