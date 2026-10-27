import SteinerGeometry.LaurentResidueLinear
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights

/-! # Actual coordinate multiplication on homogeneous Laurent Čech cochains -/
noncomputable section
namespace SteinerGeometry.LaurentCochainMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open LaurentMultiplication ProjectiveResiduePairing
open scoped BigOperators
universe u

variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

abbrev Index (q : ℕ) := OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) q
abbrev Factor (d : ℤ) {q : ℕ} (a : Index (σ := σ) q) :=
  ModuleCat.of Γ(Spec (.of R), ⊤)
    (AddMonoidAlgebra Γ(Spec (.of R), ⊤) (Allowed (fun i => (a.val i).down) d))
abbrev Term (d : ℤ) (q : ℕ) :=
  LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
    (R := R) (σ := σ) d q

def projection (d : ℤ) (q : ℕ) (a : Index (σ := σ) q) :
    Term (R := R) (σ := σ) d q ⟶ Factor (R := R) d a := Pi.π _ a

/-- Coordinate multiplication on every genuine Čech factor. -/
def coordinateTermMap (d : ℤ) (j : σ) (q : ℕ) :
    Term (R := R) (σ := σ) d q ⟶ Term (R := R) (σ := σ) (d + 1) q :=
  Limits.Pi.map (fun a : Index (σ := σ) q =>
    ModuleCat.ofHom (shiftFactor (R := R) (fun i => (a.val i).down) d j))

@[reassoc] theorem coordinateTermMap_projection (d : ℤ) (j : σ) (q : ℕ)
    (a : Index (σ := σ) q) :
    coordinateTermMap (R := R) d j q ≫ projection (d + 1) q a =
      projection d q a ≫ ModuleCat.ofHom
        (shiftFactor (R := R) (fun i => (a.val i).down) d j) := Pi.map_π _ a

/-- The local exponent shift commutes with each actual ordered Čech coface. -/
theorem coordinateTermMap_coface (d : ℤ) (j : σ) (q : ℕ) (k : Fin (q + 2)) :
    coordinateTermMap (R := R) d j q ≫
        LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
          (R := R) (σ := σ) (d + 1) q k =
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d q k ≫ coordinateTermMap (R := R) d j (q + 1) := by
  apply Pi.hom_ext
  intro a
  let cS := LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
    (R := R) (σ := σ) d q k
  let cT := LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
    (R := R) (σ := σ) (d + 1) q k
  let pS := projection (R := R) d (q + 1) a
  let pT := projection (R := R) (d + 1) (q + 1) a
  let pD := projection (R := R) d q (a.delete k)
  let pDT := projection (R := R) (d + 1) q (a.delete k)
  let sD := ModuleCat.ofHom (shiftFactor (R := R) (fun i => ((a.delete k).val i).down) d j)
  let sA := ModuleCat.ofHom (shiftFactor (R := R) (fun i => (a.val i).down) d j)
  let dS := ModuleCat.ofHom
    (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d)
  let dT := ModuleCat.ofHom
    (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k (d + 1))
  have hpS : cS ≫ pS = pD ≫ dS :=
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface_comp_π
      (R := R) d q k a
  have hpT : cT ≫ pT = pDT ≫ dT :=
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface_comp_π
      (R := R) (d + 1) q k a
  have hmD : coordinateTermMap (R := R) d j q ≫ pDT = pD ≫ sD :=
    coordinateTermMap_projection d j q (a.delete k)
  have hmA : coordinateTermMap (R := R) d j (q + 1) ≫ pT = pS ≫ sA :=
    coordinateTermMap_projection d j (q + 1) a
  have hs : sD ≫ dT = dS ≫ sA := by
    apply ModuleCat.hom_ext
    exact (shiftFactor_delete (R := R) a k d j).symm
  change (coordinateTermMap (R := R) d j q ≫ cT) ≫ pT =
    (cS ≫ coordinateTermMap (R := R) d j (q + 1)) ≫ pT
  calc
    _ = coordinateTermMap (R := R) d j q ≫ (cT ≫ pT) := Category.assoc _ _ _
    _ = coordinateTermMap (R := R) d j q ≫ (pDT ≫ dT) := congrArg (_ ≫ ·) hpT
    _ = (coordinateTermMap (R := R) d j q ≫ pDT) ≫ dT := (Category.assoc _ _ _).symm
    _ = (pD ≫ sD) ≫ dT := congrArg (· ≫ dT) hmD
    _ = pD ≫ (sD ≫ dT) := Category.assoc _ _ _
    _ = pD ≫ (dS ≫ sA) := congrArg (pD ≫ ·) hs
    _ = (pD ≫ dS) ≫ sA := (Category.assoc _ _ _).symm
    _ = (cS ≫ pS) ≫ sA := congrArg (· ≫ sA) hpS.symm
    _ = cS ≫ (pS ≫ sA) := Category.assoc _ _ _
    _ = cS ≫ (coordinateTermMap (R := R) d j (q + 1) ≫ pT) := congrArg (cS ≫ ·) hmA.symm
    _ = _ := (Category.assoc _ _ _).symm

/-- Hence coordinate multiplication commutes with the alternating differential. -/
theorem coordinateTermMap_differential (d : ℤ) (j : σ) (q : ℕ) :
    coordinateTermMap (R := R) d j q ≫
        LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) (d + 1) q =
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d q ≫ coordinateTermMap (R := R) d j (q + 1) := by
  rw [LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential,
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, coordinateTermMap_coface]

/-- Coordinate multiplication as a morphism of the actual native Laurent
Čech complexes. -/
def coordinateMap (base : σ) (d : ℤ) (j : σ) :
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base d ⟶
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base (d + 1) :=
  CochainComplex.ofHom (fun q => coordinateTermMap d j q) (fun q => by
    rw [TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d,
      TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    exact coordinateTermMap_differential d j q)

@[simp] theorem coordinateMap_f (base : σ) (d : ℤ) (j : σ) (q : ℕ) :
    (coordinateMap (R := R) base d j).f q = coordinateTermMap d j q := rfl

section LinearForm
variable [Fintype σ]

def linearFormTermMap (d : ℤ) (L : σ → Γ(Spec (.of R), ⊤)) (q : ℕ) :
    Term (R := R) (σ := σ) d q ⟶ Term (R := R) (σ := σ) (d + 1) q :=
  ∑ j, L j • coordinateTermMap (R := R) d j q

theorem linearFormTermMap_projection (d : ℤ) (L : σ → Γ(Spec (.of R), ⊤))
    (q : ℕ) (a : Index (σ := σ) q) :
    linearFormTermMap d L q ≫ projection (d + 1) q a =
      projection d q a ≫ ModuleCat.ofHom
        (LaurentResidueShift.linearFormFactor (fun i => (a.val i).down) d L) := by
  rw [linearFormTermMap, Preadditive.sum_comp]
  simp only [Linear.smul_comp, coordinateTermMap_projection, ← Linear.comp_smul]
  rw [← Preadditive.comp_sum]
  congr 1
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LaurentResidueShift.linearFormFactor]
  rfl

theorem linearFormTermMap_differential (d : ℤ) (L : σ → Γ(Spec (.of R), ⊤)) (q : ℕ) :
    linearFormTermMap d L q ≫
        LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) (d + 1) q =
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d q ≫ linearFormTermMap d L (q + 1) := by
  rw [linearFormTermMap, linearFormTermMap, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Linear.smul_comp, Linear.comp_smul, coordinateTermMap_differential]

/-- Linear-form multiplication as an actual native cochain-complex map. -/
def linearFormMap (base : σ) (d : ℤ) (L : σ → Γ(Spec (.of R), ⊤)) :
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base d ⟶
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base (d + 1) :=
  CochainComplex.ofHom (fun q => linearFormTermMap d L q) (fun q => by
    rw [TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d,
      TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    exact linearFormTermMap_differential d L q)

@[simp] theorem linearFormMap_f (base : σ) (d : ℤ) (L : σ → Γ(Spec (.of R), ⊤)) (q : ℕ) :
    (linearFormMap (R := R) base d L).f q = linearFormTermMap d L q := rfl

end LinearForm

/-- Full-negative coefficient extraction from the unique top Čech factor,
reindexed by complementary ordinary monomials. -/
def topResidueProjection (n m : ℕ) (d : ℤ)
    (hd : d = -(m : ℤ) - ((n + 1 : ℕ) : ℤ)) :
    Term (R := R) (σ := Fin (n + 1)) d n →ₗ[Γ(Spec (.of R), ⊤)]
      ResidueCoefficients (Fin (n + 1)) Γ(Spec (.of R), ⊤) m :=
  (LaurentResidueShift.residueProjection (R := R) (fun i : Fin (n + 1) => i)
    (fun i => ⟨i, rfl⟩) m d (by simpa only [Fintype.card_fin] using hd)).comp
    (projection (R := R) d n (fullIndex n)).hom

/-- The actual top-degree cochain map is the residue transpose of
polynomial multiplication by the same linear form. -/
theorem linearFormTermMap_topResidue (n m : ℕ) (d : ℤ)
    (hsource : d = -((m + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
    (htarget : d + 1 = -(m : ℤ) - ((n + 1 : ℕ) : ℤ))
    (L : Fin (n + 1) → Γ(Spec (.of R), ⊤)) :
    (topResidueProjection (R := R) n m (d + 1) htarget).comp
        (linearFormTermMap d L n).hom =
      (multiplyResidueLinearForm m L).comp
        (topResidueProjection (R := R) n (m + 1) d hsource) := by
  apply LinearMap.ext
  intro x
  have hp := ConcreteCategory.congr_hom
    (linearFormTermMap_projection d L n (fullIndex n)) x
  change (projection (R := R) (d + 1) n (fullIndex n)).hom
      ((linearFormTermMap d L n).hom x) =
    LaurentResidueShift.linearFormFactor (fun i : Fin (n + 1) => i) d L
      ((projection (R := R) d n (fullIndex n)).hom x) at hp
  change LaurentResidueShift.residueProjection (R := R) (fun i : Fin (n + 1) => i)
      (fun i => ⟨i, rfl⟩) m (d + 1) _
      ((projection (R := R) (d + 1) n (fullIndex n)).hom
        ((linearFormTermMap d L n).hom x)) = _
  rw [hp]
  exact LinearMap.congr_fun
    (LaurentResidueShift.residueProjection_linearFormFactor
      (fun i : Fin (n + 1) => i) (fun i => ⟨i, rfl⟩) m d
      (by simpa only [Fintype.card_fin] using hsource)
      (by simpa only [Fintype.card_fin] using htarget) L)
    ((projection (R := R) d n (fullIndex n)).hom x)

theorem linearFormMap_topResidue (n m : ℕ) (base : Fin (n + 1)) (d : ℤ)
    (hsource : d = -((m + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
    (htarget : d + 1 = -(m : ℤ) - ((n + 1 : ℕ) : ℤ))
    (L : Fin (n + 1) → Γ(Spec (.of R), ⊤)) :
    (topResidueProjection (R := R) n m (d + 1) htarget).comp
        ((linearFormMap base d L).f n).hom =
      (multiplyResidueLinearForm m L).comp
        (topResidueProjection (R := R) n (m + 1) d hsource) :=
  linearFormTermMap_topResidue n m d hsource htarget L

end SteinerGeometry.LaurentCochainMap
