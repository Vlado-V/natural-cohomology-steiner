module

public import SteinerGeometry.LaurentCochainMap
public import SteinerGeometry.NegativeLaurentNaturality
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount

set_option backward.privateInPublic true
@[expose] public section

/-! Exact residue coordinates on native top Laurent cohomology. -/
noncomputable section
namespace SteinerGeometry.LaurentResidueHomology
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveResiduePairing LaurentCochainMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R]

abbrev degree (n m : ℕ) : ℤ := -(m : ℤ) - ((n + 1 : ℕ) : ℤ)

def monomialEquiv (n m : ℕ) :
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n+1)) (degree n m) //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} (Fin (n+1))))} ≃
      DegreeMonomial (Fin (n+1)) m where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i => (-e.val.val i - 1).toNat), by
    have hneg (i : Fin (n+1)) : e.val.val i < 0 := by
      have h : ULift.up i ∈ e.val.liftedNegativeSupport := by rw [e.property]; trivial
      exact h
    have hcast (i : Fin (n+1)) : ((-e.val.val i - 1).toNat : ℤ) = -e.val.val i - 1 := by
      have := hneg i
      omega
    have hs : ∑ i, e.val.val i = degree n m := by
      rw [← Finsupp.degree_eq_sum]
      exact e.val.property
    have hd : ((Finsupp.degree
        (Finsupp.equivFunOnFinite.symm (fun i => (-e.val.val i - 1).toNat)) : ℕ) : ℤ) = m := by
      rw [Finsupp.degree_eq_sum, Nat.cast_sum]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply, hcast]
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hs]
      simp [degree]
    exact_mod_cast hd⟩
  invFun a := ⟨LaurentResidueShift.complementaryWeight m (degree n m) (by simp) a, by
    apply Set.eq_univ_of_forall
    intro i
    change (LaurentResidueShift.complementaryWeight m (degree n m) _ a).val i.down < 0
    simp only [LaurentResidueShift.complementaryWeight_apply, negativeExponent]
    omega⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    have hneg : e.val.val i < 0 := by
      have h : ULift.up i ∈ e.val.liftedNegativeSupport := by rw [e.property]; trivial
      exact h
    simp only [LaurentResidueShift.complementaryWeight_apply, negativeExponent,
      Finsupp.equivFunOnFinite_symm_apply_apply]
    omega
  right_inv a := by
    apply Subtype.ext
    ext i
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply,
      LaurentResidueShift.complementaryWeight_apply, negativeExponent]
    omega

theorem monomialEquiv_symm_val (n m : ℕ) (a : DegreeMonomial (Fin (n+1)) m) :
    ((monomialEquiv.{u} n m).symm a).val =
      LaurentResidueShift.complementaryWeight m (degree n m) (by simp) a := by
  apply Subtype.ext
  ext i
  rfl

def fullNegativeToResidues (n m : ℕ) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u,u}
      (R := R) (σ := Fin (n+1)) (degree n m) n ≃ₗ[Γ(Spec (.of R),⊤)]
      ResidueCoefficients (Fin (n+1)) Γ(Spec (.of R),⊤) m :=
  (NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv
    (R := R) (degree n m) n (by simp)).trans
    (LinearEquiv.funCongrLeft Γ(Spec (.of R),⊤) Γ(Spec (.of R),⊤)
      (monomialEquiv.{u} n m).symm)

theorem fullNegativeCochainTopEquiv_apply (n : ℕ) (d : ℤ)
    (s : LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u,u}
      (R := R) (σ := Fin (n+1)) d n)
    (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n+1)) d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} (Fin (n+1))))}) :
    NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv
      (R := R) d n (by simp) s e = (s e).val (LaurentMultiplication.fullIndex n) := by
  change ((LinearEquiv.ofEq
    (OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (.of R),⊤) e.val.liftedNegativeSupport n)
    (OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (.of R),⊤)
      (Set.univ : Set (ULift.{u} (Fin (n+1)))) n) (by rw [e.property]))
      (s e)).val _ = _
  rw [LinearEquiv.coe_ofEq_apply]
  exact congrArg (s e).val (Subsingleton.elim _ _)

theorem fullNegativeToResidues_projection (n m : ℕ)
    (x : Term (R := R) (σ := Fin (n+1)) (degree n m) n) :
    fullNegativeToResidues (R := R) n m
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) (degree n m) n x) =
      topResidueProjection (R := R) n m (degree n m) rfl x := by
  funext a
  change NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCochainTopEquiv
    (R := R) (degree n m) n (by simp)
    (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
      (R := R) (degree n m) n x) ((monomialEquiv.{u} n m).symm a) = _
  rw [fullNegativeCochainTopEquiv_apply]
  rw [LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_apply]
  rw [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
    (R := R) (degree n m) _ (LaurentMultiplication.fullIndex n)
    (by intro i _; exact ⟨i,rfl⟩)]
  change _ = ((projection (R := R) (degree n m) n (LaurentMultiplication.fullIndex n)).hom x).coeff _
  congr 1

/-- Complementary residues give the native positive top homology equivalence. -/
def homologyResidueEquiv (p m : ℕ) (base : Fin (p+2)) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base (degree (p+1) m)).homology (p+1) ≃ₗ[Γ(Spec (.of R),⊤)]
      ResidueCoefficients (Fin (p+2)) Γ(Spec (.of R),⊤) m :=
  (NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles
    (R := R) base (degree (p+1) m) p).trans
    ((NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCyclesEquivCochain
      (R := R) (degree (p+1) m) (p+1)).trans
      (fullNegativeToResidues (R := R) (p+1) m))

theorem homologyResidueEquiv_eq_native (p m : ℕ) (base : Fin (p+2)) :
    homologyResidueEquiv (R := R) p m base =
      (NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients
        (R := R) base (degree (p+1) m) p (by simp)).trans
        (LinearEquiv.funCongrLeft Γ(Spec (.of R),⊤) Γ(Spec (.of R),⊤)
          (monomialEquiv.{u} (p+1) m).symm) := rfl

theorem homologyResidueEquiv_eq_projection (p m : ℕ) (base : Fin (p+2))
    (x : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base (degree (p+1) m)).homology (p+1)) :
    homologyResidueEquiv (R := R) p m base x =
      fullNegativeToResidues (R := R) (p+1) m
        ((NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection
          (R := R) base (degree (p+1) m) p).hom x) := by
  let E := NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles
    (R := R) base (degree (p+1) m) p
  obtain ⟨s,rfl⟩ := E.symm.surjective x
  have h := ConcreteCategory.congr_hom
    (NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeCyclesToHomology_projection
      (R := R) base (degree (p+1) m) p) s
  change (NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection
    (R := R) base (degree (p+1) m) p).hom (E.symm s) = s.val at h
  change fullNegativeToResidues (R := R) (p+1) m (E (E.symm s)).val = _
  rw [LinearEquiv.apply_symm_apply, h]

theorem homologyResidueEquiv_homologyπ (p m : ℕ) (base : Fin (p+2)) :
    let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base (degree (p+1) m)
    K.homologyπ (p+1) ≫ (homologyResidueEquiv (R := R) p m base).toModuleIso.hom =
      K.iCycles (p+1) ≫ ModuleCat.ofHom
        (topResidueProjection (R := R) (p+1) m (degree (p+1) m) rfl) := by
  dsimp only
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) base (degree (p+1) m)
  change homologyResidueEquiv (R := R) p m base ((K.homologyπ (p+1)).hom s) =
    topResidueProjection (R := R) (p+1) m (degree (p+1) m) rfl ((K.iCycles (p+1)).hom s)
  rw [homologyResidueEquiv_eq_projection]
  have h := ConcreteCategory.congr_hom
    (NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection_homologyπ
      (R := R) base (degree (p+1) m) p) s
  change (NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection
    (R := R) base (degree (p+1) m) p).hom ((K.homologyπ (p+1)).hom s) =
      LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) (degree (p+1) m) (p+1) ((K.iCycles (p+1)).hom s) at h
  rw [h]
  exact fullNegativeToResidues_projection (p+1) m _

def homologyResidueEquivAt (p m : ℕ) (base : Fin (p+2)) (d : ℤ)
    (hd : d = degree (p+1) m) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base d).homology (p+1) ≃ₗ[Γ(Spec (.of R),⊤)]
      ResidueCoefficients (Fin (p+2)) Γ(Spec (.of R),⊤) m := by
  subst d
  exact homologyResidueEquiv p m base

theorem homologyResidueEquivAt_homologyπ (p m : ℕ) (base : Fin (p+2))
    (d : ℤ) (hd : d = degree (p+1) m) :
    let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) base d
    K.homologyπ (p+1) ≫ (homologyResidueEquivAt (R := R) p m base d hd).toModuleIso.hom =
      K.iCycles (p+1) ≫ ModuleCat.ofHom (topResidueProjection (R := R) (p+1) m d hd) := by
  subst d
  exact homologyResidueEquiv_homologyπ p m base

/-- The induced map on genuine positive top homology is exactly the residue
transpose of polynomial multiplication by the given linear form. -/
theorem homology_linearFormMap_residue (p m : ℕ) (base : Fin (p+2)) (d : ℤ)
    (hsource : d = degree (p+1) (m+1)) (htarget : d+1 = degree (p+1) m)
    (L : Fin (p+2) → Γ(Spec (.of R),⊤)) :
    HomologicalComplex.homologyMap (linearFormMap base d L) (p+1) ≫
        (homologyResidueEquivAt (R := R) p m base (d+1) htarget).toModuleIso.hom =
      (homologyResidueEquivAt (R := R) p (m+1) base d hsource).toModuleIso.hom ≫
        ModuleCat.ofHom (multiplyResidueLinearForm m L) := by
  have hfg : (linearFormMap base d L).f (p+1) ≫
        ModuleCat.ofHom (topResidueProjection (R := R) (p+1) m (d+1) htarget) =
      ModuleCat.ofHom (topResidueProjection (R := R) (p+1) (m+1) d hsource) ≫
        ModuleCat.ofHom (multiplyResidueLinearForm m L) := by
    apply ModuleCat.hom_ext
    exact linearFormMap_topResidue (p+1) m base d hsource htarget L
  exact LaurentTopNaturality.homologyProjection_naturality (linearFormMap base d L) (p+1)
    _ _ _ _ (homologyResidueEquivAt_homologyπ p (m+1) base d hsource)
    (homologyResidueEquivAt_homologyπ p m base (d+1) htarget) _ hfg

end SteinerGeometry.LaurentResidueHomology
