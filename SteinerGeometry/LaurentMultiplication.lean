module

public import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech
public import Mathlib.Order.Preorder.Finite

set_option backward.privateInPublic true
@[expose] public section

/-! Multiplication by a coordinate on the actual homogeneous Laurent coefficient modules. -/
noncomputable section
namespace SteinerGeometry.LaurentMultiplication
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective

universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

abbrev Weight (d : ℤ) := LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d
abbrev Allowed {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) :=
  {e : Weight (σ := σ) d // e.IsAllowedOn a}

/-- The exponent change caused by multiplication by a homogeneous coordinate. -/
def shiftWeight (d : ℤ) (j : σ) (e : Weight (σ := σ) d) : Weight (σ := σ) (d+1) :=
  ⟨e.val + Finsupp.single j 1, by simp [e.property]⟩

omit [LinearOrder σ] in
@[simp] theorem shiftWeight_val (d : ℤ) (j : σ) (e : Weight (σ := σ) d) :
    (shiftWeight d j e).val = e.val + Finsupp.single j 1 := rfl

omit [LinearOrder σ] in
theorem shiftWeight_injective (d : ℤ) (j : σ) : Function.Injective (shiftWeight (σ := σ) d j) := by
  intro e f h
  exact Subtype.ext (add_right_cancel (congrArg Subtype.val h))

/-- Multiplication by a coordinate does not introduce a new negative exponent. -/
theorem shiftWeight_allowed {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ)
    (e : Allowed a d) : (shiftWeight d j e.val).IsAllowedOn a := by
  intro i hi
  apply e.property
  change e.val.val i < 0
  change e.val.val i + (Finsupp.single j (1 : ℤ)) i < 0 at hi
  by_cases hj : j = i
  · subst i
    simp only [Finsupp.single_eq_same] at hi
    omega
  · simpa [Finsupp.single_apply, hj] using hi

def shiftAllowed {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ) : Allowed a d → Allowed a (d+1) :=
  fun e => ⟨shiftWeight d j e.val, shiftWeight_allowed a d j e⟩

theorem shiftAllowed_injective {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ) :
    Function.Injective (shiftAllowed a d j) := by
  intro e f h
  apply Subtype.ext
  exact shiftWeight_injective d j (congrArg Subtype.val h)

/-- On each genuine Laurent Čech factor, coordinate multiplication translates exponents. -/
def shiftFactor {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ) :
    AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (Allowed a d) →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (Allowed a (d+1)) :=
  AddMonoidAlgebra.mapDomainLinearMap Γ(Spec (CommRingCat.of R), ⊤)
    Γ(Spec (CommRingCat.of R), ⊤) (shiftAllowed a d j)

@[simp] theorem shiftFactor_single {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ)
    (e : Allowed a d) (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    shiftFactor (R := R) a d j (AddMonoidAlgebra.single e r) =
      AddMonoidAlgebra.single (shiftAllowed a d j e) r :=
  AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

/-- Every translated coefficient is the original coefficient, not only the
same dimension or rank. This is the local input for the residue pairing. -/
theorem shiftFactor_coeff_shifted {q : ℕ} (a : Fin (q+1) → σ) (d : ℤ) (j : σ)
    (x : AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (Allowed a d))
    (e : Allowed a d) :
    (shiftFactor (R := R) a d j x).coeff (shiftAllowed a d j e) = x.coeff e := by
  exact Finsupp.mapDomain_apply_of_injective (shiftAllowed_injective a d j) x.coeff e

/-- Coordinate multiplication commutes with extension from a smaller coordinate intersection. -/
theorem shiftFactor_delete {q : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (q+1))
    (k : Fin (q+2)) (d : ℤ) (j : σ) :
    (shiftFactor (R := R) (fun l => (a.val l).down) d j).comp
        (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d) =
      (StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k (d+1)).comp
        (shiftFactor (R := R) (fun l => ((a.delete k).val l).down) d j) := by
  apply AddMonoidAlgebra.lhom_ext'
  intro e
  apply LinearMap.ext
  intro r
  simp only [AddMonoidAlgebra.lsingle_apply, LinearMap.comp_apply, shiftFactor_single,
    StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap_single]
  congr 1


/-- There is a single standard intersection in the top Čech degree. -/
def fullIndex (n : ℕ) :
    OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin (n+1))) n :=
  ⟨fun i => ULift.up i, fun _ _ h => h⟩

theorem topIndex_apply (n : ℕ)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin (n+1))) n)
    (i : Fin (n+1)) : (a.val i).down = i := by
  have h : StrictMono (fun i => (a.val i).down) := a.property
  exact congrFun h.eq_id i

instance topIndexUnique (n : ℕ) :
    Unique (OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin (n+1))) n) where
  default := fullIndex n
  uniq a := by
    apply Subtype.ext
    funext i
    apply ULift.ext
    exact topIndex_apply n a i

/-- The ordered cover has no cochains above projective dimension. -/
theorem noIndexAboveTop (n q : ℕ) (h : n < q) :
    IsEmpty (OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin (n+1))) q) := by
  constructor
  intro a
  have hinj : Function.Injective (fun i => (a.val i).down) := by
    intro i j hij
    apply a.property.injective
    exact ULift.ext hij
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

end SteinerGeometry.LaurentMultiplication
