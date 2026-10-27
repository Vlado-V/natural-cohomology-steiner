module

public import SteinerGeometry.SectionContractionCategory
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles
public import Mathlib.Data.Vector.Basic

set_option backward.privateInPublic true
@[expose] public section

/-! Genuine multilinear monomial morphisms from tensor products of line factors. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u
variable {X : Scheme.{u}}

local instance sectionTensorMonomialsBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- A fixed, ordered finite tensor product. It retains all actual sheaf factors. -/
def tensorFactors : (s : ℕ) → (Fin s → X.Modules) → X.Modules
  | 0, _ => Line.Bundles.structureModule X
  | s+1, G => Tensor.ProductSheaf.tensorModule (G 0)
      (tensorFactors s (fun j => G j.succ))

/-- Ordered tensor product of line bundles, retaining its actual line-bundle structure. -/
def tensorLineFactors : (s : ℕ) → (Fin s → Line.Bundles.LineBundle X) →
    Line.Bundles.LineBundle X
  | 0, _ => Line.Bundles.LineBundle.trivial X
  | s+1, L => (L 0).tensor (tensorLineFactors s (fun j => L j.succ))

@[simp] theorem tensorLineFactors_sheaf (s : ℕ) (L : Fin s → Line.Bundles.LineBundle X) :
    (tensorLineFactors s L).sheaf = tensorFactors s (fun j => (L j).sheaf) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change Tensor.ProductSheaf.tensorModule (L 0).sheaf
      (tensorLineFactors s (fun j => L j.succ)).sheaf = _
    rw [ih]
    rfl

/-- Multiplying a coefficient morphism from each tensor factor gives a morphism
from the tensor product into the actual structure sheaf. -/
def tensorCoefficient : (s : ℕ) → (G : Fin s → X.Modules) →
    (∀ j, G j ⟶ Line.Bundles.structureModule X) →
    (tensorFactors s G ⟶ Line.Bundles.structureModule X)
  | 0, _, _ => 𝟙 _
  | s+1, G, c => Tensor.Bifunctor.tensorModuleMap (c 0)
      (tensorCoefficient s (fun j => G j.succ) (fun j => c j.succ)) ≫
        (Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom

/-- The canonical decomposable section in an ordered tensor product. -/
def tensorGenerator : (s : ℕ) → (G : Fin s → X.Modules) → (U : X.Opens) →
    (∀ j, Γ(G j, U)) → Γ(tensorFactors s G, U)
  | 0, _, U, _ => (1 : Γ(X, U))
  | s+1, G, U, v => (Tensor.Bifunctor.tensorBilinear (G 0)
      (tensorFactors s (fun j => G j.succ))).app U (v 0)
        (tensorGenerator s (fun j => G j.succ) U (fun j => v j.succ))

/-- A structure-valued morphism evaluated as a regular function. -/
def structureMapValue {M : X.Modules} (f : M ⟶ Line.Bundles.structureModule X)
    (U : X.Opens) (x : Γ(M, U)) : Γ(X, U) := f.app U x

private theorem tensorCoefficient_pair {M N : X.Modules}
    (f : M ⟶ Line.Bundles.structureModule X)
    (g : N ⟶ Line.Bundles.structureModule X) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    structureMapValue (Tensor.Bifunctor.tensorModuleMap f g ≫
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom) U
        ((Tensor.Bifunctor.tensorBilinear M N).app U x y) =
          structureMapValue f U x * structureMapValue g U y := by
  have h := congrArg (fun β : Bilinear.Sheaves.SheafBilinearMap M N
      (Tensor.ProductSheaf.tensorModule (Line.Bundles.structureModule X)
        (Line.Bundles.structureModule X)) => β.app U x y)
    (Tensor.Bifunctor.tensorModuleMap_spec f g)
  change (Tensor.Bifunctor.tensorModuleMap f g).app U
      ((Tensor.Bifunctor.tensorBilinear M N).app U x y) =
    (Tensor.Bifunctor.tensorBilinear _ _).app U (f.app U x) (g.app U y) at h
  unfold structureMapValue
  rw [Scheme.Modules.Hom.comp_app]
  change (Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom.app U
    ((Tensor.Bifunctor.tensorModuleMap f g).app U
      ((Tensor.Bifunctor.tensorBilinear M N).app U x y)) = _
  rw [h]
  have hu := congrArg (fun β : Bilinear.Sheaves.SheafBilinearMap
      (Line.Bundles.structureModule X) (Line.Bundles.structureModule X)
      (Line.Bundles.structureModule X) => β.app U (f.app U x) (g.app U y))
    ((Tensor.Bifunctor.tensorBilinear_postcomp
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom).trans
        (Tensor.PullbackUnits.tensorModuleUnitLeftIso_formula _))
  exact hu

/-- The coefficient map has exactly the ordinary product formula on decomposable sections. -/
theorem tensorCoefficient_generator (s : ℕ) (G : Fin s → X.Modules)
    (c : ∀ j, G j ⟶ Line.Bundles.structureModule X) (U : X.Opens)
    (v : ∀ j, Γ(G j, U)) :
    structureMapValue (tensorCoefficient s G c) U (tensorGenerator s G U v) =
      ∏ j, structureMapValue (c j) U (v j) := by
  induction s with
  | zero =>
    change (1 : Γ(X, U)) = ∏ j : Fin 0, structureMapValue (c j) U (v j)
    simp
  | succ s ih =>
    rw [Fin.prod_univ_succ]
    change structureMapValue (Tensor.Bifunctor.tensorModuleMap (c 0)
      (tensorCoefficient s (fun j => G j.succ) (fun j => c j.succ)) ≫
        (Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom) U
      ((Tensor.Bifunctor.tensorBilinear (G 0) (tensorFactors s (fun j => G j.succ))).app U
        (v 0) (tensorGenerator s (fun j => G j.succ) U (fun j => v j.succ))) = _
    rw [tensorCoefficient_pair, ih]

/-- The homogeneous monomial obtained by forgetting the order in a word. -/
def wordMonomial {n s : ℕ} (w : Fin s → Fin (n+1)) : Sym (Fin (n+1)) s :=
  Sym.ofVector (List.Vector.ofFn w)

/-- A homogeneous free module sheaf with its literal monomial labels. -/
abbrev homogeneousFreeSheaf (n d : ℕ) : X.Modules :=
  ⨁ fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule X

/-- Expand the product of linear-form columns as an actual sheaf morphism.
The sum over words gives every term of the ordinary commutative polynomial
product, including all multiplicities when several words have the same monomial. -/
def tensorMonomialMap {n s : ℕ} (G : Fin s → X.Modules)
    (c : ∀ j, Fin (n+1) → (G j ⟶ Line.Bundles.structureModule X)) :
    tensorFactors s G ⟶ homogeneousFreeSheaf (X := X) n s := by
  classical
  exact biproduct.lift fun b =>
    ∑ w : Fin s → Fin (n+1), if wordMonomial w = b then
      tensorCoefficient s G (fun j => c j (w j)) else 0

@[simp] theorem tensorMonomialMap_component {n s : ℕ} (G : Fin s → X.Modules)
    (c : ∀ j, Fin (n+1) → (G j ⟶ Line.Bundles.structureModule X))
    (b : Sym (Fin (n+1)) s) :
    tensorMonomialMap G c ≫ biproduct.π _ b =
      ∑ w : Fin s → Fin (n+1), if wordMonomial w = b then
        tensorCoefficient s G (fun j => c j (w j)) else 0 := by
  classical
  exact biproduct.lift_π _ _

/-- Any given inclusion of a tensor factor in the free linear-form sheaf supplies
its coefficient morphisms by the actual biproduct projections. -/
def tensorMonomialMapOfColumns {n s : ℕ} (G : Fin s → X.Modules)
    (c : ∀ j, G j ⟶ homogeneousFreeSheaf (X := X) n 1) :
    tensorFactors s G ⟶ homogeneousFreeSheaf (X := X) n s :=
  tensorMonomialMap G (fun j i => c j ≫
    biproduct.π _ (wordMonomial (fun _ : Fin 1 => i)))

/-- Evaluation of structure-valued morphisms is additive in the morphism. -/
def structureValueHom (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (M ⟶ Line.Bundles.structureModule X) →+ Γ(X, U) where
  toFun f := structureMapValue f U x
  map_zero' := rfl
  map_add' _f _g := rfl

/-- On decomposable sections the monomial morphism is literally the expansion
of the product of its linear-form columns. -/
theorem tensorMonomialMap_generator {n s : ℕ} (G : Fin s → X.Modules)
    (c : ∀ j, Fin (n+1) → (G j ⟶ Line.Bundles.structureModule X))
    (U : X.Opens) (v : ∀ j, Γ(G j, U)) (b : Sym (Fin (n+1)) s) :
    structureMapValue (tensorMonomialMap G c ≫ biproduct.π _ b) U
      (tensorGenerator s G U v) =
      ∑ w : Fin s → Fin (n+1), if wordMonomial w = b then
        ∏ j, structureMapValue (c j (w j)) U (v j) else 0 := by
  classical
  rw [tensorMonomialMap_component]
  change structureValueHom _ U (tensorGenerator s G U v) (∑ w : Fin s → Fin (n+1),
    if wordMonomial w = b then tensorCoefficient s G (fun j => c j (w j)) else 0) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs with hw
  · exact tensorCoefficient_generator s G (fun j => c j (w j)) U v
  · exact (structureValueHom _ U _).map_zero

/-- A fixed ordering of the factors of a symmetric monomial. -/
def symmetricWord {ι : Type*} {s : ℕ} (a : Sym ι s) : Fin s → ι :=
  List.Vector.get (⟨a.val.toList, (Multiset.length_toList a.val).trans a.property⟩ : List.Vector ι s)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem wordMonomial_symmetricWord {n s : ℕ} (a : Sym (Fin (n+1)) s) :
    wordMonomial (symmetricWord a) = a := by
  apply Sym.ext
  change ((List.Vector.ofFn (List.Vector.get
    (⟨a.val.toList, (Multiset.length_toList a.val).trans a.property⟩ :
      List.Vector (Fin (n+1)) s))).val : Multiset (Fin (n+1))) = a.val
  rw [List.Vector.ofFn_get]
  exact Multiset.coe_toList _

/-- The line bundle corresponding to one multi-index of a split kernel. -/
def monomialLineBundle {m s : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (a : Sym (Fin m) s) : Line.Bundles.LineBundle X :=
  tensorLineFactors s (fun j => L (symmetricWord a j))

/-- The direct sum of the actual line tensor products indexed by symmetric monomials. -/
def splitMonomialSource {m : ℕ} (L : Fin m → Line.Bundles.LineBundle X) (s : ℕ) : X.Modules :=
  ⨁ fun a : Sym (Fin m) s => (monomialLineBundle L a).sheaf

/-- Multiplication of split-kernel columns gives a genuine global morphism from
all monomial line tensor products into the free symmetric-power sheaf. -/
def splitMonomialMap {m n : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1) (s : ℕ) :
    splitMonomialSource L s ⟶ homogeneousFreeSheaf (X := X) n s := by
  classical
  exact biproduct.desc fun a =>
    eqToHom (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j))) ≫
      tensorMonomialMapOfColumns (fun j => (L (symmetricWord a j)).sheaf)
        (fun j => c (symmetricWord a j))

@[simp] theorem splitMonomialMap_component {m n s : ℕ}
    (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (a : Sym (Fin m) s) :
    biproduct.ι _ a ≫ splitMonomialMap L c s =
      eqToHom (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j))) ≫
        tensorMonomialMapOfColumns (fun j => (L (symmetricWord a j)).sheaf)
          (fun j => c (symmetricWord a j)) := by
  classical
  exact biproduct.ι_desc _ _

end SteinerGeometry
