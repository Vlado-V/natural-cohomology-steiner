module

public import SteinerGeometry.TensorFactorFrames
public import SteinerGeometry.PolynomialWordExpansion

set_option backward.privateInPublic true
@[expose] public section

/-! Literal matrix entries of the monomial sheaf map in line-bundle frames. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance splitMonomialFramesBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The ordered tensor frame induced by actual factor frames. -/
def tensorFactorFrameIso (s : ℕ) (G : Fin s → X.Modules)
    (c : ∀ j, G j ≅ Line.Bundles.structureModule X) :
    tensorFactors s G ≅ Line.Bundles.structureModule X :=
  @asIso _ _ _ _ (tensorCoefficient s G (fun j => (c j).hom))
    (tensorCoefficient_isIso s G _ (fun _j => inferInstance))

/-- The inverse tensor frame at one is exactly the tensor of inverse factor frames at one. -/
theorem tensorFactorFrameIso_inv_one (s : ℕ) (G : Fin s → X.Modules)
    (c : ∀ j, G j ≅ Line.Bundles.structureModule X) (U : X.Opens) :
    (tensorFactorFrameIso s G c).inv.app U (1 : Γ(X, U)) =
      tensorGenerator s G U (fun j => (c j).inv.app U (1 : Γ(X, U))) := by
  apply (AddCommGrpCat.mono_iff_injective ((tensorFactorFrameIso s G c).hom.app U)).mp inferInstance
  have h : (tensorFactorFrameIso s G c).hom.app U
      ((tensorFactorFrameIso s G c).inv.app U (1 : Γ(X, U))) = (1 : Γ(X, U)) := by
    exact congrArg (fun f : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X =>
      f.app U (1 : Γ(X, U))) (tensorFactorFrameIso s G c).inv_hom_id
  rw [h]
  change (1 : Γ(X, U)) = structureMapValue (tensorCoefficient s G (fun j => (c j).hom)) U _
  rw [tensorCoefficient_generator]
  have hi (j : Fin s) : structureMapValue (c j).hom U
      ((c j).inv.app U (1 : Γ(X, U))) = 1 :=
    congrArg (fun f : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X =>
      f.app U (1 : Γ(X, U))) (c j).inv_hom_id
  simp only [hi, Finset.prod_const_one]

/-- The chosen frame on each actual monomial line bundle. -/
def monomialFrameIso {m s : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X) (a : Sym (Fin m) s) :
    (monomialLineBundle L a).sheaf ≅ Line.Bundles.structureModule X :=
  eqToIso (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j))) ≪≫
    tensorFactorFrameIso s (fun j => (L (symmetricWord a j)).sheaf)
      (fun j => c (symmetricWord a j))

/-- Frames on the summands give a frame on their actual finite direct sum. -/
def splitMonomialFrameIso {m : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X) (s : ℕ) :
    splitMonomialSource L s ≅ ⨁ fun _ : Sym (Fin m) s => Line.Bundles.structureModule X :=
  biproduct.mapIso (monomialFrameIso L c)

set_option backward.isDefEq.respectTransparency false in
/-- The matrix entry in monomial frames is exactly a coefficient of a product
of the framed kernel columns. -/
theorem splitMonomialMap_frame_entry {m n s : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (a : Sym (Fin m) s) (b : Sym (Fin (n+1)) s) (U : X.Opens) :
    structureMapValue ((monomialFrameIso L frames a).inv ≫
      biproduct.ι (fun a : Sym (Fin m) s => (monomialLineBundle L a).sheaf) a ≫ splitMonomialMap L c s ≫ biproduct.π _ b) U (1 : Γ(X, U)) =
      (∏ j, Steiner.SymmetricContraction.linearForm (fun i =>
        structureMapValue (c (symmetricWord a j) ≫
          biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) U
            ((frames (symmetricWord a j)).inv.app U (1 : Γ(X, U))))).coeff
        (Steiner.operatorExponent s b) := by
  classical
  rw [← Category.assoc (biproduct.ι (fun a : Sym (Fin m) s => (monomialLineBundle L a).sheaf) a), splitMonomialMap_component]
  change structureMapValue ((monomialFrameIso L frames a).inv ≫
    eqToHom (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j))) ≫
      tensorMonomialMapOfColumns (fun j => (L (symmetricWord a j)).sheaf)
        (fun j => c (symmetricWord a j)) ≫ biproduct.π _ b) U _ = _
  have he : (monomialFrameIso L frames a).inv ≫
      eqToHom (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j))) =
      (tensorFactorFrameIso s (fun j => (L (symmetricWord a j)).sheaf)
        (fun j => frames (symmetricWord a j))).inv := by
    simp [monomialFrameIso]
  rw [← Category.assoc, ← Category.assoc, he]
  change structureMapValue (tensorMonomialMapOfColumns
    (fun j => (L (symmetricWord a j)).sheaf) (fun j => c (symmetricWord a j)) ≫
      biproduct.π _ b) U
    ((tensorFactorFrameIso s (fun j => (L (symmetricWord a j)).sheaf)
      (fun j => frames (symmetricWord a j))).inv.app U (1 : Γ(X, U))) = _
  rw [tensorFactorFrameIso_inv_one]
  unfold tensorMonomialMapOfColumns
  rw [tensorMonomialMap_generator]
  exact (product_linearForms_coeff (R := Γ(X, U)) (fun j i =>
    structureMapValue (c (symmetricWord a j) ≫
      biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) U
        ((frames (symmetricWord a j)).inv.app U (1 : Γ(X, U)))) b).symm

end SteinerGeometry
