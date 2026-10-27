import SteinerGeometry.SheafDual
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! The actual sheaf dual takes cokernels to kernels. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.SheafDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}

private def pairingFlip {M N P : X.Modules}
    (b : Bilinear.Sheaves.SheafBilinearMap M N P) :
    Bilinear.Sheaves.SheafBilinearMap N M P where
  app U := (b.app U).flip
  naturality h n m := b.naturality h m n

private theorem pairingFlip_flip {M N P : X.Modules}
    (b : Bilinear.Sheaves.SheafBilinearMap M N P) :
    pairingFlip (pairingFlip b) = b := by
  ext U m n
  rfl

/-- The symmetry of the bilinear pairing exchanges its two arguments. -/
def pairingTranspose {M N : X.Modules} (f : M ⟶ dual N) : N ⟶ dual M :=
  TensorHom.Construction.sheafBilinearCurry
    (pairingFlip (TensorHom.Construction.sheafBilinearUncurry f))

@[simp] theorem pairingTranspose_pairingTranspose {M N : X.Modules} (f : M ⟶ dual N) :
    pairingTranspose (pairingTranspose f) = f := by
  simp only [pairingTranspose, TensorHom.Construction.sheafBilinearUncurry_curry,
    pairingFlip_flip, TensorHom.Construction.sheafBilinearCurry_uncurry]

/-- Transposition is natural under precomposition. -/
theorem pairingTranspose_comp {M M' N : X.Modules} (f : M ⟶ dual N) (a : M' ⟶ M) :
    pairingTranspose (a ≫ f) = pairingTranspose f ≫ dualMap a := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro t
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

/-- The ordinary contravariant internal-Hom dual. -/
def dualFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.Modules where
  obj M := dual M.unop
  map f := dualMap f.unop
  map_id M := dualMap_id M.unop
  map_comp f g := dualMap_comp g.unop f.unop

instance (X : Scheme.{u}) : (dualFunctor X).PreservesZeroMorphisms where
  map_zero M N := dualMap_zero N.unop M.unop

/-- Sheaf duality is a contravariant self-adjunction, by symmetry of bilinear maps. -/
def dualAdjunction (X : Scheme.{u}) : (dualFunctor X).rightOp ⊣ dualFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun f => pairingTranspose f.unop
          invFun := fun g => (pairingTranspose g).op
          left_inv := fun f => by
            change (pairingTranspose (pairingTranspose f.unop)).op = f
            exact (congrArg (fun z : N.unop ⟶ dual M => z.op)
              (pairingTranspose_pairingTranspose f.unop)).trans (Quiver.Hom.op_unop f)
          right_inv := fun g => by
            change pairingTranspose (pairingTranspose g) = g
            exact pairingTranspose_pairingTranspose g }
      homEquiv_naturality_left_symm := by
        intro M' M N f g
        apply Quiver.Hom.unop_inj
        exact pairingTranspose_comp g f
      homEquiv_naturality_right := by
        intro M N N' f g
        exact pairingTranspose_comp f.unop g.unop }

instance (X : Scheme.{u}) : PreservesLimits (dualFunctor X) :=
  (dualAdjunction X).rightAdjoint_preservesLimits

/-- An actual cokernel diagram becomes a kernel diagram under sheaf duality. -/
def dualKernelOfCokernel {R F Q : X.Modules} (i : R ⟶ F) (p : F ⟶ Q)
    (w : i ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι (dualMap p)
      (show dualMap p ≫ dualMap i = 0 by rw [← dualMap_comp, w, dualMap_zero])) := by
  let ho := CokernelCofork.IsColimit.ofπOp p w h
  exact KernelFork.mapIsLimit _ ho (dualFunctor X)

/-- The kernel of the dual inclusion is the dual of its actual cokernel. -/
def dualCokernelIso {R F Q : X.Modules} (i : R ⟶ F) (p : F ⟶ Q)
    (w : i ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    dual Q ≅ kernel (dualMap i) :=
  IsLimit.conePointUniqueUpToIso (dualKernelOfCokernel i p w h) (limit.isLimit _)

end SteinerGeometry.SheafDual
