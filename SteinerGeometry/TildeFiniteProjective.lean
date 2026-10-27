import SteinerGeometry.KernelLocalFreeness
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Finite projective modules give locally free tilde sheaves
The affine base-change comparison uses the actual tilde adjunction.
Local bases are obtained by localizing a finite projective module and
spreading a stalk basis to a principal open.
-/

noncomputable section
namespace SteinerGeometry.TildeFiniteProjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module
universe u

private def sectionsFunctor (R : CommRingCat.{u}) :
    TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)

private def pushforwardSectionsIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars f.hom := by
  let e := pushforwardCompModulesSpecToSheafIso f
  let Γ := sectionsFunctor R
  refine NatIso.ofComponents (fun N => Γ.mapIso (e.app N)) ?_
  intro M N g
  exact congrArg (fun h => Γ.map h) (e.hom.naturality g)

/-- Actual affine base change for associated module sheaves. -/
def tildePullbackIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (pushforwardSectionsIso f).symm)

private theorem opensMap_final {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final := by
  let F := TopologicalSpace.Opens.map f.base
  have : PreservesLimit (Functor.empty.{0} Y.Opens) F :=
    preservesTerminal_of_iso F
      (F.mapIso (terminalIsTerminal.uniqueUpToIso isTerminalTop) ≪≫
        eqToIso (show F.obj (⊤ : Y.Opens) = (⊤ : X.Opens) from by ext; simp [F]) ≪≫
        isTerminalTop.uniqueUpToIso terminalIsTerminal)
  infer_instance

/-- Pullback of a genuine free module sheaf is free on the same index set. -/
def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (Q : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free Q) ≅ SheafOfModules.free Q := by
  have : (SheafOfModules.pushforward
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have := opensMap_final f
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom Q

/-- An affine localized basis gives a free frame on the actual principal open. -/
def basicOpenFreeTrivialization {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (r : R) (Q : Type u)
    (eLocal : LocalizedModule.Away r M ≃ₗ[Localization.Away r] (Q →₀ Localization.Away r)) :
    (Scheme.Modules.pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj
      (tilde M) ≅ SheafOfModules.free Q := by
  let A := CommRingCat.of (Localization.Away r)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let i := basicOpenIsoSpecAway r
  let eModule : (ModuleCat.extendScalars f.hom).obj M ≅ ModuleCat.of A (Q →₀ A) := by
    have halg : f.hom.toAlgebra = inferInstanceAs (Algebra R (Localization.Away r)) :=
      toAlgebra_algebraMap
    have hloc : letI := f.hom.toAlgebra
        IsLocalization (.powers r) (Localization.Away r) := by
      rw [halg]
      infer_instance
    have htower : @IsScalarTower R (Localization.Away r) (LocalizedModule.Away r M)
        f.hom.toAlgebra.toSMul inferInstance inferInstance := by
      rw [halg]
      infer_instance
    letI : Algebra R (Localization.Away r) := f.hom.toAlgebra
    haveI : IsLocalization (.powers r) (Localization.Away r) := hloc
    haveI := htower
    exact ((IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) M)).equiv ≪≫ₗ eLocal).toModuleIso
  exact (Scheme.Modules.pullbackCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app
      (tilde M) ≪≫
    ((Scheme.Modules.pullbackComp i.hom (Spec.map f)).app (tilde M)).symm ≪≫
    (Scheme.Modules.pullback i.hom).mapIso ((tildePullbackIso f).app M) ≪≫
    (Scheme.Modules.pullback i.hom).mapIso
      ((tilde.functor A).mapIso eModule ≪≫ tildeFinsupp Q) ≪≫
    pullbackFreeIso i.hom Q

/-- The equivalence between modules on an open and modules on its open
subscheme preserves the free module on an arbitrary index set. -/
def overEquivFreeIso {X : Scheme.{u}} (U : X.Opens) (Q : Type u) :
    (Scheme.Modules.overEquiv U).functor.obj
      (SheafOfModules.free (R := X.ringCatSheaf.over U) Q) ≅ SheafOfModules.free Q :=
  (asIso (sigmaComparison (Scheme.Modules.overEquiv U).functor
    (fun _ : Q => SheafOfModules.unit (X.ringCatSheaf.over U)))).symm ≪≫
    Sigma.mapIso (fun _ => Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf)

/-- Turn a free frame after geometric open pullback into the precise
`over`-frame required by Mathlib's locally-free definition. -/
def overFrameOfPullback {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (Q : Type u)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free Q) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) Q ≅ M.over U := by
  let eR : (Scheme.Modules.overEquiv U).functor.obj (M.over U) ≅
      (Scheme.Modules.pullback U.ι).obj M :=
    (Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  exact (Scheme.Modules.overEquiv U).functor.preimageIso
    (overEquivFreeIso U Q ≪≫ e.symm ≪≫ eR.symm)


/-- A basis of a finite projective module on one principal neighborhood of
an arbitrary point, with no assumed global freeness. -/
structure LocalBasisAt {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (p : PrimeSpectrum R) where
  Index : Type u
  finite : Finite Index
  scalar : R
  not_mem : scalar ∉ p.asIdeal
  basis : Basis Index (Localization.Away scalar) (LocalizedModule.Away scalar M)

/-- A stalk basis spreads to a principal neighborhood by finite presentation. -/
def chooseLocalBasis {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) : LocalBasisAt M p := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let S := p.asIdeal.primeCompl
  let f := LocalizedModule.mkLinearMap S M
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule S M
  letI : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule S (Rₚ := Rₚ) f
  letI : Module.Free Rₚ Mₚ := Module.free_of_flat_of_isLocalRing
  let I := Module.Free.ChooseBasisIndex Rₚ Mₚ
  let b : Basis I Rₚ Mₚ := Module.Free.chooseBasis Rₚ Mₚ
  letI : Finite I := Module.Finite.finite_basis b
  let h := Module.FinitePresentation.exists_basis_localizedModule_powers S f Rₚ b
  exact ⟨I, inferInstance, h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose⟩

/-- A finite projective module defines a locally free sheaf on its spectrum. -/
theorem tilde_locallyFree_of_finite_projective {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] : (tilde M).IsLocallyFree := by
  let D := chooseLocalBasis M
  let U : PrimeSpectrum R → (Spec R).Opens := fun p => PrimeSpectrum.basicOpen (D p).scalar
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro p _
    exact Opens.mem_iSup.mpr ⟨p, (D p).not_mem⟩
  apply KernelLocalFreeness.locallyFree_of_local_frames (tilde M) U hU (fun p => (D p).Index)
  intro p
  exact overFrameOfPullback (tilde M) (U p) (D p).Index
    (basicOpenFreeTrivialization M (D p).scalar (D p).Index (D p).basis.repr)

/-- The same finite local bases give finite type and quasicoherence. -/
theorem tilde_finiteType_of_finite_projective {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] :
    (tilde M).IsQuasicoherent ∧ (tilde M).IsFiniteType := by
  let D := chooseLocalBasis M
  let U : PrimeSpectrum R → (Spec R).Opens := fun p => PrimeSpectrum.basicOpen (D p).scalar
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro p _
    exact Opens.mem_iSup.mpr ⟨p, (D p).not_mem⟩
  let : ∀ p, Finite ((D p).Index) := fun p => (D p).finite
  apply KernelLocalFreeness.finiteType_of_local_frames (tilde M) U hU (fun p => (D p).Index)
  intro p
  exact overFrameOfPullback (tilde M) (U p) (D p).Index
    (basicOpenFreeTrivialization M (D p).scalar (D p).Index (D p).basis.repr)


end SteinerGeometry.TildeFiniteProjective
