module

public import SteinerGeometry.NativeCohomology
public import SteinerGeometry.CanonicalTraceComplex
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- The affine pullback descent argument works for any quasicoherent module
with a split unit, including the symmetric powers used in the paper. -/
theorem cohomology_zero_of_split_affine_pullback
    {X Y : Scheme.{0}} [X.IsSeparated]
    (f : Y ⟶ X) [IsAffineHom f] (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    [((Scheme.Modules.pullback f).obj M).IsQuasicoherent]
    (hs : IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M))
    (q : ℕ)
    (hz : IsZero (H (f ≫ p) ((Scheme.Modules.pullback f).obj M) q)) :
    IsZero (H p M q) := by
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) q
  let η : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  obtain ⟨⟨r, hr⟩⟩ := hs
  have hη : IsSplitMono (F.map η) := ⟨⟨F.map r,
    (F.map_comp η r).symm.trans ((congrArg F.map hr).trans (F.map_id M))⟩⟩
  let _ := hη
  have hz' : IsZero (F.obj ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj M))) :=
    hz.of_iso (Affine.PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso
      f p ((Scheme.Modules.pullback f).obj M) q).symm
  exact IsZero.of_mono (F.map η) hz'

/-- Vanishing after a finite-flat pullback of invertible degree descends to
any actual quasicoherent coefficient sheaf. -/
theorem cohomology_zero_of_finiteFlat_pullback
    {X Y : Scheme.{0}} [X.IsSeparated] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ}
    (hn : ∀ x, f.finrank x = n) (v : Γ(X, ⊤)ˣ) (hv : (v : Γ(X, ⊤)) = n)
    (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj M).IsQuasicoherent]
    (q : ℕ) (hz : IsZero (H (f ≫ p) ((Scheme.Modules.pullback f).obj M) q)) :
    IsZero (H p M q) :=
  cohomology_zero_of_split_affine_pullback f p M
    (CanonicalTrace.finiteFlat_pullbackUnit_splitMono f hn v hv M) q hz

/-- The same descent with a supplied normalized structure trace. -/
theorem cohomology_zero_of_structureTrace
    {X Y : Scheme.{0}} [X.IsSeparated]
    (f : Y ⟶ X) [IsAffineHom f] (p : X ⟶ Spec (.of ℂ))
    (M : X.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj M).IsQuasicoherent]
    (t : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶
      Line.Bundles.structureModule X)
    (ht : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ t = 𝟙 _)
    (q : ℕ) (hz : IsZero (H (f ≫ p) ((Scheme.Modules.pullback f).obj M) q)) :
    IsZero (H p M q) :=
  cohomology_zero_of_split_affine_pullback f p M
    (CanonicalTrace.pullbackUnit_splitMono_of_structureTrace f M t ht) q hz


/-- On a complex scheme the positive finite-flat degree is automatically invertible. -/
theorem cohomology_zero_of_finiteFlat_pullback_complex
    {X Y : Scheme.{0}} [X.IsSeparated] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ}
    (hn : ∀ x, f.finrank x = n) (p : X ⟶ Spec (.of ℂ)) (hnpos : 0 < n)
    (M : X.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj M).IsQuasicoherent]
    (q : ℕ) (hz : IsZero (H (f ≫ p) ((Scheme.Modules.pullback f).obj M) q)) :
    IsZero (H p M q) :=
  cohomology_zero_of_split_affine_pullback f p M
    (CanonicalTrace.finiteFlat_pullbackUnit_splitMono_complex f hn p hnpos M) q hz

end SteinerGeometry.EllipticCohomology
