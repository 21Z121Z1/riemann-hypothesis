import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SpehProductSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0734
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0741
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0742
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpecFac

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fock

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem pureTensorO_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (f + f') P =
      pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P := by
  have hA : ∀ k g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g) :=
    fun k g hg => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hg
  have hl : ∀ l : List (FVar D T.rank S.rank),
      l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) (f + f') =
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f +
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f' ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f) ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f') := by
    intro l
    induction l with
    | nil => exact ⟨rfl, hf, hf'⟩
    | cons i l ih =>
      simp only [List.foldr_cons]
      refine ⟨?_, hA i _ ih.2.1, hA i _ ih.2.2⟩
      rw [ih.1]
      exact GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ ih.2.1 ih.2.2
  have e : pureTensorO ψ θ S T sS sT BS BT (f + f') =
      pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT f' := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    simp only [pureTensorO, pureTensorL, LinearMap.add_apply, Module.Basis.constr_basis, opPow]
    exact (hl _).1
  rw [e, LinearMap.add_apply]

theorem theta_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a)) :
    IsThetaFunO ψ S T (∑ a ∈ s, c a • f a) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun a ha => GlobalTheory.OrientedHeis.theta_smul _ (hf a ha)

theorem pureTensorO_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a))
    (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (∑ a ∈ s, c a • f a) P = ∑ a ∈ s, c a • pureTensorO ψ θ S T sS sT BS BT (f a) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, IsThetaFunO ψ S T (f x) := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      pureTensorO_add hψ hθ sS BS sT BT (GlobalTheory.OrientedHeis.theta_smul _ (hf a (Finset.mem_insert_self a s)))
        (theta_sum s c f hs) P,
      GlobalTheory.FiniteFock.pureTensorO_smul, ih hs]

theorem series_sum {B : Base S T} (hB : B.Good) (ω : PairRep S T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO B.F.ψ S T (f a)) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    series B.F ω (∑ a ∈ s, c a • f a) h P g = ∑ a ∈ s, c a * series B.F ω (f a) h P g := by
  simp only [series_apply, Frame.fock]
  rw [pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ s c f hf P, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

end Fock

section Spec

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem coef_add (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a a' : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (a + a'))) : X.Ok i k) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) *
        ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a')) : X.Ok i k) := by
  rw [map_add, ofAdd_add, map_mul, Units.val_mul, map_mul]

open Classical in

theorem coef_prod (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) =
      ∏ PP, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP (a PP)))) : X.Ok i k) := by
  have e : a = ∑ PP, Pi.single PP (a PP) := (Finset.univ_sum_single a).symm
  conv_lhs => rw [e]
  rw [map_sum, ofAdd_sum, map_prod, Units.coe_prod, map_prod]

open Classical in

theorem locFn_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (fun PP y =>
          ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) := by
  funext y
  simp only [Base.locFn, specLoc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coef_prod ρ Y i b k Q M χ a, Finset.prod_mul_distrib]
  ring

open Classical in

theorem vecAt_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a := by
  rw [Base.vecAt, locFn_specLoc]
  change (ρ.B i j b).F.vecL (ρ.B i j b).G _ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  rfl

theorem coord_open (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (P : Pl D.host.E) :
    IsOpen ((coord Y i Q M P).ker : Set (G D.host.E N.Om)) := by
  unfold coord
  split_ifs
  · exact Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one])
      (Y.delU_open i Q M)
  · rw [MonoidHom.ker_one]
    exact isOpen_univ

theorem detChar_tw {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : GlobalTheory.UnivChar.IsUnivChar Y)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (hχ : TwOK i k Q (χ.comp (Y.delU i Q M)))
    (g : GA D (Wc D j)) :
    ((detChar (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi g : Circle) : ℂ) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Multiplicative.toAdd
        (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g)))) :
          X.Ok i k) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym (detRoot (Wc D j) g)
  have hker : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
    Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) (Y.delU_open i Q M)
  have hn : X.l i ^ M ≠ 0 := NeZero.ne _
  have hpow : (χ.comp (Y.delU i Q M)) σ ^ (X.l i ^ M) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow]
    have e : Y.delU i Q M σ ^ (X.l i ^ M) = 1 := by
      apply Multiplicative.toAdd.injective
      funext v
      rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
      rfl
    rw [e, map_one]
  have hd : Multiplicative.toAdd
      (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g) =
        fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
    funext PP
    change Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) (detRoot (Wc D j) g)) = _
    rw [ρ.rc.pull_eq (coord_open Y i _ M PP.1) hσ]
  change ((charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) (detRoot (Wc D j) g) : Circle) : ℂ) = _
  rw [charOf_eq ρ.rc (ρ.eOk i b k) hker hσ hn hpow, hd, MonoidHom.comp_apply,
    ← ofAdd_toAdd (Y.delU i Q M σ), delU_eq_spread hY (twSet_of_twOK hχ) (hρ.ch i) σ]

end Spec

theorem specXi_eq_specSer : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  intro D N X ρ hρ Y hY i j b k Q M χ hχ h P
  classical
  funext g
  have hB := hρ.base i j b
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h)
      (hχ.2.1.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have htheta : ∀ a ∈ (Finset.univ : Finset (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M))),
      IsThetaFunO (ρ.B i j b).F.ψ (Vc D j) (Wc D j) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))
        (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a) := fun a _ => by
    have := Base.isThetaFunO_fock_vecAt hB hadm (fun PP y =>
      ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) 1
    rwa [Frame.fock, GlobalTheory.FiniteFock.pureTensorO_one] at this
  unfold specSer
  rw [twistBy_apply, vecAt_specLoc, series_sum hB _ _ _ _ htheta, detChar_tw hρ hY i j b k Q M χ hχ g]
  unfold specXi
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Setup.xi, Base.xiCoef_apply]
  rw [← Equiv.sum_comp (Equiv.addRight (Multiplicative.toAdd (detChar (Wc D j)
    ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.coe_addRight, add_sub_cancel_right, coef_add]
  ring

end GlobalTheory.SpecFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.IndefiniteRowSideFullHecke.SpehProductSatake GlobalTheory.LFun
  GlobalTheory.PRep Formalism.UG

namespace GlobalTheory.BcSpehCompare

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Linear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}

omit [IsTotallyComplex E] in

theorem isCompact_KGL : IsCompact (KGL w a : Set (GL (Fin a) (w.adicCompletion E))) :=
  IntPtsUnitary.isCompact_GLint _
    (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w))

theorem injective_of_irred {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {τ : G → W → W} (h0 : ∀ g, τ g 0 = 0) {f : V →ₗ[ℂ] W} (hf0 : f ≠ 0)
    (hf : ∀ g v, f (σ g v) = τ g (f v)) : Function.Injective f := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ).2 (LinearMap.ker f) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf, hv, h0]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hf0

theorem hasSat_iff {P : CuspSub E a} {σ : LocIrr w a} (h : P.IsLocComp w σ) (B : Multiset ℂˣ) :
    (CG.mk P).HasSat w B ↔ HasSatGL w σ.ρ B := by
  rw [CG.hasSat_mk]
  obtain ⟨f, h0, hf⟩ := h
  have hi := injective_of_irred σ.irred (τ := fun g => P.locRep w g) (fun _ => map_zero _) h0 hf
  have hfix : ∀ v ∈ fixed σ.ρ (KGL w a), f v ∈ fixed (P.locRep w) (KGL w a) := fun v hv =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, GlobalTheory.LGrp.mem_fixed.1 hv k hk]
  have hne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v => (map_ne_zero_iff f hi).2
  constructor
  · intro hB
    refine ⟨?_, fun v hv hv0 => (hB.2 _ (hfix v hv) (hne v hv0)).of_map f hf hi⟩
    obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have h1 : LinearMap.range f ⊓ fixed (P.locRep w) (KGL w a) ≠ ⊥ := fun e =>
      h0 (LinearMap.range_eq_bot.1 (LocEx.eq_bot_of_fixed P w isCompact_KGL hφ0 hφ _
        (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hf g v⟩) e))
    obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hi (by
      rw [hf, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩
  · intro hB
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    refine ⟨(Submodule.ne_bot_iff _).2 ⟨f v, hfix v hv, hne v hv0⟩, fun x hx hx0 => ⟨hx0, hx, hB.card, fun ϖ hϖ j hj => ?_⟩⟩
    have htop : LocUniq.isoPart σ.ρ (P.locRep w) = ⊤ := by
      have hm := Submodule.map_injective_of_injective P.V.injective_subtype
      rcases P.irred ((LocUniq.isoPart σ.ρ (P.locRep w)).map P.V.subtype) (Submodule.map_subtype_le _ _) (by
        rintro o _ ⟨x, hx, rfl⟩
        exact ⟨_, LocUniq.isoPart_op P w σ.ρ o hx, rfl⟩) with h1 | h1
      · have h3 : f v ∈ LocUniq.isoPart σ.ρ (P.locRep w) :=
          Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (P.locRep w)) ⟨v, rfl⟩
        rw [hm (h1.trans (Submodule.map_bot _).symm)] at h3
        exact absurd h3 (hne v hv0)
      · exact hm (h1.trans (Submodule.map_subtype_top _).symm)
    have hc := Final.GLintComm E w a
    have hT := Tj_mem_hecke (n := a) hϖ j
    let e := LocGL.idem (P.isSmooth_locRep w) (isCompact_KGL (w := w) (a := a))
    have key : ∀ y ∈ LocUniq.isoPart σ.ρ (P.locRep w),
        heckeVec (P.locRep w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) (e y) = satEig (qV E w) a B j • e y := fun y hy => by
      refine Submodule.iSup_induction _ (motive := fun y =>
        heckeVec (P.locRep w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) (e y) = satEig (qV E w) a B j • e y) hy ?_ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        have h1 : e (g.toLinearMap u) = g.toLinearMap (LocGL.idem σ.smooth isCompact_KGL u) :=
          (LocGL.map_idem σ.smooth _ _ g u).symm
        rw [h1, ← map_heckeVec hc hT g.toLinearMap fun k y => LinearMap.congr_fun (g.isIntertwining' k) y, ← map_smul]
        congr 1
        by_cases hu : LocGL.idem σ.smooth (isCompact_KGL (w := w) (a := a)) u = 0
        · simp [hu, heckeVec]
        · exact (hB.2 _ (LocGL.idem_mem _ _ u) hu).2.2.2 ϖ hϖ j hj
      · simp [heckeVec]
      · intro y z hy hz
        rw [map_add, smul_add, ← hy, ← hz]
        refine Eq.trans (finsum_congr fun _ => ?_)
          (finsum_add_distrib (finite_heckeVec hc hT _ (e y)) (finite_heckeVec hc hT _ (e z)))
        simp only [map_add, smul_add]
    have h2 := key x (htop ▸ Submodule.mem_top)
    rwa [show e x = x from LocGL.idem_of_mem _ _ hx] at h2

end Linear

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c a : ℕ} {w : HeightOneSpectrum (𝓞 E)}

theorem not_isSplitAt {s : w.adicCompletion E →+* w.adicCompletion E}
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ¬ IsSplitAt w := by
  rintro ⟨u, hu, e⟩
  have hw : ∀ k : E, w.valuation E (IsCMField.complexConj E k) = w.valuation E k := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
        w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have := w.isPrime
  refine hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top
    (GlobalTheory.FixedPrime.le_of_under_le w.asIdeal (fun x hx => ?_) _ (congrArg HeightOneSpectrum.asIdeal e).le)))
  rw [← w.valuation_lt_one_iff_mem (K := E)] at hx ⊢
  exact (hw x).symm.trans_lt hx

theorem isUnramU_of_hasSatAt {π : Submodule ℂ (UA E n → ℂ)} {s : w.adicCompletion E →+* w.adicCompletion E}
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hval : ∀ x, Valued.v (s x) = Valued.v x)
    {ϖ : w.adicCompletion E} {q : ℕ} {α : Fin (n / 2) → ℂˣ} (h : HasSatAt π w s ϖ q α) : IsUnramU π w := by
  obtain ⟨b, hb, hJ, p, hp, σ, ⟨hσ, f, h0, h1, h2⟩, hS⟩ := h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨ι, -, hι, -⟩ := GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit E n w s hs hval (not_isSplitAt hs hval)
  have hsurj : Function.Surjective p := fun g => by
    have hg : cT s g.1.val * antiJ _ n * g.1.val = antiJ _ n := g.2
    have hm : b * g.1 * b⁻¹ ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      change cT s (b.val * g.1.val * (b⁻¹).val) * 1 * (b.val * g.1.val * (b⁻¹).val) = 1
      calc _ = cT s (b⁻¹).val * (cT s g.1.val * (cT s b.val * b.val) * g.1.val) * (b⁻¹).val := by
            simp only [cT_mul, Matrix.mul_assoc, Matrix.mul_one]
        _ = cT s (b.val * (b⁻¹).val) * (b.val * (b⁻¹).val) := by
            rw [hJ, hg, ← hJ]; simp only [cT_mul, Matrix.mul_assoc]
        _ = 1 := by rw [Units.mul_inv, cT_one, Matrix.mul_one]
    refine ⟨⟨_, (hι ⟨_, hm⟩).1⟩, Subtype.ext ?_⟩
    rw [hp, (hι _).2]
    group
  have hi : Function.Injective f := by
    choose t ht using hsurj
    exact injective_of_irred hσ (τ := fun g => RU E n (t g)) (fun _ => map_zero _) h0 fun g u => by
      rw [← h2, ht]
  refine ⟨f v, h1 v, (map_ne_zero_iff f hi).2 hv0, fun x hx hk => ?_⟩
  rw [← h2 ⟨x, hx⟩ v, GlobalTheory.LGrp.mem_fixed.1 hv _ ⟨(p _).2, ?_⟩]
  change (p ⟨x, hx⟩).val ∈ KGL w n
  rw [hp]
  exact mul_mem (mul_mem (inv_mem hb) hk) hb

theorem exists_hasSatAt
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) (hw : ¬ IsSplitAt w) (hu : IsUnramU π w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ) (α : Fin (n / 2) → ℂˣ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q ∧
        HasSatAt π w s ϖ q α := by
  obtain ⟨s, ϖ, q, h1, h2⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hE w) hw
  obtain ⟨α, h3⟩ := GlobalTheory.T.exists_satakeParameter_definiteUnitary_inertPlace E n w s ϖ q h1 h2 (GlobalTheory.T.finiteDimensional_definiteUnitary_levelForms E n (GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets E n))
    (GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit E n w s h1 h2.2.1 hw) π hπ hu
  exact ⟨s, ϖ, q, α, h1, h2, h3⟩

theorem isNormalised_of_isCsd {P : CuspSub E a} (h : P.IsCsd) : GlobalTheory.DiscSpec.IsNormalised P := by
  intro φ hφ t g
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a P
  have h1 := CsdUnitary.dchi_theta hω h fun _ => (t : ℂ)
  have h2 : dchi ω (fun _ => (t : ℂ)) = 0 := by
    rw [show star (fun _ => (t : ℂ) : Cinf E) = fun _ => (t : ℂ) from funext fun _ => Complex.conj_ofReal t,
      map_neg] at h1
    linear_combination -h1 / 2
  have h3 := chiInf_expU ω fun _ => (t : ℂ)
  rw [h2, Complex.exp_zero] at h3
  have h4 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
  rw [show ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 from h3, one_mul] at h4
  rw [← h4]
  exact congrArg (fun x => φ.1 (x * g)) (cornerGL_scalar (sInf E) _)

def HasUnitarySpeh (P : CG E a) (d : ℕ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), ∃ (ρ : LocIrr w a) (σ : LocIrr w (d * a)), P.IsLoc w (Quotient.mk _ ρ) ∧
    IsUnitarisable ρ.ρ ∧ IsUnitarisable σ.ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred) d σ.ρ

theorem transport {π : Submodule ℂ (UA E n → ℂ)} {N N' : Fin c → ℕ} (e : N = N') (h : ∑ i, N i = n) (h' : ∑ i, N' i = n)
    (Q : Fin c → ∀ b, LocIrr w b → Prop) (S : ∀ i, LocIrr w (N i)) (hQ : ∀ i, Q i _ (S i))
    (hS : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w S)) :
    ∃ S' : ∀ i, LocIrr w (N' i), (∀ i, Q i _ (S' i)) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h' w S') := by
  subst e
  exact ⟨S, hQ, hS⟩

def SpehShape (π : Submodule ℂ (UA E n → ℂ)) : Prop :=
  ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
    (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
    (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
    ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))

end CM

end GlobalTheory.BcSpehCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionHeisenbergIrreducibleOrthogonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_heisenberg_irreducible_orthogonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ w : WO S T, thetaIP μ 𝓕 h (heisO ψ S T w e) = 0) → h = 0 ∨ e = 0 := by
  first | exact @GlobalTheory.ThetaIrred.orth_heis_translates | exact GlobalTheory.ThetaIrred.orth_heis_translates | (intros; apply GlobalTheory.ThetaIrred.orth_heis_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestrictionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalChar_spread_commutes_with_restriction : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  first | exact @GlobalTheory.SpreadRestrict.spread_restrict | exact GlobalTheory.SpreadRestrict.spread_restrict | (intros; apply GlobalTheory.SpreadRestrict.spread_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtendingStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  first | exact @GlobalTheory.CompletionIsom.valued_v_map | exact GlobalTheory.CompletionIsom.valued_v_map | (intros; apply GlobalTheory.CompletionIsom.valued_v_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_laterClauses_hold : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantNormBound D HW F Cm := by
  first | exact @GlobalTheory.NL.wach_used_clauses | exact GlobalTheory.NL.wach_used_clauses | (intros; apply GlobalTheory.NL.wach_used_clauses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatibStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E), Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) → (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  first | exact @GlobalTheory.WeightParamTie.weightParam_of_levelTied | exact GlobalTheory.WeightParamTie.weightParam_of_levelTied | (intros; apply GlobalTheory.WeightParamTie.weightParam_of_levelTied <;> assumption)
end

