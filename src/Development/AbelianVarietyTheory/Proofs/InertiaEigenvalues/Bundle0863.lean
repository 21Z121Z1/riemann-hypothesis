import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0859
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0860
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.LatHalf

open GlobalTheory.ExportSeries
open Formalism.L2.DIV (Pl)

variable {D : D7}

theorem levConj_conjPl (P : Formalism.L2.DIV.Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl P (Formalism.L2.DIV.conjPl P) := by
  intro c hc
  refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ P.asIdeal
  rw [Formalism.L2.DIV.starO_starO]
  exact hc

theorem eq_conjPl_of_levConj {A B : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl A B) :
    B = Formalism.L2.DIV.conjPl A := by
  refine (HeightOneSpectrum.ext ?_).symm
  refine Ideal.IsMaximal.eq_of_le (Formalism.L2.DIV.conjPl A).isMaximal B.isPrime.ne_top fun b hb => ?_
  obtain ⟨c', hc', e⟩ := h (Formalism.L2.DIV.starO b) hb
  have : c' = b := RingOfIntegers.ext (by rw [e, Formalism.L2.DIV.starO_coe, star_star])
  exact this ▸ hc'

theorem isIdemAt_conjPl {e : AE D} {P : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.L2.DIV.conjPl P) :=
  GlobalTheory.MovedIdem.isIdemAt_conj h fun x => by
    rw [show Formalism.L2.Col.cO D.host.E x = Formalism.L2.DIV.starO x from RingOfIntegers.ext (by rw [Formalism.L2.DIV.starO_coe]; rfl)]
    rfl

theorem conj_placesOK {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) ∧ PlacesOK ∅ (Pg.image Formalism.L2.DIV.conjPl) := by
  obtain ⟨P, h1, -, hP⟩ := h.split
  have hS := hP.mono h1
  have hinj : Set.InjOn Formalism.L2.DIV.conjPl (Pg : Set (Pl D.host.E)) := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl]
  have hc : ∀ PP ∈ Pg, idemAt (Formalism.L2.DIV.conjPl PP) = cA D (idemAt PP) := fun PP hPP =>
    idemAt_eq (isIdemAt_conjPl (hS.isIdemAt hPP))
  have he : idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) := by
    rw [idem, Finset.sum_image hinj, idem, map_sum]
    exact Finset.sum_congr rfl hc
  refine ⟨he, ⟨⟨Pg.image Formalism.L2.DIV.conjPl, Finset.empty_subset _, le_rfl,
    ⟨idem (Pg.image Formalism.L2.DIV.conjPl), ⟨idemAt, ?_, rfl⟩, ?_⟩⟩, Finset.disjoint_empty_left _, ?_⟩⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    rw [hc P0 hP0]
    exact isIdemAt_conjPl (hS.isIdemAt hP0)
  · rw [he, GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hS.isIdemSum.2
  · intro PP hPP PP' hPP'
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 (hPP.resolve_left (Finset.notMem_empty PP))
    rcases hPP' with rfl | hc'
    · exact h.prime P0 (Or.inl hP0) _ (Or.inr (levConj_conjPl P0))
    · rw [eq_conjPl_of_levConj hc', Formalism.L2.DIV.conjPl_conjPl]
      exact h.prime P0 (Or.inl hP0) P0 (Or.inl rfl)

theorem goodPosition_auxiliaryPlaces_alone {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) : PlacesOK ∅ Q :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (hPP.resolve_left (Finset.notMem_empty PP)))⟩

theorem idem_sq {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem toEAf_idem_int {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) :
    toEAf D (idem R) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, -, h2, hP⟩ := h.split
  have := GlobalTheory.DatumFourier.idem_div_int (hP.mono h2).isIdemSum one_ne_zero fun PP _ hPP =>
    PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hPP))
  simpa using this

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem mem_lat_piece {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    (x : WO S T) (hi : IsIntM (frMapO S T F.βS F.βT x)) : idem R • x ∈ F.lat := by
  refine GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR (isHalf_smul (idem_sq hR) x) ?_
  rw [frMapO_smul]
  exact fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (toEAf_idem_int hR) (hi i j)

theorem mem_lat_iff_isIntM_halfIdem : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good →
    ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}, GlobalTheory.ExportSeries.PlacesOK Pg Q →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
    ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  intro D S T F hF Pg Q h _ x hx
  obtain ⟨hR1, hR⟩ := conj_placesOK h
  have hQ := goodPosition_auxiliaryPlaces_alone h
  have hxe : x = idem (Pg.image Formalism.L2.DIV.conjPl) • x + idem Q • x := by
    rw [← add_smul, hR1]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · intro hl
    obtain ⟨o1, a1⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR (isHalf_smul (idem_sq hR) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hR) hl)
    obtain ⟨o2, a2⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hQ (isHalf_smul (idem_sq hQ) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hQ) hl)
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add]
    exact ⟨fun i j => add_mem (a1 i j) (a2 i j), fun i j => add_mem (o1 i j) (o2 i j)⟩
  · rintro ⟨-, hi⟩
    rw [hxe]
    exact add_mem (mem_lat_piece hF hR x hi) (mem_lat_piece hF hQ x hi)

end GlobalTheory.ExportSeries.LatHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

theorem GlobalTheory.RawLift.vacFin_off : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → GlobalTheory.FinZeta.VacFin R.ψ (Vc D i) (Wc D i) v (R.vP i t) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hoffP
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hth, ?_⟩
  obtain ⟨hf₀, e, he, hthA⟩ := hL.thP.vP i t
  obtain ⟨ε, hε, rfl⟩ := hf
  have hoff : ∀ PP ∈ R.Pg ∪ R.Q t, PP.under (𝓞 D.host.F) ≠ v := by
    intro PP hPP h0
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    obtain ⟨e', f', hp⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ PP
    obtain ⟨w, ε', hε', hf', hw⟩ := GlobalTheory.VacLat.place_of_primeIdem hp
    refine hoffP PP (Finset.mem_union.1 hPP) e' f' hp ?_
    rw [h0] at hw
    subst hw
    rw [hf', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hL.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hL.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hthA (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hthA u (hz u hu) (hlat.2 e' he' u (hle hu) hh)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

theorem isResAt_one_of_unram : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  intro D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := hP.isIdemAt hPP
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hei, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  have hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D) := by
    linear_combination hoff
  have hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩ := by
    apply Subtype.ext
    have := congrArg (toEAf D) hx
    simp only [map_add, map_sub, map_mul, map_one] at this
    exact this.trans rfl

  have hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0 := by
    intro PP'
    by_cases hq : PP' = PP
    · subst hq
      rw [hu]
      exact u.ne_zero
    · have := PP'.isPrime
      have hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0 := by
        have hnle : ¬ PP'.asIdeal ≤ PP.asIdeal := fun hle =>
          hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))
        obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
        have ha0' : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
        have hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
          by_contra k
          exact ha ((he.2 a ha0).2 k)
        have hint' := GlobalTheory.IdemRes.toEAf_mem_of_finPart hint
        have hb : toEAf D (incA D (a : D.host.E)) =
            ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
        have hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a := by
          apply Subtype.ext
          change toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _
          rw [← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]
        rw [hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]
      rw [hxI, map_add, map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]
      exact one_ne_zero
  obtain ⟨w, hw⟩ := Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres
  have hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    have h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.inv_mul, RingHom.map_one]
    have h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv w)
      rw [hw] at this
      exact this
    calc _ = toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * (toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hl : IsLocUnit PP u x := by
    refine ⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩
    · have := congrArg (infPart D) hx
      rw [map_add, map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero] at this
      exact this
    · rw [hinv]
      exact Subtype.property _
  rw [hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]

end GlobalTheory.ConjTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelTranslateSumEqClassicalShortSeriesStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_translateSum_eq_classicalShortSeries : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r g q0 : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (hq : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x₀ : Frame X.Ψ r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsMod W hr X → IsSympl X bas → IsONFr X x₀ → IsInvOf W hr X x₀ s → IsBasOf W hr X hq x₀ BW → IsVarOf V W X q0 vr → ∀ (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), l₂.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E, IsRoots l₂ (latR hr (latG W k)) mk N Y → ∀ (v : TF V.rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (latR hr (latG W k))) v → Reads θ V W hr X bas idx (om (1, k) f₀) (a • v) (frMove θ W hr X k x₀) → ∀ (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW (transSum ψ V W l₂ ι e f₀ w) (MvPolynomial.rename vr P)) = (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * (((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℂ)) * ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR hr (latG W k)) v w Y) P (frMove θ W hr X k x₀) := by
  first | exact @GlobalTheory.SingleDatum.ShortSum.thetaKO_transSum_eq_short_series | exact GlobalTheory.SingleDatum.ShortSum.thetaKO_transSum_eq_short_series | (intros; apply GlobalTheory.SingleDatum.ShortSum.thetaKO_transSum_eq_short_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralSourceTranslationRightMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integralSourceTranslation_right_mul : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1), ∃ hQ, SuppAt (idem Q) S hQ ∧ ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank), series B.F ω (B.vecAt Q fun PP y => φ PP (y * (hb PP).val)) h P = series B.F ω (B.vecAt Q φ) (h * hQ) P := by
  first | exact @GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul | exact GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul | (intros; apply GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeSupportLift

variable {D : D7}

theorem exists_isBaseFrame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsFrame β Λ) (h : IsSelfDualC V Λ) :
    ∃ N, Lev.IsBaseFrame V β Λ N := by
  obtain ⟨_, N, hB⟩ := GlobalTheory.FinAdIdent.exists_baseFrame V Λ h
  exact ⟨N, hβ, hB.2⟩

theorem idem_add_conj_mul {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    (idem P + cA D (idem P)) * (idemAt PP + cA D (idemAt PP)) = idemAt PP + cA D (idemAt PP) := by
  have e1 : idem P * idemAt PP = idemAt PP := by
    rw [idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hP.mul_eq_zero hq hPP fun e => hne e.symm)
      (fun h => absurd hPP h)]
    exact (hP.isIdemAt hPP).1.1
  have e2 : idem P * cA D (idemAt PP) = 0 := by
    rw [idem, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => hP.mul_conj hq hPP
  have e3 : cA D (idem P) * idemAt PP = 0 := by
    rw [idem, map_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hP.mul_conj hPP hq
  have e4 : cA D (idem P) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, e1]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, e4, add_zero, zero_add]

theorem suppAt_idem_of_mem {V : HSp D} {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    {g : GA D V} (hg : SuppAt (idemAt PP) V g) : SuppAt (idem P) V g := fun i j => by
  rw [← hg i j, ← mul_assoc, idem_add_conj_mul hP hPP]

theorem exists_lift_supp {S T : HSp D} (B : Base S T) (hB : B.Good) (u : G0 B.G.Pg T.rank) :
    ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ := by
  obtain ⟨N, hN⟩ := exists_isBaseFrame hB.frame.frT hB.frame.sdT
  obtain ⟨R, h1, -, hR⟩ := hB.places.split
  have hPg : SplitSet B.G.Pg := hR.mono h1
  obtain ⟨e, κ, hl, hall⟩ := GlobalTheory.ParahoricLift.exists_lift_prod T B.F.βT B.G.levT B.F.ΛT N hN
    (fun PP hP PP' hP' => by
      rcases hP' with hP' | hP'
      · exact GlobalTheory.ExportType.not_isConjPl_of_splitSet hR (h1 hP) (h1 hP')
      · exact absurd hP' (Finset.notMem_empty _))
    (Finset.disjoint_empty_right _) u
  refine ⟨_, (hall Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)).1, ?_⟩
  refine List.prod_induction _ (fun a b ha hb => GlobalTheory.SplitLinear.suppAt_mul ha hb) (GlobalTheory.SplitLinear.suppAt_one _ _) ?_
  intro x hx
  obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hx
  have hs := (hl PP).2.1
  rw [← idemAt_eq (hl PP).1] at hs
  exact suppAt_idem_of_mem hPg PP.2 hs

open Classical in

theorem series_type_supp : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω →
    ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧
      SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q →
        ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T),
          series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  intro D S T B hB hS ω hω u hu
  obtain ⟨κ, hκ, hs⟩ := exists_lift_supp B hB u
  refine ⟨κ, hκ, hs, fun Q hQ φ h P g => ?_⟩
  have hred : ∀ PP : ↥Q, redFn B.F.βT PP.1 (Lev.finE T κ) = 1 := fun PP =>
    GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT (GlobalTheory.ExportSeries.DualType.dualTypePlaces_isSplitNonconjugate_of_admissible hQ) Finset.subset_union_left
      (Finset.mem_union_right _ (Finset.mem_union_right _ PP.2))
      (fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ PP.2)) (parLev_St hκ.2.1) hs
  have := GlobalTheory.ExportType.series_type hB hS hQ hω hu (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ) (φ := φ) (φ' := φ) (fun _ => 1)
    (fun PP y => by rw [hred PP, Units.val_one, Matrix.one_mul, Units.val_one, one_mul]) h P g
  rw [this, Finset.prod_const_one, inv_one, mul_one]

end GlobalTheory.TypeSupportLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaGenerator_eq_classSum_integralForm : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k Q ψ, TwOK i k Q ψ → (∀ x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ), (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range) → ∀ s h P, ρ.IsDatum i j b s h P → ∀ f ∈ ρ.gens i j b k Q ψ h P, ∃ F ∈ ρ.mt i j b k Q ψ, f = ρ.sum i j b k Q ψ F := by
  first | exact @GlobalTheory.TwTraceCx.trace_cx | exact GlobalTheory.TwTraceCx.trace_cx | (intros; apply GlobalTheory.TwTraceCx.trace_cx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.GoodModUnr

open GlobalTheory.IdemSupport

variable {D : D7}

theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} {χ : (AE D)ˣ →* Circle} (h : GlobalTheory.Hk3.UnrPl w χ) :
    GlobalTheory.LFun.UnrAt χ w := by
  intro u hu
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  have hd := (of_isPrimeIdem hΦ hp).1
  have hee : e * e = e := delta_idem hΦ hd
  have hfe : f * e = e := by
    rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
    · have ho : e * cA D e = 0 := hi.1.2.1
      linear_combination hee + ho
    · exact hee
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w u).1 hu
  have hg : e * ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) + (1 - e) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) :=
    GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd (GlobalTheory.LFun.EulerTie.finComp_locIdele_self w u)
  have hx : f * (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1 := by
    linear_combination (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) * hfe + (1 - f) * hg
  have i1 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u).2 h1
  have i2 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u⁻¹).2 h2
  rw [map_inv] at i2
  have := h e f hp _ hx i1 i2
  exact (congrArg Circle.toUnits this).trans (map_one _)

theorem good_of_ne {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) (hv : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.Hk3.Good R t w := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  intro PP hPP
  have key : PP.under (𝓞 D.host.F) ≠ v := by
    intro hu
    obtain ⟨e, f', hp⟩ := exists_isPrimeIdem hΦ PP
    obtain ⟨-, ε, hε, hf'⟩ := of_isPrimeIdem hΦ hp
    obtain ⟨ε', hε', rfl⟩ := hf
    rw [hu] at hε
    exact hv PP hPP e f' hp (by rw [hf', placeIdem_unique hε hε'])
  refine ⟨fun h => key (h ▸ hw), fun h => key ?_⟩
  rw [← hw, (isConjPl_iff PP w).1 h, under_cP]

theorem chrTh_unrAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hv w hw
  obtain ⟨he, hm⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hL.lev t w (good_of_ne R t hf hv hw)
  have a := unrAt_of_unrPl (hm ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega))
  have b := unrAt_of_unrPl he
  exact ⟨a, a.mul b.inv⟩

end GlobalTheory.GoodModUnr
end
end

