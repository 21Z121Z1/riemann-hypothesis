import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0760
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0755
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0747
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0754
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0583
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0639
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0762
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LineAdjZero

open GlobalTheory.AdjLatO GlobalTheory.LineCompLat

variable {D : D7}

theorem genT_smul_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (c : D.host.E) (t : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (c • t) u = genT T x t (star c • u) := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem genT_add_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (t t' : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (t + t') u = genT T x t u + genT T x t' u := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, mul_add,
    TensorProduct.tmul_add]

theorem genT_zero_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (u : Fin n → D.host.E) :
    genT T x 0 u = 0 := by
  ext p q
  simp [genT]

theorem latO_idLat_le (S T : HSp D) (LS : Lat S) (LT : Lat T) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (hI : ∀ σ ∈ I, ∀ τ ∈ I, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ) (P : GlobalTheory.FinPl.Pl D → Prop) :
    latO S T (idLat I LS : Set _) (idLat I LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  have hσ : ∀ σ ∈ I, ∀ t ∈ idLat I LT, star σ • t ∈ LT := by
    intro σ hσ t ht
    unfold idLat at ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
      obtain ⟨c, hc⟩ := hI σ hσ τ hτ
      rw [smul_smul, ← hc, algebraMap_smul]
      exact LT.smul_mem c hy
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact LT.smul_mem r hy
  have key : ∀ t ∈ idLat I LT, genT S (pairA D.host.F 0 α) s (a • t) ∈ latO S T (LS : Set _) (LT : Set _) P := by
    have hs' : s ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ LS, z = s • y} := hs
    clear hs
    induction hs' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨σ, hσI, y, hy, rfl⟩ := hz
      intro t ht
      rw [genT_smul_left, smul_comm]
      exact genT_mem_of_mem_span T S LT LS P α hα hP y hy _
        (Submodule.subset_span ⟨a, ha, _, hσ σ hσI t ht, rfl⟩)
    | zero => intro t _; rw [genT_zero_left]; exact zero_mem _
    | add y z _ _ hy hz => intro t ht; rw [genT_add_left]; exact add_mem (hy t ht) (hz t ht)
    | smul r y _ hy =>
      intro t ht
      obtain ⟨r', hr'⟩ := GlobalTheory.FinPl.LatMem.star_int r
      have e1 : r • y = (r : D.host.E) • y := (algebraMap_smul D.host.E r y).symm
      have e2 : (r' : D.host.E) • t = r' • t := algebraMap_smul D.host.E r' t
      rw [e1, genT_smul_left, smul_comm, ← hr', e2]
      exact hy _ (Submodule.smul_mem _ r' ht)
  exact key t ht

theorem star_mul_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∀ σ ∈ shiftId G, ∀ τ ∈ shiftId G, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ := by
  intro σ hσ τ hτ
  have h1 : star σ ∈ (shiftId G)⁻¹ := by
    rw [← GlobalTheory.RowBig.conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, ← Formalism.BasicNotions.bridge_star_holds D.R D.host, star_star]
    exact hσ
  have h2 := FractionalIdeal.mul_mem_mul h1 hτ
  rw [inv_mul_cancel₀ (GlobalTheory.RowBig.shiftId_ne_zero G)] at h2
  exact (FractionalIdeal.mem_one_iff _).1 h2

theorem mulVec_idLat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ')
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ' := by
  intro x hx
  unfold idLat at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨τ, hτ, _, hM y hy, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul r y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r hy

theorem lineComp_mem_shift : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1))) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have sdC' := GlobalTheory.RowBig.isSelfDualC_idLat_shiftId G _ sdC
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hD T L μ0 hL sc G W Mv hM (2 * ρ + 1) (by omega) (by omega) hU1
  clear hU1 hu
  have hq : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) :=
    GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits (F.dJ ρ h) (GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all sdC) fun v => (hloc v).2
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC' _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1)))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    exact rat_mulVec_latV (F.dJ ρ h).q0 (mulVec_idLat _ hq _) hy
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4

theorem adj_lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu
  have hx := lineComp_mem_shift D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  exact latO_idLat_le _ _ _ _ (shiftId G) (star_mul_shiftId G) _
    (incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _ _ _ _
      (GlobalTheory.AdjSrcZero.star_smul_mem_span G _) _ hx)

end GlobalTheory.LineAdjZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift : ∀ D : D7, UpFB D := by
  first | exact @GlobalTheory.UpFromBessel.upFB | exact GlobalTheory.UpFromBessel.upFB | (intros; apply GlobalTheory.UpFromBessel.upFB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDepthLatticeMulVecMemCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ShiftRowMul

variable {D : D7}

theorem latV_at_le_all {S : HSp D} {Λ : Lat S} {v : GlobalTheory.FinPl.Pl D} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S Λ (· = v)) : y ∈ latV S Λ (fun _ => True) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at *
  refine AddSubgroup.closure_mono ?_ hy
  rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun _ h => (h trivial).elim, a, ha, x, hx, rfl⟩

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : D.host.E} (hc : c ∈ I⁻¹) {x : Fin n → D.host.E}
    (hx : x ∈ idLat I Λ) : c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    have h1 : c * t ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hI]; exact FractionalIdeal.mul_mem_mul hc ht
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Λ.smul_mem r hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul r x _ h =>
    rw [← algebraMap_smul D.host.E r x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Λ.smul_mem r h

theorem smul_mem_latV {S : HSp D} {Λ : Lat S} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {v : GlobalTheory.FinPl.Pl D}
    {s : AE D} (hs : s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * I⁻¹) v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S (idLat I Λ) (fun _ => True)) : s • z ∈ latV S Λ (· = v) := by
  have hAA : D.host.AA ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hs
    by_cases hI : I = 0
    · subst hI
      rw [_root_.inv_zero, mul_zero, FractionalIdeal.mem_zero_iff] at hb
      subst hb
      rw [TensorProduct.tmul_zero, zero_smul]; exact zero_mem _
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hz
      have hba : b * a ∈ I⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hb ha
        rwa [mul_comm D.host.AA⁻¹, mul_assoc, inv_mul_cancel₀ hAA, mul_one] at this
      refine AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβ hα,
        fun w hw => by rw [map_mul, hβv w hw, zero_mul], 1, rfl, (b * a) • x, smul_mem_of_idLat hI hba hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.FinPlLoc.pairA_mul, one_mul, mul_assoc]
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | neg s _ h => rw [neg_smul]; exact neg_mem h

end GlobalTheory.ShiftRowMul

theorem GlobalTheory.AscFin.shiftRow_smul_mulVec_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * (shiftId G)⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hq T L μ0 hL sc G W Mv hMv F hF ρ h M hM v y hy s hs
  have hBig : M ∈ latBig G (2 * ρ + 1) :=
    GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W Mv hMv (2 * ρ + 1) (by omega) (by omega) hM
  have hS : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1 + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT := ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W Mv hMv F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  have hmap := ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT (fun _ => True) M).1 hBig).2 y
    (GlobalTheory.ShiftRowMul.latV_at_le_all hy)
  exact GlobalTheory.ShiftRowMul.smul_mem_latV hs hmap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), IsCompact ((pcBF W F ρ h).A₂ : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ)) ∧ ∃ U : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ), IsOpen U ∧ (0 : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ (pcBF W F ρ h).A₂ := by
  first | exact @GlobalTheory.AnnPiece.pcBF_A₂_compact_open | exact GlobalTheory.AnnPiece.pcBF_A₂_compact_open | (intros; apply GlobalTheory.AnnPiece.pcBF_A₂_compact_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem pcBF_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨fun u hu => ?_⟩
  have e1 := ((F.dB ρ h).coordS (G.V (.grid (2 * ρ + 1) 0))).symm_apply_apply u
  have e2 := ((F.dJ ρ h).coordT (F.V₀ ρ)).symm_apply_apply (u ⬝ (F.dB ρ h).j0)
  obtain ⟨s1, -, s3⟩ := GlobalTheory.T.bessel_depth_lattice_splits_along_source_witt D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  obtain ⟨f4, i4⟩ := GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have b := GlobalTheory.T.depth_lattice_core_parts_mem_selfDual_lattice D hq T L μ0 hL sc G W M hM F hF ρ h _ s3
  refine ⟨u ⬝ (F.dB ρ h).jX, s1, u ⬝ (F.dB ρ h).jY, AddSubgroup.subset_closure ⟨f4, i4⟩,
    (F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0), b.1, (F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0), b.2,
    (F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0), GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt D hq T L μ0 hL sc G W M hM F hF ρ h _ s3, ?_,
    GlobalTheory.T.base_point_character_trivial_on_depth_lattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu, GlobalTheory.T.besselSecondBasePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu⟩
  have e2' : (F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0)) = (u ⬝ (F.dB ρ h).j0) := by
    simp only [HypDec.coordT, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e2
    exact (add_right_comm _ _ _).trans e2
  have e1' : (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) + (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) + (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) = u := by
    simp only [HypDec.coordS, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e1
    exact (add_right_comm _ _ _).trans e1
  rw [e2', e1']

end GlobalTheory.AscFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowZeroLeSelfDualHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_zero_le_selfDualHomLattice : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  first | exact @GlobalTheory.RowBig.latRow_zero_le_latBig | exact GlobalTheory.RowBig.latRow_zero_le_latBig | (intros; apply GlobalTheory.RowBig.latRow_zero_le_latBig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingMethodConsequence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ScalConj.scalarConjRow : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  intro pI hH pD _ pBZ _ _ pU pW _ D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hsep hC hEx hP
  exact GlobalTheory.T.conjugate_baseLevel_of_howeUnramifiedCorrespondence hH T R F κ v₀ O s hOk hsep hC hEx
    (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law GlobalTheory.SingleBlock.localIntegralSingleBlock R.toRealDat F.lv2 (GlobalTheory.PlaceTensor.placeModels D))
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses pD pW pI R.toRealDat F.lv2 hP)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula (GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral) R.toRealDat F.lv2 (GlobalTheory.PlaceTensor.placeModels D))
    (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue pD pBZ pU R.toRealDat F.lv2)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetFJ

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv g hg u a ha hoff
  obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hιι, hX, hΦ, hA⟩ :=
    GlobalTheory.T.split_local_frame_diagonal D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨ha1, ha2⟩ := hA a ha
  subst hpv
  obtain ⟨k₀, hk₀, hoff'⟩ := GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power D k p _ σ β (xFB F σ h') ι ι' s t (G.pl.depth sc p.v) (G.pl.depth_pos sc _) hι hι' hιι
    hX hΦ g hg u a ha1 ha2 hoff
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  refine ⟨β.gl _, GlobalTheory.T.framedCongruenceElement_mem_principalCongruence D hQ T L μ0 hL sc G W M hM (.grid (2 * σ + 2) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
  exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetFJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

open scoped Topology

noncomputable section

namespace GlobalTheory.VacTranslate

variable {D : D7}

theorem exists_finCong_mod (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (hV : IsSelfDualC V ΛV) (hW : IsSelfDualC W ΛW)
    (N : ℕ) (hN : 0 < N) :
    ∃ n : ℕ, ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V n.factorial k →
      ∀ x ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        ∃ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
          actO V W k 1 x = x + N • l := by
  by_contra hne
  push_neg at hne
  choose k hk hkc hkne using hne
  have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
  have ht2 : Filter.Tendsto (fun n => ((k n, (1 : GA D W)) : GA D V × GA D W)) Filter.atTop (𝓝 1) := by
    have := ht.prodMk_nhds (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : GA D W)) Filter.atTop (𝓝 1))
    rwa [Prod.mk_one_one] at this
  obtain ⟨n, hn⟩ := (ht2.eventually (GlobalTheory.Mem.CoefInv.eventually_mod ΛV ΛW hV hW N hN)).exists
  obtain ⟨x, hx, hxne⟩ := hkne n
  obtain ⟨l, hl, e⟩ := hn x hx
  exact hxne l hl e

theorem psi_four_eq_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hlat : ∀ u ∈ Λ, heisO ψ S T (2 • u) f = f) {w₀ : WO S T} (hw₀ : f w₀ ≠ 0) {a b : WO S T} (ha : a ∈ Λ)
    (hb : b ∈ Λ) : ψ (symplO S T ((2 * 2) • a) b) = 1 := by
  have h := GlobalTheory.SplitScalar.heisO_comm ψ S T (2 • a) (2 • b) f
  rw [hlat b hb, hlat a ha, hlat b hb] at h
  have h3 := congrFun h w₀
  rw [Pi.smul_apply, smul_eq_mul] at h3
  have h4 : ψ (symplO S T (2 • a) (2 • b)) = 1 :=
    mul_right_cancel₀ hw₀ (h3.symm.trans (one_mul _).symm)
  rwa [← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_smul] at h4

theorem lat_iff_of_mod {V W : HSp D} {L : AddSubgroup (WO V W)} {n : ℕ}
    (hn : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V n.factorial k → ∀ x ∈ L, ∃ l ∈ L, actO V W k 1 x = x + 1 • l)
    {k : GA D V} (hk : k ∈ GlobalTheory.Member.PrincLevel.levelGroup V n.factorial) :
    ∀ u : WO V W, u ∈ L ↔ ∃ u₀ ∈ L, u = actO V W k 1 u₀ := by
  have hki := inv_mem hk
  intro u
  constructor
  · intro hu
    obtain ⟨l, hl, e⟩ := hn k⁻¹ hki.1 hki.2 u hu
    refine ⟨actO V W k⁻¹ 1 u, by rw [e, one_nsmul]; exact L.add_mem hu hl, ?_⟩
    have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D W) u
    rw [inv_inv, inv_one] at this
    exact this.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    obtain ⟨l, hl, e⟩ := hn k hk.1 hk.2 u₀ hu₀
    rw [e, one_nsmul]
    exact L.add_mem hu₀ hl

end GlobalTheory.VacTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRow_data_have_depth : GlobalTheory.SepRows.DatumDep := by
  first | exact @GlobalTheory.FirstRowDepth.datumDep | exact GlobalTheory.FirstRowDepth.datumDep | (intros; apply GlobalTheory.FirstRowDepth.datumDep <;> assumption)
end

