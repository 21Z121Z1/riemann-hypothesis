import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0095
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.Bundle0004
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0085
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.OneLetterJetKernel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0096
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtension
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

open Classical in

theorem hodgeTateJumps_coefficientExtension : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  intro D L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  obtain ⟨ep, hep⟩ := hJ
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  have hτ₀ : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) :=
    ⟨((D.nbr i w hw).Kw.1.val).codRestrict Cx.LL.1.toSubalgebra
      (fun x => Cx.le ((D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x))⟩
  obtain ⟨τ₀⟩ := hτ₀
  obtain ⟨g₀, ρ₀, hr₀, -⟩ := hep i r hP.good w hw Cx τ₀
  obtain ⟨κ, hκ⟩ := exists_base_reads D.host (D.nbr i w hw).Kw Cx.LL (Br.cEw D.nbr i w hw)
    (D.naut.iotaQC i) τ₀ g₀ hr₀.1
  refine ⟨if ep then 1 else -1, κ, ?_⟩

  have hc : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), (Continuous fun g => M g) →
      Continuous (TruncatedSeriesCountingIdentities.locC Cx M) := by
    intro k M hM
    refine continuous_matrix fun a b => ?_
    have h1 := locC_cont D i M hM w hw Cx (Pi.single b 1)
    have h2 := (continuous_apply a).comp h1
    simpa [Function.comp_def, Matrix.mulVec_single] using h2
  have hW : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hP.contρ
  refine GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition L C₀ i w hw C r ρ π _ κ hR h7 (hF i w hw Cx).2.2.1
    (fun z => (IntermediateField.inclusion Cx.le).commutes z)
    (fun x => hc _ (rTwO_cont D i r hP.cont x)) (hc _ hW) (fun x => hP.crys w hw Cx x) hP.dec ?_
  intro τ
  obtain ⟨g, ρ', hrd, hx, hπ⟩ := hep i r hP.good w hw Cx τ
  have hup : (decide (LJ.TypeU D ep g) = true ↔ LJ.TypeU D ep g) := decide_eq_true_iff
  have hs := GlobalTheory.T.rationalJumpSets_eq_integerMultisets_twistedDual D i ρ' g ep _ hrd.2 hup
  refine ⟨g, hκ τ g hrd.1, ?_, ?_⟩
  · intro x a ha
    exact ((hs a).1).1 (((hx x a).2.2.1).1 ha)
  · intro a
    refine ((hπ ρ π hP.mem hP.dec a).2.2.2).trans ?_
    by_cases h : a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep = true then 1 else -1) g)
    · rw [if_pos ((hs a).2.2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hs a).2.1 h')), if_neg h]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBasesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_jets_realPlace_local_bases : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  first | exact @GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | exact GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | (intros; apply GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWOfMulEqOne
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CompareInert

section Letters

variable (D : D7) (p : ℕ) [Fact p.Prime]

variable {D p}

def beT (N N' : ℕ) (r : Bool × HH D) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    MvPowerSeries (TeichmullerFactorisation.Var D N N') ℂ_[p] :=
  ∑ a : Fin N, ∑ b : Fin N', MvPowerSeries.subst
    (fun s : ZMod (nP D p) => TeichmullerFactorisation.zOf D p ((TeichmullerFactorisation.letter D p r s, a, b) : TeichmullerFactorisation.Var D N N')) be

end Letters

section Rings

open Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

theorem mem_Wp_of_kur {x : ℂ_[l]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) : x ∈ Wp l := by
  have hp : l.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers l).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime l = {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem Wp_subset_Kur {x : ℂ_[l]} (hx : x ∈ Wp l) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  refine closure_mono (s := ((Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Subring ℂ_[l]) : Set ℂ_[l])) ?_ hx
  intro y hy
  have hle : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro ζ ⟨n, h0, hn, h⟩
    exact Subfield.subset_closure ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (Nat.coprime_comm.mp hn), h⟩
  exact hle hy

theorem Wp_subset_Wfrac {x : ℂ_[l]} (hx : x ∈ Wp l) : x ∈ product_zeroth_first_parts.Wfrac l := by
  refine closure_mono (s := ((Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Subring ℂ_[l]) : Set ℂ_[l])) ?_ hx
  intro y hy
  have hle : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
      (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubring :=
    Subring.closure_le.2 fun ζ hζ => Algebra.subset_adjoin hζ
  exact hle hy

theorem exists_pow_norm_le {K : Type*} [NormedField K] {a : K} (ha : ‖a‖ < 1) (x : K) : ∃ k : ℕ, ‖a ^ k * x‖ ≤ 1 := by
  by_cases hr : x = 0
  · exact ⟨0, by simp [hr]⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hr)) ha
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow]
  have h0 : 0 < ‖x‖ := norm_pos_iff.2 hr
  calc ‖a‖ ^ k * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ h0.ne'

theorem algebraMap_mem_Kur (r : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] r ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨k, hk⟩ := exists_pow_norm_le hl r
  have h1 := Wp_subset_Kur (GlobalTheory.BiextInhab.algebraMap_mem_Wp hk)
  have h2 : algebraMap ℚ_[l] ℂ_[l] r =
      (((l : ℂ_[l]) ^ k)⁻¹) * algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ k * r) := by
    have hc : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    rw [map_mul, map_pow, map_natCast]
    field_simp
  rw [h2]
  exact mul_mem (inv_mem (pow_mem (natCast_mem _ l) k)) h1

def kurAlg (l : ℕ) [Fact l.Prime] : Subalgebra ℚ_[l] ℂ_[l] :=
  { (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l).toSubring with
    algebraMap_mem' := algebraMap_mem_Kur }

theorem Wfrac_subset_Kur {x : ℂ_[l]} (hx : x ∈ product_zeroth_first_parts.Wfrac l) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have h1 : Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) ≤ kurAlg l :=
    Algebra.adjoin_le fun ζ hζ => Wp_subset_Kur (Subring.le_topologicalClosure _ (Subring.subset_closure hζ))
  have hx' : x ∈ closure (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := by
    rw [← Subalgebra.topologicalClosure_coe]; exact hx
  have hc : IsClosed (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l : Set ℂ_[l]) := Subfield.isClosed_topologicalClosure _
  exact closure_minimal (fun y hy => h1 hy) hc hx'

theorem norm_l_lt : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(l : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l]
    exact norm_algebraMap' ℂ_[l] _
  rw [h]
  exact Padic.norm_p_lt_one

theorem mem_Wint_iff {x : ℂ_[l]} : x ∈ product_zeroth_first_parts.Wint l ↔ x ∈ Wp l := by
  constructor
  · rintro ⟨h1, h2⟩
    exact mem_Wp_of_kur (Wfrac_subset_Kur h1) h2
  · intro h
    exact ⟨Wp_subset_Wfrac h, GlobalTheory.UnitModel.norm_le_one_of_mem_Wp h⟩

theorem mem_Wfrac_iff {x : ℂ_[l]} : x ∈ product_zeroth_first_parts.Wfrac l ↔ InWf x := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_pow_norm_le (norm_l_lt) x
    exact ⟨k, mem_Wp_of_kur (mul_mem (pow_mem (natCast_mem _ l) k) (Wfrac_subset_Kur h)) hk⟩
  · rintro ⟨k, hk⟩
    have hc : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    have h1 := Wp_subset_Wfrac hk
    have h2 : x = algebraMap ℚ_[l] ℂ_[l] (((l : ℚ_[l]) ^ k)⁻¹) * ((l : ℂ_[l]) ^ k * x) := by
      rw [map_inv₀, map_pow, map_natCast]
      field_simp
    rw [h2]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) h1

end Rings

section Props

open Formalism.MainNotions.GL3Theta MvPowerSeries

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

def twoB (d : ℕ) : ZMod d × Fin 2 ≃ ZMod d × Bool := (Equiv.refl _).prodCongr finTwoEquiv

def cobT (r : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l] × MvPowerSeries (ZMod d × Fin 2) ℂ_[l] :=
  (subst (fun s : ZMod d => if s.val % 2 = r then jetLogG l d (s, 0) + jetLogG l d (s, 1) else jetLogG l d (s, (0 : Fin 2))) be,
   subst (fun s : ZMod d => jetLogG l d (s, (0 : Fin 2))) be +
    subst (fun s : ZMod d => if s.val % 2 = r then jetLogG l d (s, 1) else jetLogG l d (s, (0 : Fin 2))) be)

end Props

section Sign

open Formalism.MainNotions.GL3Theta MvPowerSeries

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

end Sign

section Reps

variable (D : D7) (p : ℕ)

theorem posPl_back (z : Bool × HH D) (e : ℕ) : posPl D p (posPl D p z e) (e * (nP D p - 1)) = z := by
  have hn : 1 ≤ nP D p := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have h : e + e * (nP D p - 1) = e * nP D p := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [hm]; simp; ring
  rw [posPl_add, h, ← posPl_mod, Nat.mul_mod_left, posPl_zero]

def orbSetoid : Setoid (Bool × HH D) where
  r a b := ∃ e : ℕ, posPl D p a e = b
  iseqv :=
    ⟨fun a => ⟨0, posPl_zero D p a⟩,
      fun {a b} ⟨e, h⟩ => ⟨e * (nP D p - 1), by rw [← h]; exact posPl_back D p a e⟩,
      fun {a b c} ⟨e, h⟩ ⟨f, k⟩ => ⟨e + f, by rw [← posPl_add, h, k]⟩⟩

end Reps

section Hyp

end Hyp

section Statements

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Statements

section Units

open MvPowerSeries

variable {D : D7} {p : ℕ} [Fact p.Prime]

end Units

section Direction

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[l])

end Direction

section Main

variable (D : D7) {Dx : DivX D} {Tw : TwForms D}

end Main

end GlobalTheory.CompareInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeOrbitGainWithoutOperator
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob alG capG lsG deLoss dSet lgN DivAB)
open Formalism.GrowthSums (excessGain)
open Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights (young_second_row_length_count yd_size yd_one_le_colLen yd_colLen_le)
open Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel (tieFrame)

namespace GlobalTheory.KerGaussA

theorem card_height_one (μ : YoungDiagram) :
    (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)).card = μ.rowLen 0 - μ.rowLen 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (μ.rowLen 0))))
    (fun c => 2 ≤ μ.colLen c)
  rw [young_second_row_length_count, Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)) =
      Finset.univ.filter (fun c : Fin (μ.rowLen 0) => ¬ 2 ≤ μ.colLen c) := by
    ext c
    have := yd_one_le_colLen μ c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [e]; omega

theorem mem_dSet {ν : ℕ} [NeZero ν] (TT : Finset (ZMod (2 * ν))) (s : ZMod (2 * ν)) (e : ℕ) :
    2 * e + 1 ∈ dSet TT s ↔ (2 * e + 1 < 2 * ν ∧ s + ((2 * e + 1 : ℕ) : ZMod (2 * ν)) ∈ TT) := by
  have hν : 0 < ν := Nat.pos_of_ne_zero (NeZero.ne ν)
  have : NeZero (2 * ν) := ⟨by omega⟩
  unfold dSet
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨s', ⟨h1, -⟩, h3⟩
    refine ⟨h3 ▸ ZMod.val_lt _, ?_⟩
    rw [← h3, ZMod.natCast_zmod_val]
    simpa using h1
  · rintro ⟨h1, h2⟩
    refine ⟨_, ⟨h2, ?_⟩, ?_⟩
    · rw [ZMod.val_add, ZMod.val_cast_of_lt h1, Nat.mod_mod_of_dvd _ (Dvd.intro ν rfl)]
      omega
    · rw [add_sub_cancel_left, ZMod.val_cast_of_lt h1]

theorem tsum_odd (f : ℕ → ℝ) (hf : ∀ e, ¬ Odd e → f e = 0) : ∑' e : ℕ, f (2 * e + 1) = ∑' e : ℕ, f e := by
  refine Function.Injective.tsum_eq (g := fun e : ℕ => 2 * e + 1) (fun a b h => by simpa using h) ?_
  intro e he
  have ho : Odd e := by
    by_contra h
    exact he (hf e h)
  obtain ⟨k, hk⟩ := ho
  exact ⟨k, hk.symm⟩

theorem constantCoeff_sumE {K ι : Type} [Field K] [Fintype ι] {N0 N1 : ℕ} (be : MvPowerSeries (Fin 2) K)
    (h : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = 0 := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  refine MvPowerSeries.constantCoeff_subst_eq_zero ?_ ?_ h
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
  · intro a; simp

theorem exists_root_sq (l : ℕ) [hl : Fact l.Prime] : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  refine Formalism.L2.Th1.D.kurRoots l (l ^ 2 - 1) (by omega) fun hd => ?_
  have h2 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
  have h3 : l ∣ 1 := by
    have := (Nat.dvd_sub h2 hd)
    rwa [Nat.sub_sub_self h1.le] at this
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_pi (l : ℕ) [hl : Fact l.Prime] : ∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

theorem kernel_bound (l : ℕ) [Fact l.Prime] (ν m N0 N1 : ℕ) [NeZero ν] (hm : m = ν) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin m → MaximalUnramifiedExtension l)
    (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (hF : IsLawOfLog l F) (h1 : F1 F be0) (h2 : F2 l σ be0)
    (hO : OwOK (2 * ν) σ om oms) (hT : TrDual (2 * ν) σ om oms)
    (U0 : MvPowerSeries (Bool × Fin m × Fin N0 × Fin N1) ℂ_[l]) (hU : Formalism.DworkPowerSeriesWeights.Integral U0)
    (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (hp : ∀ s c, hts s c ≤ N0) (I : ∀ s c, Fin (hts s c) → Fin N1) (n : (ZMod (2 * ν) × Fin N0 × Fin N0) →₀ ℕ) :
    ‖MvPolynomial.coeff n (Formalism.DworkPowerSeriesWeights.frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms
        (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) * U0)))‖ ≤
      (l : ℝ) ^ (-(excessGain (l : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss l N0 N1 TT (alG TT colN hts) (lsG TT colN hts)))) := by
  subst hm
  have : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have hb : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) = 0 := by
    have h0 : MvPowerSeries.constantCoeff be0 = 0 := h1.1 0 (Or.inl rfl)
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  exact (Formalism.L2.Th1.D.kernelOfF l (MaximalUnramifiedExtension l) σ hσ (exists_root_sq l) F hF be0 h1 h2 ℂ_[l] (MaximalUnramifiedExtension l).subtype m N0 N1
    (fun _ => rfl) (exists_pi l) om oms hO hT U0 _ hU (constantCoeff_sumE _ hb)
    ((Formalism.InvariantFactorPaths.G7.equivalence_rules ℂ_[l] _).1 _) TT colN hts hp I n).1

theorem kvalGe_gainA : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th (gainA Lc) := by
  rintro Lc ep be hep ⟨σ, F, be0, om, oms, ζ, hD, rfl⟩ hB
  obtain ⟨U0, hU, hTh⟩ := GlobalTheory.T.exists_integral_orbit_series Lc ep σ F be0 om oms ζ hD hB
  have hp : ∀ s (c : Fin ((Lc.nu s).rowLen 0)), (Lc.nu s).colLen c ≤ Lc.N0 :=
    fun s c => (yd_colLen_le _ _).trans (Lc.nu_rows s)
  refine tieFrame Lc.l Lc.d Lc.N0 Lc.N1 Lc.nu hp Lc.Th ep _ hep ?_
  intro I n
  rw [hTh]
  clear hTh hB
  obtain ⟨hσ, hF, h1, h2, hO, hT, -⟩ := hD
  obtain ⟨J, rank_lt_alt, nu, hnu, TT⟩ := Lc
  obtain @⟨l, hl, h5, d, hd, hev, h2d, N0, N1, Th⟩ := J
  obtain ⟨ν, hν⟩ : ∃ ν, d = 2 * ν := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  subst hν
  have : NeZero ν := ⟨by omega⟩
  refine (kernel_bound l ν (2 * ν / 2) N0 N1 (by omega) σ F be0 om oms hσ hF h1 h2 hO hT U0 hU TT
    (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) hp I n).trans (le_of_eq ?_)
  set Lc : product_zeroth_first_parts.Loc := ⟨⟨l, h5, 2 * ν, hev, h2d, N0, N1, Th⟩, rank_lt_alt, nu, hnu, TT⟩ with hLc
  have hal : alG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = alLoc Lc := by
    funext s
    unfold alG alLoc
    by_cases hs : s ∈ TT
    · rw [if_pos hs, if_pos (show s ∈ Lc.TT from hs)]
      exact card_height_one _
    · rw [if_neg hs, if_neg (show s ∉ Lc.TT from hs)]
  have hcap : capG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = Lc.cap := by
    funext s
    unfold capG
    rw [hal]
    unfold alLoc product_zeroth_first_parts.Loc.cap
    have hle : (nu s).rowLen 1 ≤ (nu s).rowLen 0 := (nu s).rowLen_anti 0 1 (Nat.zero_le _)
    by_cases hs : s ∈ Lc.TT
    · rw [if_pos hs, if_pos hs]
      show (nu s).rowLen 0 - ((nu s).rowLen 0 - (nu s).rowLen 1) = (nu s).rowLen 1
      omega
    · rw [if_neg hs, if_neg hs]
      rfl
  have hls : lsG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = fun s => Lc.size s - alLoc Lc s := by
    funext s
    unfold lsG
    rw [hal, ← yd_size]
    rfl
  rw [hcap, hls, hal]
  congr 2
  unfold excessGain gainA deLoss
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← tsum_odd _ (fun e he => if_neg (fun h => he h.1))]
  refine tsum_congr fun e => ?_
  have ho : Odd (2 * e + 1) := ⟨e, rfl⟩
  by_cases h : 2 * e + 1 ∈ dSet TT s
  · rw [if_pos h, if_neg (fun h' => h'.2 ((mem_dSet TT s e).1 h))]
  · rw [if_neg h, if_pos ⟨ho, fun h' => h ((mem_dSet TT s e).2 h')⟩]

end GlobalTheory.KerGaussA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWordStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.fits_of_isSubOfSums | exact GlobalTheory.HTW.Rec.fits_of_isSubOfSums | (intros; apply GlobalTheory.HTW.Rec.fits_of_isSubOfSums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumpsStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  first | exact @GlobalTheory.HTW.Rec.fits_lowCount_of_matRep | exact GlobalTheory.HTW.Rec.fits_lowCount_of_matRep | (intros; apply GlobalTheory.HTW.Rec.fits_lowCount_of_matRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamifiedStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E, (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  first | exact @GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | exact GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | (intros; apply GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePointStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  first | exact @GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | exact GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | (intros; apply GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt <;> assumption)
end

