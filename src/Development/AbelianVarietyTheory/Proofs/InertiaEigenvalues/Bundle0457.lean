import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveMaxUnramifiedSubfieldAlgebraMap
section
noncomputable section

namespace GlobalTheory.TopSteps.FinSummandDim

open Module TensorProduct
open GlobalTheory.AdmLoc GlobalTheory.TopSteps GlobalTheory.TopSteps.FinSummand Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace Qp] [TopologicalSpace LL]

theorem h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) : H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ = ⊥ := by
  obtain ⟨_, _, _⟩ := hO.1
  refine invariants_stableLattice_mod_irreducible_eq_bot (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hlam ?_
  change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
  rw [latRep_twLattice]
  exact h0

theorem finrank_h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) :
    finrank LL ↥(H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) = 0 := by
  rw [h0V_tw hO Γ hχ hlam h0, finrank_bot]

theorem isCompl_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    ∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C := by
  obtain ⟨_, _, _⟩ := hO.1
  exact exists_isCompl_of_saturated _ (h1fT_saturated PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L)

theorem finrank_tw [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V)) :
    finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = finrank LL (FiniteCohomology PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) := by
  obtain ⟨_, _, _⟩ := hO.1
  exact finrank_h1fT PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hT

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem cont_inv (hC : S.CrysCalc) : Continuous fun g => algebraMap S.O ↥S.LL.1 (S.Γ.χ₁⁻¹ g) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2.1

abbrev tw (hC : S.CrysCalc) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O := twLat S.Γ.T₀ S.Γ.χ₁⁻¹ (cont_inv S hC)

theorem tw_crysWith (hC : S.CrysCalc) :
    CrysWith (P.PD S.K) S.emb (tw S hC).ρ (fun i => (S.D.U i).map (· + -S.D.w i)) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1

theorem tw_h0V (hC : S.CrysCalc) (hV : S.Vanish) : H0V (tw S hC).ρ = ⊥ := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

theorem tw_finrank_h0V (hC : S.CrysCalc) (hV : S.Vanish) : finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) = 0 := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact finrank_h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

theorem exists_isCompl (hC : S.CrysCalc) (hH : S.FreeH) :
    ∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C :=
  isCompl_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hH.1.2.1

theorem finrank_hf (hC : S.CrysCalc) :
    finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) :=
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  finrank_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC)
    (GlobalTheory.Cyc.locLat_isOpen (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ.T₀)

theorem sum_card_neg :
    ∑ i, Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) = S.D.dsum := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

theorem bijective_maxUnramifiedSubfield_algebraMap : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) := by
  obtain ⟨⟨-, hA, -⟩, -⟩ := S.hyp
  exact ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩

theorem fSummand_of_finrank (hC : S.CrysCalc) (hH : S.FreeH)
    (hd : finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) = S.D.dsum) : S.FSummand :=
  ⟨exists_isCompl S hC hH, (finrank_hf S hC).trans hd⟩

theorem fSummand_of_dim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ)) : S.FSummand := by
  refine fSummand_of_finrank S hC hH ?_
  have h0 := tw_finrank_h0V S hC hV
  have h1 : ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ) = (S.D.dsum : ℤ) := by
    rw [← sum_card_neg S, Nat.cast_sum]
  have key : ∀ (a b c : ℕ) (s : ℤ), (a : ℤ) = (b : ℤ) + s → b = 0 → s = (c : ℤ) → a = c := by
    intro a b c s h h' h''
    omega
  exact key _ _ _ _ hd h0 h1

theorem fSummand_of_codim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hD : Module.Finite ↥S.LL.1 ↥(DdR (P.PD S.K) (tw S hC).ρ))
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ((finrank ↥S.LL.1 ↥(DdR (P.PD S.K) (tw S hC).ρ) : ℤ) -
        finrank ↥S.LL.1 ↥(DdR (P.PD S.K) (tw S hC).ρ ⊓
          FilV (P.PD S.K) (LL := ↥S.LL.1) (V := (tw S hC).V) 0))) : S.FSummand := by
  obtain ⟨⟨-, -, hn, hemb, -⟩, -⟩ := S.hyp
  exact fSummand_of_dim S hC hV hH (hd.trans (congrArg _
    (codim_fil_zero (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) hn _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockAndTorsionExponentBoundsCanonicalHubData
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem blockAndTorsionExponentBounds_canonicalHubData : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → 1 ≤ L.sc.L → ∀ c : ℝ, 120 ≤ c → GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c := by
  intro D L HW R X hX hL c hc
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  have hnV : 1 ≤ D.R.nV := by
    show 1 ≤ D.R.r + D.R.t
    omega
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hnVR : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hN : 1 ≤ 4 * D.R.n * D.R.nV := by
    have := Nat.mul_le_mul hn hnV
    nlinarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L := rfl
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  refine ⟨?_, ?_⟩
  · intro i _ _ _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.cB]
    have h := GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL
    simp only [cBof, hb, hLg]
    push_cast at h
    have hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L := by positivity
    nlinarith
  · intro i _ _ _ _ u _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.c0]
    have h := GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL
    simp only [c0of, hOf, hb, hLg]
    push_cast at h ⊢
    have hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L := by positivity
    nlinarith

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem discAinf_isDomain : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    IsDomain (bk.DA ρ) ∧ (∀ x y : bk.DA ρ, (ρ : ℝ) ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ∧
      ∀ a : bk.DA ρ, a ≠ 0 → ∃ C : ℝ, ∀ y, ‖y‖ ≤ C * ‖a * y‖ := by
  intro l _ K bk ρ h0 h1
  obtain ⟨N, hmul, hadd, hl, hle, hge⟩ := GlobalTheory.T.exists_gaussNorm_ainf_disc l K bk ρ h0 h1
  have hρ : (0 : ℝ) < (ρ : ℝ) := h0
  obtain ⟨hdom, hnorm⟩ := GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm l (Ainf l) (bk.ev X) ρ N (ρ : ℝ) hρ hmul hadd hl hle hge
  refine ⟨hdom, hnorm, fun a ha => ⟨((ρ : ℝ) ^ 2 * ‖a‖)⁻¹, fun y => ?_⟩⟩
  have hpos : 0 < (ρ : ℝ) ^ 2 * ‖a‖ := mul_pos (pow_pos hρ 2) (norm_pos_iff.2 ha)
  have h := hnorm a y
  rw [← mul_assoc] at h
  calc ‖y‖ = ((ρ : ℝ) ^ 2 * ‖a‖)⁻¹ * ((ρ : ℝ) ^ 2 * ‖a‖ * ‖y‖) := by field_simp
    _ ≤ ((ρ : ℝ) ^ 2 * ‖a‖)⁻¹ * ‖a * y‖ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hpos.le)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  first | (exact @GlobalTheory.BKLim.beta_step) | (exact GlobalTheory.BKLim.beta_step) | (intros; apply GlobalTheory.BKLim.beta_step  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicative
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.GaussMul

open Filter

theorem norm_sum_lt_of_ultra {E ι : Type} [SeminormedAddCommGroup E] [IsUltrametricDist E] (s : Finset ι)
    (f : ι → E) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem exists_eq_sup {f : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (hle : ∀ n, f n ≤ M)
    (hsup : ∀ r : ℝ, 0 ≤ r → (∀ n, f n ≤ r) → M ≤ r) (ht : Tendsto f atTop (nhds 0)) : ∃ n, f n = M := by
  by_contra hne
  push_neg at hne
  have hlt : ∀ n, f n < M := fun n => lt_of_le_of_ne (hle n) (hne n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hM)))
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  have h1 : M ≤ max (M / 2) (f k) := hsup _ ((half_pos hM).le.trans (le_max_left _ _)) fun n => by
    by_cases hn : n < N + 1
    · exact (hk n (Finset.mem_range.2 hn)).trans (le_max_right _ _)
    · exact (hN n (by omega)).le.trans (le_max_left _ _)
  exact absurd h1 (not_le.2 (max_lt (half_lt_self hM) (hlt k)))

theorem gauss {D : Type} [NormedRing D] [IsUltrametricDist D] (hm : ∀ x y : D, ‖x * y‖ = ‖x‖ * ‖y‖) {ρ : ℝ}
    (hρ : 0 < ρ) (p q : ℕ → D) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hp : ∀ n, ‖p n‖ * ρ ^ n ≤ P)
    (hq : ∀ n, ‖q n‖ * ρ ^ n ≤ Q) (hp0 : ∃ n, ‖p n‖ * ρ ^ n = P) (hq0 : ∃ n, ‖q n‖ * ρ ^ n = Q) :
    ∃ N, ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, p x.1 * q x.2‖ * ρ ^ N = P * Q := by
  classical
  set n₀ := Nat.find hp0
  set m₀ := Nat.find hq0
  have hn₀ : ‖p n₀‖ * ρ ^ n₀ = P := Nat.find_spec hp0
  have hm₀ : ‖q m₀‖ * ρ ^ m₀ = Q := Nat.find_spec hq0
  refine ⟨n₀ + m₀, ?_⟩
  have hρN : 0 < ρ ^ (n₀ + m₀) := pow_pos hρ _
  have hmem : (n₀, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n₀ + m₀) := by simp
  rw [← Finset.add_sum_erase _ _ hmem]
  have hdom : ‖p n₀ * q m₀‖ * ρ ^ (n₀ + m₀) = P * Q := by
    rw [hm, pow_add, ← hn₀, ← hm₀]; ring
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n₀ + m₀)).erase (n₀, m₀), p x.1 * q x.2‖ < P * Q / ρ ^ (n₀ + m₀) := by
    refine norm_sum_lt_of_ultra _ _ (div_pos (mul_pos hP hQ) hρN) fun x hx => ?_
    rw [lt_div_iff₀ hρN]
    obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have e : ‖p x.1 * q x.2‖ * ρ ^ (n₀ + m₀) = (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) := by
      rw [hm, ← hx, pow_add]; ring
    rw [e]
    have h1 : 0 ≤ ‖p x.1‖ * ρ ^ x.1 := by positivity
    have h2 : 0 ≤ ‖q x.2‖ * ρ ^ x.2 := by positivity
    by_cases h : x.1 < n₀
    · have hlt : ‖p x.1‖ * ρ ^ x.1 < P := lt_of_le_of_ne (hp _) (Nat.find_min hp0 h)
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ (‖p x.1‖ * ρ ^ x.1) * Q :=
            mul_le_mul_of_nonneg_left (hq _) h1
        _ < P * Q := mul_lt_mul_of_pos_right hlt hQ
    · have h' : x.2 < m₀ := by
        by_contra h''
        apply hne
        ext <;> simp <;> omega
      have hlt : ‖q x.2‖ * ρ ^ x.2 < Q := lt_of_le_of_ne (hq _) (Nat.find_min hq0 h')
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ P * (‖q x.2‖ * ρ ^ x.2) :=
            mul_le_mul_of_nonneg_right (hp _) h2
        _ < P * Q := mul_lt_mul_of_pos_left hlt hP
  have hdom' : ‖p n₀ * q m₀‖ = P * Q / ρ ^ (n₀ + m₀) := by
    rw [eq_div_iff hρN.ne', hdom]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdom']; exact hrest.ne'), hdom',
    max_eq_left hrest.le, div_mul_cancel₀ _ hρN.ne']

end GlobalTheory.BSP.GaussMul

namespace GlobalTheory.BSP.GaussMul

theorem norm_mul_disc (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (x y : bk.DS ρ) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 hρ1
  haveI : IsUltrametricDist (Disc l (0 : Wq l bk.a) 1) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) 0 1).1
  have hm0 := (GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk).1
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ0

  have step1 : ∀ s t : bk.S, ‖toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t‖ =
      ‖toDisc l (X : bk.S) ρ s‖ * ‖toDisc l (X : bk.S) ρ t‖ := by
    intro s t
    rcases eq_or_ne (toDisc l (X : bk.S) ρ s) 0 with hu | hu
    · simp [hu]
    rcases eq_or_ne (toDisc l (X : bk.S) ρ t) 0 with hv | hv
    · simp [hv]
    have hP : 0 < ‖toDisc l (X : bk.S) ρ s‖ := norm_pos_iff.2 hu
    have hQ : 0 < ‖toDisc l (X : bk.S) ρ t‖ := norm_pos_iff.2 hv
    obtain ⟨N, hN⟩ := gauss hm0 hρ (fun n => a n (toDisc l (X : bk.S) ρ s)) (fun n => a n (toDisc l (X : bk.S) ρ t))
      hP hQ (fun n => ha2 n _) (fun n => ha2 n _)
      (exists_eq_sup hP (fun n => ha2 n _) (ha3 _) (ha4 _)) (exists_eq_sup hQ (fun n => ha2 n _) (ha3 _) (ha4 _))
    have hconv : a N (toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, a x.1 (toDisc l (X : bk.S) ρ s) * a x.2 (toDisc l (X : bk.S) ρ t) := by
      rw [← map_mul, ha1, coeff_mul, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, ha1, ha1]
    refine le_antisymm (norm_mul_le _ _) ?_
    rw [← hN, ← hconv]
    exact ha2 N _

  have hlm := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ).2.1
  have hl0 : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.2 hl.out.pos
  have hlpow : ∀ (n : ℕ) (z : bk.DS ρ), ‖z * ((l : ℕ) : bk.DS ρ) ^ n‖ = ‖z‖ / (l : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, ← mul_assoc, mul_comm _ ((l : ℕ) : bk.DS ρ), hlm, ih, pow_succ, div_div]
  have hpre : ∀ p : PreDisc l (X : bk.S) ρ, ∃ (n : ℕ) (s : bk.S),
      ofPre l (X : bk.S) ρ p * ((l : ℕ) : bk.DS ρ) ^ n = toDisc l (X : bk.S) ρ s := by
    intro p
    obtain ⟨n, s, h⟩ := IsLocalization.Away.surj ((l : ℕ) : bk.S) p
    refine ⟨n, s, ?_⟩
    have h' := congrArg (ofPre l (X : bk.S) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at h'
    exact h'
  have step2 : ∀ p q : PreDisc l (X : bk.S) ρ, ‖ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q‖ =
      ‖ofPre l (X : bk.S) ρ p‖ * ‖ofPre l (X : bk.S) ρ q‖ := by
    intro p q
    obtain ⟨n, s, hs⟩ := hpre p
    obtain ⟨m, t, ht⟩ := hpre q
    have e : ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q * ((l : ℕ) : bk.DS ρ) ^ (n + m) =
        toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t := by
      rw [← hs, ← ht, pow_add]; ring
    have h1 := hlpow (n + m) (ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q)
    rw [e, step1, ← hs, ← ht, hlpow, hlpow, pow_add, div_mul_div_comm] at h1
    exact ((div_left_inj' (by positivity)).1 h1).symm
  exact (denseRange_ofPre l (X : bk.S) ρ).induction_on₂ (p := fun x y : bk.DS ρ => ‖x * y‖ = ‖x‖ * ‖y‖)
    (isClosed_eq (continuous_norm.comp (continuous_fst.mul continuous_snd))
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd))) step2 x y

theorem norm_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ :=
  fun l _ K bk ρ h0 h1 x y => norm_mul_disc l K bk ρ h0 h1 x y

end GlobalTheory.BSP.GaussMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bk_ev_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  intro a a' h
  have h1 : tb.c tb.i₀ 1 = 1 := by simpa [tb.b_i₀] using tb.c_self tb.i₀
  have key : ∀ x, tb.c tb.i₀ (bk.ev x) = x := fun x => by
    have := tb.c_mul tb.i₀ x (tb.b tb.i₀)
    rw [tb.b_i₀, mul_one, h1, mul_one] at this
    exact this
  rw [← key a, ← key a', h]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  first | (exact @GlobalTheory.BKLim.CrLimit.isCr_of_link) | (exact GlobalTheory.BKLim.CrLimit.isCr_of_link) | (intros; apply GlobalTheory.BKLim.CrLimit.isCr_of_link  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  first | (exact @GlobalTheory.BKLim.BetaDiv.isBeta_div) | (exact GlobalTheory.BKLim.BetaDiv.isBeta_div) | (intros; apply GlobalTheory.BKLim.BetaDiv.isBeta_div  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismGaloisLiftIsPrismHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PrismTwist

variable {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : GlobalTheory.BKReal.PiSys l e)

theorem ev_injective : Function.Injective (ϖ.ev a) := by
  let Q := OCb l ⧸ Ideal.span {ϖ.flat}
  have hn : ¬ IsUnit ϖ.flat := fun h => ϖ.not_isUnit_teich (h.map (WittVector.teichmuller l))
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : CharP Q l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk _), CharP.cast_eq_zero, map_zero])
  let r : Ainf l →+* WittVector l Q := WittVector.map (Ideal.Quotient.mk _)
  have hr : Function.Injective (r.comp (wA l a).toRingHom) := fun x y h => WittVector.ext fun n =>
    ((Ideal.Quotient.mk (Ideal.span {ϖ.flat})).comp (Fq.val l a)).injective
      (congrArg (WittVector.coeff · n) h)
  have hR : r ϖ.teich = 0 := by
    change WittVector.map (Ideal.Quotient.mk _) (WittVector.teichmuller l ϖ.flat) = 0
    rw [WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _),
      WittVector.teichmuller_zero]
  have ht : ϖ.teich ≠ 0 := fun h => by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simp only [PiSys.teich, WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] at this
    exact ϖ.flat_ne_zero this
  have key : ∀ n (x : (Wq l a)⟦X⟧), ϖ.ev a x = 0 → coeff n x = 0 := by
    have h0 : ∀ x : (Wq l a)⟦X⟧, ϖ.ev a x = 0 → constantCoeff x = 0 := fun x hx => by
      rw [x.eq_X_mul_shift_add_const, map_add, map_mul, PiSys.ev_X, PiSys.ev_C] at hx
      have h1 := congrArg r hx
      rw [map_add, map_mul, hR, zero_mul, zero_add, map_zero] at h1
      exact hr (h1.trans (map_zero _).symm)
    intro n
    induction n with
    | zero => exact fun x hx => by simpa using h0 x hx
    | succ n ih =>
      intro x hx
      have h1 := h0 x hx
      rw [x.eq_X_mul_shift_add_const, h1, map_zero, add_zero, map_mul, PiSys.ev_X] at hx
      have h2 := ih _ ((mul_eq_zero.1 hx).resolve_left ht)
      rw [coeff_mk] at h2
      exact h2
  refine (injective_iff_map_eq_zero _).2 fun x hx => PowerSeries.ext fun n => ?_
  rw [key n x hx, map_zero]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff, WittVector.map_coeff, GlobalTheory.RingIface.sigA_coeff,
    frobenius_def, frobenius_def, map_pow]

end GlobalTheory.BKGal.PrismTwist

theorem GlobalTheory.BKGal.PrismTwist.hom_restrict : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  intro l _ a e _ _ ϖ g σ hσ ψ hψ
  have hfrob : ∀ x, ψ (frobS l a x) = frobS l a (ψ x) := fun x =>
    GlobalTheory.BKGal.PrismTwist.ev_injective a ϖ (by
      rw [hψ, PiSys.ev_frobS, PiSys.ev_frobS, hψ, GlobalTheory.BKGal.PrismTwist.σA_frobenius])
  refine ⟨{ f := ψ
            f_δ := (deltaS l a).map_δ_of_map_φ (deltaS l a)
              (fun x hx => (mul_eq_zero.1 hx).resolve_left (l_ne_zero l a)) ψ hfrob
            f_I := fun (x : (Wq l a)⟦X⟧) hx => ?_
            f_str := fun r (x : (Wq l a)⟦X⟧) h => ?_ }, fun _ => rfl⟩
  · have hx' := Ideal.mem_span_singleton.1 hx
    refine Ideal.mem_span_singleton.2 ((ϖ.theta_ev_eq_zero_iff a (ψ x)).1 ?_)
    rw [hψ, GlobalTheory.RingBasics.θ_σA, (ϖ.theta_ev_eq_zero_iff a x).2 hx', map_zero]
  · apply ϖ.quotToOC_injective a
    change ϖ.quotToOC a (Ideal.Quotient.mk _ (ψ x)) = ϖ.quotToOC a (ϖ.strMap a (σ r))
    have h' : Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r := h
    rw [PiSys.quotToOC_mk, PiSys.quotToOC_strMap, hψ, GlobalTheory.RingBasics.θ_σA, ← PiSys.quotToOC_mk, h',
      PiSys.quotToOC_strMap]
    refine Subtype.ext ?_
    rw [GlobalTheory.RingIface.sigO_coe]
    change Per.σC g (((r : ↥(ϖ.field a).1) : Om l) : ℂ_[l]) = (((σ r : ↥(ϖ.field a).1) : Om l) : ℂ_[l])
    rw [hσ]
    exact GlobalTheory.RingBasics.σC_coe g _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_wild_jumpSum_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent <;> assumption)
end

