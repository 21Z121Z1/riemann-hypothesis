import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
import GroundTheory.PAdicHodge.AInfGalois
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem formalDegreeUpperC_of_hypotheses : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  intro hp D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  obtain ⟨hcore, -, hσ, -⟩ := hL
  have h5 : GlobalTheory.Core5 R F := ⟨hcore.lev, hcore.grp, hcore.fam, hcore.models, hcore.thP⟩
  intro Fr hFr ρ mR hmR e he
  dsimp only
  obtain ⟨hanti, hhalf, hwid⟩ := GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width R F h5 i σ s hσ ρ
  have hsig : ∀ ρ', ((Wc D i).sig (tauE D ρ')).1 + ((Wc D i).sig (tauE D ρ')).2 = (Wc D i).rank :=
    fun ρ' => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ').2.2.1
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have h1 : 1 ≤ (Wc D i).rank := by
    rw [hrk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]; omega
  have h3 : 3 ≤ D.R.nV := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m; have := D.R.three_m_lt_t
    simp only [Formalism.BasicNotions.Ranks.nV, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨hint, hinv⟩ := GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual hp D.cd (Wc D i) _ (R.MW i σ) Fr hFr hsig ρ hanti hhalf _ he
  have hm := GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual D.cd _ _ mR hmR
  rw [hsig ρ] at hm
  obtain ⟨hvol, hQpos, hlog⟩ := GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound (Wc D i).rank D.R.nV (degAt D i σ ρ) ((R.MW i σ).lam ρ) h1 h3
    (by positivity) hanti hwid
  have e1 : (((Wc D i).rank : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  rw [e1] at hlog
  subst hm
  refine ⟨hint.smul_measure ENNReal.ofReal_ne_top, ?_, ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul]
    refine mul_pos hvol ?_
    have : 0 < (∫ b : Upq (Wc D i) ρ, ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(D.cd.cd _ _))⁻¹ := by
      rw [hinv]; exact hQpos
    exact inv_pos.mp this
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul, mul_inv, hinv, mul_comm, ← div_eq_mul_inv]
    exact hlog

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPolyOfRecTwist
section
open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem frobPoly_of_rec_twist : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) {l : ℕ} [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ) {m : ℕ} {r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)}, Continuous r → ∀ {rc : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h}, GlobalTheory.LocLanglands.IsRec h rc → ∀ {σ : GlobalTheory.SmGL.IrrRep (GL (Fin m) (w.adicCompletion E))} {α : Fin m → ℂˣ}, GlobalTheory.SmGL.HasSatake σ.ρ α → GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (m : ℝ)) / 2) → ∀ {g : Formalism.ConjugateSelfDual.G E Ω}, Formalism.ConjugateSelfDual.IsFrob (F := E) A (Formalism.ConjugateSelfDual.normV w) g → ((r g⁻¹ : GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map (ι : Formalism.ConjugateSelfDual.Qbar l →+* ℂ) = GlobalTheory.SphPar.frobPoly (Formalism.ConjugateSelfDual.normV w) m ((Finset.univ.val.map α).map fun b : ℂˣ => (b : ℂ)) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι m r hr rc hrc σ α hα hwd g hg
  have hr' : Continuous fun x => (r x : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr
  have hgW : g ∈ GlobalTheory.WeilDeligne.Weil h := GlobalTheory.WeilDeligne.mem_Weil_of_isFrob h hg
  have hd : GlobalTheory.WeilDeligne.deg (⟨g, hgW⟩ : GlobalTheory.WeilDeligne.Weil h) = 1 :=
    GlobalTheory.WeilDeligne.deg_eq_one_iff.mpr hg
  have e1 := GlobalTheory.WeilDeligne.charPol_wdOf hl ι hr' (⟨g, hgW⟩ : GlobalTheory.WeilDeligne.Weil h)⁻¹
  rw [hwd, GlobalTheory.CuspRep.ParLaws.rec_eq_diag hrc hα, GlobalTheory.WeilDeligne.WD.lpTw_mk,
    GlobalTheory.WeilDeligne.WD.charPol_mk, GlobalTheory.WeilDeligne.WDRep.tw_ρ,
    GlobalTheory.WeilDeligne.WDRep.diag_ρ, GlobalTheory.WeilDeligne.deg_inv, hd] at e1
  have e2 : ∀ (a : ℂ) (d : Fin m → ℂ), a • GlobalTheory.WeilDeligne.diagEnd d =
      GlobalTheory.WeilDeligne.diagEnd fun i => a * d i := fun a d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [e2, GlobalTheory.WeilDeligne.charpoly_diagEnd] at e1
  change ((r ((⟨g, hgW⟩ : GlobalTheory.WeilDeligne.Weil h)⁻¹ : GlobalTheory.WeilDeligne.Weil h) :
    GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map
      ι.toRingHom = _
  rw [← e1, GlobalTheory.SphPar.frobPoly, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 2
  rw [zpow_neg_one, zpow_neg_one, Units.val_inv_eq_inv_val, inv_inv, mul_comm, ← Complex.cpow_neg,
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  congr 2
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_complexHessian_fubiniStudy_potential : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  first | exact @GlobalTheory.FSDet.det_fubiniStudy_hess | exact GlobalTheory.FSDet.det_fubiniStudy_hess | (intros; apply GlobalTheory.FSDet.det_fubiniStudy_hess <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsCentralCharacter
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandOfCapelli

open Finset Polynomial
open GlobalTheory.Dec (gelfVal)

theorem main_succ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (F : Fin (m+1) → Fin (m+1) → A)
    (χ : Fin (m+1) → ℂ) (hF : GlRel F)
    (hq : ∀ w : ℂ, qdet F w = algebraMap ℂ A ((GlobalTheory.CapelliNewton.capQ m χ).eval w)) (N : ℕ) :
    etr F N = algebraMap ℂ A (gelfVal χ N) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  set Q := GlobalTheory.CapelliNewton.capQ m χ with hQ
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
      qminor F (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m F (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow F (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
      qminor F (Fin.succAbove j) (Fin.succAbove i) w * epow F (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  let Rp : ℂ[X] := ∑ d ∈ range (m + 1), C (φ (Rc d)) * X ^ d
  have hRp : ∀ w : ℂ, φ (∑ d ∈ range (m + 1), w ^ d • Rc d) = Rp.eval w := by
    intro w
    simp only [Rp, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul, smul_eq_mul]
    exact sum_congr rfl fun d _ => mul_comm _ _
  have hRpdeg : Rp.natDegree ≤ m := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hφa : ∀ c : ℂ, φ (algebraMap ℂ A c) = c * φ 1 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (Q.eval (w + 1) - Q.eval w) * φ 1 + (-1) ^ N * Rp.eval w
      = Q.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k) := by
    intro w
    have h1 := congrArg φ (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m F hF w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    simp only [hq, ← Algebra.smul_def, map_add, map_smul, smul_eq_mul, hRp] at h1
    simp only [mul_sum, map_sum, map_smul, map_sub, smul_eq_mul, hφa] at h1
    rw [mul_sum]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  let S : ℂ[X] := ∑ k ∈ range (N + 1),
    C ((-1) ^ k * (φ (etr F k) - gelfVal χ k * φ 1)) * (X - C (m : ℂ)) ^ (N - k)
  have hSe : ∀ w : ℂ, S.eval w = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k))
      - φ 1 * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k := by
    intro w
    simp only [S, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hQS : Q * S = C ((-1) ^ N) * Rp + C (φ 1) * rs := by
    refine Polynomial.funext fun w => ?_
    have h2 := hrsE w
    rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (w + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ w, ← hQ] at h2
    simp only [eval_mul, eval_add, eval_C, hSe]
    linear_combination -hrec w + φ 1 * h2
  have hS0 : S = 0 := by
    by_contra hne
    have hd := (GlobalTheory.CapelliNewton.capQ_monic m χ).natDegree_mul' hne
    rw [← hQ, hQS, GlobalTheory.CapelliNewton.capQ_natDegree] at hd
    have hle : (C ((-1 : ℂ) ^ N) * Rp + C (φ 1) * rs).natDegree ≤ m :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hRpdeg)
        ((natDegree_C_mul_le _ _).trans hrs))
    omega
  have h0 := congrArg (eval (m : ℂ)) hS0
  simp only [S, eval_zero, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self] at h0
  rw [sum_eq_single N (fun b hb hbN => by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hb)) hbN)), mul_zero])
    (fun h => absurd (self_mem_range_succ N) h)] at h0
  rw [Nat.sub_self, pow_zero, mul_one] at h0
  have hne : ((-1 : ℂ)) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [map_sub, hφa]
  exact mul_left_cancel₀ hne (by linear_combination h0)

theorem gelfand_of_capelli : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (F : Fin n → Fin n → A) (χ : Fin n → ℂ),
    GlRel F → (∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) = algebraMap ℂ A (∏ s, (u + χ s))) →
    ∀ k : ℕ, etr F (k + 1) = algebraMap ℂ A (GlobalTheory.Dec.gelfVal χ (k + 1)) := by
  intro A _ _ n F χ hF hq k
  cases n with
  | zero => simp [etr, gelfVal]
  | succ m =>
    refine main_succ A m F χ hF (fun w => ?_) (k + 1)
    calc qdet F w = qdet F ((w - (m : ℂ) / 2) + (((m + 1 : ℕ) : ℂ) - 1) / 2) := by congr 1; push_cast; ring
      _ = algebraMap ℂ A (∏ s, ((w - (m : ℂ) / 2) + χ s)) := hq _
      _ = _ := by rw [GlobalTheory.CapelliNewton.capQ_eval]

end GlobalTheory.GelfandOfCapelli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsDetermineMultiset
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandInj

open Finset Polynomial

theorem capQ_eq_prod (m : ℕ) (χ : Fin (m+1) → ℂ) :
    GlobalTheory.CapelliNewton.capQ m χ
      = (((Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a))).map (fun a => X - C a)).prod := by
  unfold GlobalTheory.CapelliNewton.capQ
  rw [Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, map_sub]
  ring

theorem capQ_roots (m : ℕ) (χ : Fin (m+1) → ℂ) :
    (GlobalTheory.CapelliNewton.capQ m χ).roots = (Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a)) := by
  rw [capQ_eq_prod, Polynomial.roots_multiset_prod_X_sub_C]

theorem gelfVal_multiset_eq : ∀ (n : ℕ) (χ χ' : Fin n → ℂ), (∀ k : ℕ, GlobalTheory.Dec.gelfVal χ (k + 1) = GlobalTheory.Dec.gelfVal χ' (k + 1)) → Multiset.map χ Finset.univ.val = Multiset.map χ' Finset.univ.val := by
  intro n χ χ' h
  cases n with
  | zero => simp
  | succ m =>
    have hall : ∀ k, GlobalTheory.Dec.gelfVal χ k = GlobalTheory.Dec.gelfVal χ' k := by
      intro k
      cases k with
      | zero => rw [GlobalTheory.CapelliNewton.gelfVal_zero, GlobalTheory.CapelliNewton.gelfVal_zero]
      | succ k => exact h k
    have hgv : GlobalTheory.Dec.gelfVal χ = GlobalTheory.Dec.gelfVal χ' := funext hall
    obtain ⟨r, hr, hrE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m (m + 1) χ
    obtain ⟨r', hr', hrE'⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m (m + 1) χ'
    have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m (m + 1) (GlobalTheory.Dec.gelfVal χ)
      (GlobalTheory.CapelliNewton.capQ m χ - GlobalTheory.CapelliNewton.capQ m χ') (r - r')
      (Nat.lt_succ_self m) (GlobalTheory.CapelliNewton.gelfVal_zero m χ) ?_ ?_ ?_
    · have hQ : GlobalTheory.CapelliNewton.capQ m χ = GlobalTheory.CapelliNewton.capQ m χ' := sub_eq_zero.mp hf
      have hroots := congrArg Polynomial.roots hQ
      rw [capQ_roots, capQ_roots] at hroots
      exact Multiset.map_injective (fun a b hab => by simpa using hab) hroots
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_sub]
      rcases Nat.lt_or_ge (m + 1) k with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt),
          coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt), sub_zero]
      · have hk' : k = m + 1 := le_antisymm hge hk
        subst hk'
        have h1 := (GlobalTheory.CapelliNewton.capQ_monic m χ).coeff_natDegree
        have h2 := (GlobalTheory.CapelliNewton.capQ_monic m χ').coeff_natDegree
        rw [GlobalTheory.CapelliNewton.capQ_natDegree] at h1 h2
        rw [h1, h2, sub_self]
    · exact (natDegree_sub_le _ _).trans (max_le hr hr')
    · intro u
      have h1 := hrE u
      have h2 := hrE' u
      rw [← hgv] at h2
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ u] at h1
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ' (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ' u] at h2
      simp only [eval_sub]
      linear_combination h1 - h2

end GlobalTheory.GelfandInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreClosedSubvarietyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_closed_subvariety : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (x : G) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = j x → ∀ (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB Y), (∀ a, (P a).IsLB) → (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a => ((P a).pull i).pull j')) = (letI := algebraΓOfHom s; interNumRed B.functionField (⟨closure {x}, isClosed_closure⟩ : Closeds _) (fun a => (P a).pull j)) := by
  first | exact @GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed | exact GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed | (intros; apply GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.GenericMember

theorem genSec_chart_ne_zero_and_isPrime : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  intro k _ N X X' _ f f' π L hL b V hne hW c hVc j hj
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  intro e he1 he2
  haveI : Nonempty V := hne.to_subtype
  set a : Fin N → Γ(X, V) := fun i => resG X hVc ((b i).f c) with ha
  set t₀ : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) :=
    ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i with ht
  obtain ⟨ht0, hI⟩ := GlobalTheory.GenericForm.span_genericForm_isPrime_or_eq_top k Γ(X, V) N a j hj t₀ rfl
  have hWU : π ⁻¹ᵁ V ≤ (L.pull π).U (fun _ => c) := fun x hx => Set.mem_iInter.2 fun _ => hVc hx
  have hsum : ∀ J, (genSec k N f' π L b).f J =
      ∑ i, resG X' le_top (genVar k N f' i) * (secPull (b i) π).f J := by
    intro J
    let F : (L.pull π).Sec →+ Γ(X', (L.pull π).U J) :=
      { toFun := fun s => s.f J, map_zero' := rfl, map_add' := fun _ _ => rfl }
    show F (∑ i, genVar k N f' i • secPull (b i) π) = _
    rw [map_sum]
    rfl
  have key : resG X' hWU ((genSec k N f' π L b).f (fun _ => c)) = e t₀ := by
    rw [hsum (fun _ => c), map_sum, ht, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hq : algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i =
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] (1 : Γ(X, V))) *
          ((1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] a i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hq, map_mul, he1, he2]
    congr 1
    · have e2 : f'.appTop ≫ X'.presheaf.map (homOfLE (le_top : (L.pull π).U (fun _ => c) ≤ ⊤)).op ≫
          X'.presheaf.map (homOfLE hWU).op = f'.appLE ⊤ (π ⁻¹ᵁ V) le_top := by
        simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv.hom
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))) e2
    · have e1 : π.appLE (L.U c) ((L.pull π).U (fun _ => c)) ((GlobalTheory.chartPullPull L π).le (fun _ => c)) ≫
          X'.presheaf.map (homOfLE hWU).op = X.presheaf.map (homOfLE hVc).op ≫ π.app V := by
        rw [Scheme.Hom.naturality]
        simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((b i).f c)) e1
  have hid : (secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ =
      Ideal.span {e t₀} := by
    rw [ideal_secIdeal (LB.isLB_pull hL π) _ ⟨π ⁻¹ᵁ V, hW⟩ (fun _ => c) hWU]
    exact congrArg (fun x => Ideal.span {x}) key
  have hmap : Ideal.span {e t₀} = Ideal.map e (Ideal.span {t₀}) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine ⟨fun h0 => ht0 (e.injective ?_), ?_⟩
  · rw [map_zero, ← key, h0, map_zero]
  · rw [hid]
    rcases hI with h | ⟨hp, hx⟩
    · left
      rw [hmap, h, Ideal.map_top]
    · right
      refine ⟨?_, ?_⟩
      · haveI := hp
        rw [hmap]
        exact Ideal.map_isPrime_of_equiv e
      · rw [eq_bot_iff]
        intro x hx'
        rw [Ideal.mem_bot]
        apply hx x
        rw [Ideal.mem_comap, ← he1, Ideal.mem_span_singleton'] at hx'
        obtain ⟨d, hd⟩ := hx'
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm d, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, hd]

end GlobalTheory.GenericMember
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem genPair_specializes_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str,
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
        (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  intro F _ Y K _ ψ₁ ψ₂ hG
  obtain ⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩ := hG
  have hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn)) :=
    fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans
      ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))
  have h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str := by
    rw [k, k, hF]
  refine ⟨h, ?_⟩
  haveI : IsDominant (spMap (algebraMap V K)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap V K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]
    exact bot_le
  have hv : v₁ ≫ Y.str = v₂ ≫ Y.str := by
    refine ext_of_isDominant (spMap (algebraMap V K)) ?_
    rw [← Category.assoc, ← Category.assoc, e₁, e₂]
    exact h
  let v := Limits.pullback.lift v₁ v₂ hv
  have hgen : spMap (algebraMap V K) ≫ v =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst]; exact e₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · simp only [v, Category.assoc, Limits.pullback.lift_snd]; exact e₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hres : spMap (IsLocalRing.residue V) ≫ v =
      (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
    · simp only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]
      exact e₃.symm
  have hsp := ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)
  rw [hgen] at hsp
  have hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
    calc v (IsLocalRing.closedPoint V) = (spMap (IsLocalRing.residue V) ≫ v) (IsLocalRing.closedPoint _) :=
          (ClosedPt.closedPt_comp v).symm
      _ = ((spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str) (IsLocalRing.closedPoint _) := by
          rw [hres]
      _ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) :=
          Scheme.Hom.comp_apply _ _ _
      _ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]
  rw [hc] at hsp
  exact hsp

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorizationStatement
section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_morphism_factorization : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (K : Type) [Field K] [Algebra Z.functionField K] [FiniteDimensional Z.functionField K] (g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ Z) [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g], g = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫ Z.fromSpecStalk (genericPoint Z) → ∃ (hη : g.fromNormalization (genericPoint g.normalization) ⤳ genericPoint Z) (ψ : K →+* g.normalization.functionField), ψ.comp (algebraMap Z.functionField K) = GlobalTheory.TrueGeo.SmallSec.fnMap g.fromNormalization hη := by
  first | exact @GlobalTheory.NormFnField.normalization_functionField | exact GlobalTheory.NormFnField.normalization_functionField | (intros; apply GlobalTheory.NormFnField.normalization_functionField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricDegree_pull_birationalModel : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧ ∀ (a t : ℝ), L.IsSelfInter a → ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  first | exact @GlobalTheory.HSNef.gdeg_pull_model | exact GlobalTheory.HSNef.gdeg_pull_model | (intros; apply GlobalTheory.HSNef.gdeg_pull_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  first | exact @GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart | exact GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart | (intros; apply GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiserStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphJets_mem_pow_sup_uniformiser : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by
  first | exact @GlobalTheory.GraphLocal.jets_mem_pow_sup | exact GlobalTheory.GraphLocal.jets_mem_pow_sup | (intros; apply GlobalTheory.GraphLocal.jets_mem_pow_sup <;> assumption)
end

