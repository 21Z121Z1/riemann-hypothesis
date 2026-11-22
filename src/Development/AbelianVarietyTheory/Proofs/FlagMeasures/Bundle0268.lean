import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariant
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariantStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (A : LocS W), GoodW D τ w w' θ W → 0 < Tr D w → 0 < Tr D w' → IsSPsiEquiv W.z (psiS D W.z) W.π A.Φ → IsSPsiEquiv W.z' (psiS D W.z') W.π' A.Φ' → ContinuousOn A.Φ (UH (Hpk D.R.k D.R.rS)) → ContinuousOn A.Φ' (UH (Hpk D.R.k D.R.rS)) → ∀ (γ a a' : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (ν ν' : Measure (Mt D.R.k D.R.rS)), RelPt D W.z W.z' γ p → a ∈ Sset D.R.k D.R.rS W.z → a' ∈ Sset D.R.k D.R.rS W.z' → RMeas D W γ 1 ν → RMeas D W (a * γ * a'⁻¹) 1 ν' → hsNormSq (A.J ν' (a * γ * a'⁻¹)) = hsNormSq (A.J ν γ) := by
  first | exact @GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | exact GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | (intros; apply GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqIintLeLiminfStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsNormSq_Iint_le_liminf_alt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ Om Om' : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → IsFolner (Sset k r z') μS' Om' → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ)) ≤ Filter.liminf (fun j => (∫⁻ p, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of (act2 γ p)))) ∂(μS.prod μS')) / (μS (Om j) * μS' (Om' j))) Filter.atTop := by
  first | exact @GlobalTheory.SgInf.FolnerLower.hsNormSq_Iint_le_liminf | exact GlobalTheory.SgInf.FolnerLower.hsNormSq_Iint_le_liminf | (intros; apply GlobalTheory.SgInf.FolnerLower.hsNormSq_Iint_le_liminf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypotheses_of_global_rows_and_nodes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Glob0 D x eps CD Cg → Nodes D x eps → (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) → StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  first | exact @GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | exact GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | (intros; apply GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEqEllStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iint_eq_ell_alt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∀ γ ∈ Greg k r z z', Integrable (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG ∧ ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ = (⟪l w₀, ξ⟫_ℂ * ⟪ξ', l' w₀'⟫_ℂ * (d : ℂ)) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
  first | exact @GlobalTheory.SgInf.EllName.iint_eq_ell | exact GlobalTheory.SgInf.EllName.iint_eq_ell | (intros; apply GlobalTheory.SgInf.EllName.iint_eq_ell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishes
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma eq_zero_of_sum_star_mul_const_mul_eq_zero {n : ℕ} (x : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : ∑ i, star (x i) * (c * x i) = 0) : x = 0 := by
  have h1 : c * ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) = 0 := by
    rw [← h, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Complex.normSq (x i) : ℂ) = star (x i) * x i := Complex.normSq_eq_conj_mul_self
    rw [e]; ring
  have h2 : ∑ i, Complex.normSq (x i) = 0 := by
    have h3 := (mul_eq_zero.mp h1).resolve_left hc
    exact_mod_cast h3
  funext i
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp h2 i
    (Finset.mem_univ i)
  simpa using h4

theorem one_le_rkR_of_isIsoC {n : ℕ} {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} (hW : IsIsoC ε W) :
    1 ≤ rkR ε := by
  unfold IsIsoC herm Jm at hW
  obtain ⟨hne, hiso⟩ := hW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq := hiso x hxW x hxW

  have hall : ∀ b : Bool, ∃ i, ε i = b := by
    intro b
    by_contra hno
    push_neg at hno
    have hb : ∀ i, ε i = !b := fun i => by
      have h' := hno i
      cases hε : ε i <;> cases b <;> simp_all
    apply hx0
    apply eq_zero_of_sum_star_mul_const_mul_eq_zero x (if (!b) = true then (1 : ℂ) else -1) (by split_ifs <;> norm_num)
    rw [← hq]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hb]
  obtain ⟨i, hi⟩ := hall true
  obtain ⟨j, hj⟩ := hall false
  unfold rkR
  apply le_min
  · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem decE_le_exp {q : ℕ} (hq : 1 ≤ q) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    decE q h t ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * t)) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  unfold decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt q := ⟨_, rfl⟩
  rw [← hsd] at hs hs1 ⊢
  have hs0 : s ≠ 0 := hs.ne'

  have key : t / s - min (2 * t ^ 2) (t / s) ≤ 1 := by
    rcases le_total (2 * t ^ 2) (t / s) with h' | h'
    · rw [min_eq_left h']
      obtain ⟨u, hu⟩ : ∃ u, u = t / s := ⟨_, rfl⟩
      rw [← hu]
      have ht : t = u * s := by rw [hu]; field_simp
      have h2 : t ^ 2 = u ^ 2 * s ^ 2 := by rw [ht]; ring
      have h1 : 0 ≤ u ^ 2 * (s ^ 2 - 1) := mul_nonneg (sq_nonneg u) (by nlinarith)
      nlinarith [sq_nonneg (u - 1 / 4)]
    · rw [min_eq_right h']; norm_num
  have e : h / (8 * s) * t = h / 8 * (t / s) := by ring
  rw [e]
  nlinarith [mul_nonneg hh (sub_nonneg.mpr key)]

theorem rate_lt {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) {h : ℝ}
    (hh : 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    0 ≤ h ∧ 12 * (n : ℝ) * q < h / (8 * Real.sqrt q) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow] at hh
  have hP : 0 < (n : ℝ) * q * Real.sqrt q := by positivity
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

private lemma list_prod_eq_take_mul_pair_mul_drop {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ) (v : ι) :
    ∏ u, F u = F v * ∏ u ∈ Finset.univ.erase v, F u :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ v)).symm

private lemma rkR_le' {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  unfold rkR
  calc min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card
      ≤ (Finset.univ.filter fun a => ε a = true).card := min_le_left _ _
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem integral_phe_eq_zero : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  classical
  intro hS B d h hD hL hh v Wv hW ν hν x y
  obtain ⟨hHC, hDS, hLow, hFd⟩ := hD v
  have hDS' := hDS
  obtain ⟨_, _, hU, _⟩ := hDS'
  obtain ⟨hw1, hwS⟩ := hLow
  have hq1 : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn1 : 1 ≤ B.I.n := le_trans hq1 (rkR_le' _)
  obtain ⟨h0, hc⟩ := rate_lt hn1 hq1 (hh v)

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU
    (hS B.I.n (B.I.ε v) (B.lam v) hHC (B.H v) (B.σ v) hDS).1

  have hT := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v) : ℝ))) α (B.w v) hU hFd hc hw1 hαs hαc
    (fun u => hαfix (B.w v) hwS u)
    ⟨Real.exp (h / 8), fun g => (hL v g).trans (decE_le_exp hq1 h0 _)⟩ (x.1 v) (y.1 v)
  have hstar : ∫ m, star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν = 0 := by
    refine (integral_conj (μ := ν)
      (f := fun m => ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ)).trans ?_
    rw [hT]; simp

  have hfun : ∀ m : UJ (B.I.ε v),
      phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
        ((((∏ u, d u : ℝ) : ℂ) * star (∏ u ∈ Finset.univ.erase v,
          ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ)) * B.e (x.2 * y.2)) *
        star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    have hrest : ∏ u ∈ Finset.univ.erase v,
        ⟪B.w u, B.σ u (uMat (x.1 u * (open Classical in (Pi.mulSingle v m : B.I.Ginf)) u * y.1 u)) (B.w u)⟫_ℂ =
        ∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ :=
      Finset.prod_congr rfl fun u hu => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]
    simp only [GlobalTheory.Count.phe, GlobalTheory.Count.ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [list_prod_eq_take_mul_pair_mul_drop _ v, hrest, Pi.mulSingle_eq_same, star_mul']
    ring
  refine (integral_congr_ae (ae_of_all ν hfun)).trans ?_
  rw [integral_const_mul, hstar, mul_zero]

end GlobalTheory.RealFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianNormFibreDilationStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hermitianNormFibre_dilation : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib → β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ → ∫⁻ y, φ y ∂(fib (t * β)) = ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  first | exact @GlobalTheory.FibreScaling.lintegral_fibre_scale | exact GlobalTheory.FibreScaling.lintegral_fibre_scale | (intros; apply GlobalTheory.FibreScaling.lintegral_fibre_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHermitianDualQuotientCyclicSplitPlace
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.CyclicQuot

theorem match_of_coprime {A K ι : Type} [CommRing A] [CommRing K] (p : A →+* K) (H : AddSubgroup (ι → A))
    (T k : ℤ) (hc : IsCoprime k T) (y z : ι → A) (hy : T • y ∈ H) (hz : z ∈ H)
    (h : ∀ b, p (z b) = (k : K) * p (y b)) : ∃ z' ∈ H, ∀ b, p (z' b) = p (y b) := by
  obtain ⟨u, w, huw⟩ := hc
  refine ⟨u • z + w • (T • y), H.add_mem (H.zsmul_mem hz u) (H.zsmul_mem hy w), fun b => ?_⟩
  have h' : (u : K) * k + w * T = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huw
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_zsmul, h b]
  simp only [zsmul_eq_mul]
  linear_combination (p (y b)) * h'

theorem coprime_sub {T : ℕ} (hT : T.Prime) (i j : Fin T) (hij : i ≠ j) :
    IsCoprime (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) (T : ℤ) := by
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  refine (hp.irreducible.coprime_iff_not_dvd.mpr fun hd => hij ?_).symm
  have hi := i.2
  have hj := j.2
  have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  exact Fin.ext (by omega)

theorem cyclic_of_components {A K ι : Type} [CommRing A] [CommRing K] (sp : A ≃+* K × K) (O : Subring A)
    (e : A) (he : e ∈ O) (hsp : sp e = (1, 0)) (M D : Submodule O (ι → A)) (T : ℕ) (hT : T.Prime)
    (hTD : ∀ y ∈ D, (T : ℤ) • y ∈ M)
    (y₁ : ι → A) (hy₁ : y₁ ∈ D) (h₁ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).1 = (sp (y₁ b)).1)
    (y₂ : ι → A) (hy₂ : y₂ ∈ D) (h₂ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).2 = (sp (y₂ b)).2)
    (hidx : M.toAddSubgroup.relIndex D.toAddSubgroup = T ^ 2) :
    ∃ d ∈ D, ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ M := by
  classical
  let eO : O := ⟨e, he⟩
  let d : ι → A := eO • y₁ + (1 - eO) • y₂
  have hd : d ∈ D := D.add_mem (D.smul_mem _ hy₁) (D.smul_mem _ hy₂)
  have hdb : ∀ b, sp (d b) = ((sp (y₁ b)).1, (sp (y₂ b)).2) := by
    intro b
    have : d b = e * y₁ b + (1 - e) * y₂ b := rfl
    rw [this, map_add, map_mul, map_mul, map_sub, map_one, hsp]
    ext <;> simp
  let a : Fin T × Fin T → O := fun ij => ((ij.1 : ℕ) : O) * eO + ((ij.2 : ℕ) : O) * (1 - eO)
  have ha : ∀ ij, sp (a ij : A) = (((ij.1 : ℕ) : K), ((ij.2 : ℕ) : K)) := by
    intro ij
    have : (a ij : A) = ((ij.1 : ℕ) : A) * e + ((ij.2 : ℕ) : A) * (1 - e) := by
      simp [a, eO]
    rw [this, map_add, map_mul, map_mul, map_sub, map_one, hsp, map_natCast, map_natCast]
    ext <;> simp
  let φ : Fin T × Fin T → D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup :=
    fun ij => QuotientAddGroup.mk ⟨a ij • d, D.smul_mem _ hd⟩
  have hcard : Nat.card (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) = T ^ 2 := hidx
  have hfin : Finite (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hT.ne_zero)
  have hinj : Function.Injective φ := by
    intro s t hst
    have hm : -(a s • d) + a t • d ∈ M := QuotientAddGroup.eq.mp hst
    have hc : ∀ b, sp ((-(a s • d) + a t • d) b) =
        ((((t.1 : ℕ) : K) - ((s.1 : ℕ) : K)) * (sp (y₁ b)).1,
          (((t.2 : ℕ) : K) - ((s.2 : ℕ) : K)) * (sp (y₂ b)).2) := by
      intro b
      have : (-(a s • d) + a t • d) b = -((a s : A) * d b) + (a t : A) * d b := rfl
      rw [this, map_add, map_neg, map_mul, map_mul, ha, ha, hdb]
      ext <;> simp <;> ring
    by_contra hne
    by_cases h1 : t.1 = s.1
    · have h2 : t.2 ≠ s.2 := fun h2 => hne (Prod.ext h1.symm h2.symm)
      refine h₂ (match_of_coprime ((RingHom.snd K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h2) y₂ _ (hTD _ hy₂) hm fun b => ?_)
      have := congrArg Prod.snd (hc b)
      push_cast
      exact this
    · refine h₁ (match_of_coprime ((RingHom.fst K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h1) y₁ _ (hTD _ hy₁) hm fun b => ?_)
      have := congrArg Prod.fst (hc b)
      push_cast
      exact this
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcard]; simp [sq])
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨s, hs⟩ := hbij.2 (QuotientAddGroup.mk ⟨x, hx⟩)
  have hm : -(a s • d) + x ∈ M := QuotientAddGroup.eq.mp hs
  refine ⟨a s, (a s).2, ?_⟩
  rw [sub_eq_neg_add]
  exact hm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem [StarRing E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ e ∈ intV E v, sp e = (1, 0) := by
  have hH : IsHerm (cm.sig : E →+* E) (1 : Matrix (Fin 1) (Fin 1) E) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [cT]
  let L : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hL : ∀ x ∈ L, ∀ b, x b ∈ intOE E := by
    intro x hx b
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨c, by simp [Algebra.smul_def]⟩
  have hloc : ∀ y ∈ loc v L, ∀ b, y b ∈ intV E v := by
    intro y hy b
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact Subring.subset_closure (Or.inl ⟨⟨x b, hL x hx b⟩, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem c.2 hx
  have hone : (fun _ => 1 : Fin 1 → E ⊗[F] v.adicCompletion F) ∈ loc v L :=
    Submodule.subset_span ⟨fun _ => 1, Submodule.subset_span rfl, by funext i; simp⟩
  have hmem := ((GlobalTheory.T.split_place_lattice_components F E cm 1 1 hH (by simp) v sp h1 h2).1 L (fun _ => sp.symm (1, 0))).mpr
    ⟨⟨_, hone, fun b => by simp⟩, ⟨0, zero_mem _, fun b => by simp⟩⟩
  exact ⟨sp.symm (1, 0), hloc _ hmem 0, by simp⟩

theorem smul_mem_loc {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) : ∀ y ∈ loc v (dualL σ J L), (T : ℤ) • y ∈ loc v L := by
  have h0 : ∀ x ∈ dualL σ J L, (T : ℤ) • x ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have := h x hx
      rwa [Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact L.smul_mem c hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h0 x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_zsmul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem local_dual_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 → ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL v hv sp h1 h2 hiff hidx
  obtain ⟨e, he, hsp⟩ := exists_idem cm v sp h1 h2
  obtain ⟨x, hx, hxn⟩ := hL.2.2.2.2 v hv
  have crit := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v sp h1 h2).1 L x
  have n1 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1 :=
    fun h => hxn (crit.mpr ⟨h x hx, hiff.mp h x hx⟩)
  have n2 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2 :=
    fun h => n1 (hiff.mpr h)
  obtain ⟨y₁, hy₁⟩ := not_forall.mp n1
  obtain ⟨y₂, hy₂⟩ := not_forall.mp n2
  obtain ⟨hy₁, h₁⟩ := Classical.not_imp.mp hy₁
  obtain ⟨hy₂, h₂⟩ := Classical.not_imp.mp hy₂
  exact cyclic_of_components sp (intV E v) e he hsp _ _ T hT
    (smul_mem_loc cm.sig J T L hL.2.2.1 v) y₁ hy₁ h₁ y₂ hy₂ h₂ hidx

end GlobalTheory.St.G.CyclicQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotient
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem phiIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun y : Mt k r => coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) μG ∧
    ∫ y, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ ∂μG =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  haveI : SigmaFinite μG := hHaarG.1
  haveI : SigmaFinite μS := hHaarS.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hF := GlobalTheory.T.integrable_bessel_fubini_integrand_prod k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have haeG : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hHaarG.2.2.1
  have haeS : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaarS.2.2.1
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS :=
    haeG.mono fun y hy => GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  refine ⟨hF.integral_prod_left.congr (hae.mono fun y hy => hy.symm), ?_⟩
  rw [integral_congr_ae hae, integral_integral_swap hF]
  have hin : ∀ᵐ t ∂μS, (∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μG) =
      (⟪u₁, u⟫_ℂ / (d : ℂ)) * (⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ) := by
    filter_upwards [haeS] with t ht
    rw [integral_mul_const, GlobalTheory.T.besselSchur_translated_matrixCoefficient k r σ w a μG d hStd u u₁ v _ (hcl.2.2.2.1.1 ht)]
    ring
  rw [integral_congr_ae hin, integral_const_mul, GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm k r σ w a μG d z c π μS hStd hSide v hv ξ]
  ring

theorem innerIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν →
    ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun x : Mt k r => ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ) ν ∧
    ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hUnS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hSide.1 hSide.2.1 μS).1 hHaarS
  obtain ⟨-, hνG, -, hWeil, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHaarG hHaarS hUnS hν
  obtain ⟨hφ, hφint⟩ := phiIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  obtain ⟨hWi, hWe⟩ := hWeil ℂ _ hφ
  have haeν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := ae_iff.2 hνG
  have hae : ∀ᵐ x ∂ν, (∫ s, (fun y : Mt k r => coef σ u v (Matrix.of y) *
        ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) (lmulM (Matrix.of s) x) ∂μS) =
      ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ :=
    haeν.mono fun x hx => (GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx).symm
  refine ⟨hWi.congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← hWe, hφint]

theorem normIdentity_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) ∧ Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν ∧ MemLp (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) 2 ν ∧ ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν = ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) ∧ 0 ≤ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).re ∧ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).im = 0 := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hwD : w ∈ DD σ w := by
    have h1 := mem_DD σ w hcl.1.2.2.1
    rwa [hStd.2.1.1.1, ContinuousLinearMap.one_apply] at h1
  have hAi := GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure k r σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  obtain ⟨hIi, -⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  have hIe := (innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ).2
  have hsq : Integrable (fun x : Mt k r => ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ ^ 2) ν := by
    refine hIi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    exact inner_self_eq_norm_sq _
  obtain ⟨-, hwe⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν w hwD w hwD v hv ξ
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hL : (∫ x, ⟪Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)⟫_ℂ ∂ν)
      = ((∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [hL, hww, one_mul] at hwe
  have hX : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ =
      ((d * ∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [eq_div_iff hd'] at hwe
    rw [← hwe]; push_cast; ring
  refine ⟨GlobalTheory.T.besselFunctional_equivariant_unipotent_character k r σ w a μG d z c π μS hStd hSide u hu v hv ξ, hAi,
    (memLp_two_iff_integrable_sq_norm hAi.aestronglyMeasurable).2 hsq, hIe, ?_, ?_⟩
  · rw [hX, Complex.ofReal_re]
    exact mul_nonneg hd.le (integral_nonneg fun x => by positivity)
  · rw [hX, Complex.ofReal_im]

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPowLeCardFlagQuotientStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_le_card_flag_quotient : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  first | exact @GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ | exact GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ | (intros; apply GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PolarSqCompareStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polar_tanSq_ptSq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  first | exact @GlobalTheory.PolarCompare.polar_sq_compare | exact GlobalTheory.PolarCompare.polar_sq_compare | (intros; apply GlobalTheory.PolarCompare.polar_sq_compare <;> assumption)
end

