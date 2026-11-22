import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexGlMapStandardLatticeOfIntegralStatement
section
open GlobalTheory.LatHecke GlobalTheory.SatakeInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_glMap_standardLattice_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  first | exact @GlobalTheory.LatHecke.relIndex_glMap_std_of_integral | exact GlobalTheory.LatHecke.relIndex_glMap_std_of_integral | (intros; apply GlobalTheory.LatHecke.relIndex_glMap_std_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C →
    L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧
      (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  intro D L C h
  obtain ⟨hC, _, hw, hwb, -, hb⟩ := h
  obtain ⟨s, hs⟩ := D.R.t_odd
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hts : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) + 1 := by
    rw [hs]; push_cast; ring
  have hb'pos : 0 < L.sc.b' := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hfac : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb' : L.sc.b' ≤ L.sc.b := by nlinarith
  have htb : (D.R.t : ℝ) + 2 ≤ L.sc.b := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hdiv : (D.R.t + 1) / 2 = s + 1 := by omega
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hc1 := Nat.le_ceil L.sc.b
  have hc2 := Nat.ceil_lt_add_one hb0
  have hle : s + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((s + 1 : ℕ) : ℝ) ≤ ⌈L.sc.b⌉₊ := by
      have : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
      push_cast; nlinarith
    exact_mod_cast this
  have hval : (bHat L : ℝ) = (⌈L.sc.b⌉₊ : ℝ) - ((s : ℝ) + 1) := by
    unfold bHat
    rw [hdiv, Nat.cast_sub hle]
    push_cast; ring
  rw [hval, hts]
  constructor <;> linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_add_etaHat_add_sHat_le_hPage {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  have ht : 5 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hη : 0 < L.etaSz := L.etaSz_pos
  have hS : 0 < L.Sc := L.Sc_pos
  obtain ⟨hC, hw1, hw2, hwb, -, hb⟩ := h
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hb' : (100 : ℝ) ≤ L.sc.b' := hw1.trans hwb
  have hfac : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbig : 100 * L.sc.b' ≤ L.sc.b := by
    have := mul_le_mul_of_nonneg_right hfac (by linarith : (0 : ℝ) ≤ L.sc.b')
    linarith
  have htR : ((D.R.t : ℕ) : ℝ) ≤ L.sc.b := by nlinarith
  have hb0 : 0 ≤ L.sc.b := by linarith
  set c := (D.R.t + 1) / 2 with hcdef
  have hc3 : 3 ≤ c := by omega
  have hct : c ≤ D.R.t := by omega
  have htc : D.R.t ≤ ⌈L.sc.b⌉₊ := by exact_mod_cast htR.trans (Nat.le_ceil _)
  have hcle : c ≤ ⌈L.sc.b⌉₊ := hct.trans htc
  have h1 : (⌈L.sc.b⌉₊ : ℝ) < L.sc.b + 1 := Nat.ceil_lt_add_one hb0
  have h2 : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le hη.le
  have h3 : (⌊L.Sc⌋₊ : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have hc3R : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc3
  unfold bHat etaHat sHat hPage
  rw [← hcdef, Nat.cast_sub hcle]
  push_cast
  linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_param_of_thetaLift_baseChange : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.ArchimedeanSignatureMatching D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa → ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧ IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  first | exact @GlobalTheory.RowThetaParam.param_of_theta | exact GlobalTheory.RowThetaParam.param_of_theta | (intros; apply GlobalTheory.RowThetaParam.param_of_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatio
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem scale_log_mul_b'_le_b : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  intro eps C A heps hC hA
  have hK : 0 ≤ C * (A + 1) := by positivity
  have hev : ∀ᶠ t in Filter.atTop, t ^ ⌈6 / eps⌉₊ * Real.exp (-t) ≤ 1 / (C * (A + 1) + 1) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈6 / eps⌉₊).eventually
      (ge_mem_nhds (by positivity))
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max T0 1 ^ (3 / eps), fun s hse hx => ?_⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 ≤ s.x := by linarith
  have hT1 : 0 ≤ max T0 1 := le_trans zero_le_one (le_max_right _ _)
  have ht : max T0 1 ≤ s.x ^ (eps / 3) := by
    calc max T0 1 = (max T0 1 ^ (3 / eps)) ^ (eps / 3) := by
          rw [← Real.rpow_mul hT1]
          rw [show 3 / eps * (eps / 3) = 1 by field_simp, Real.rpow_one]
      _ ≤ s.x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)
  have ht1 : 1 ≤ s.x ^ (eps / 3) := le_trans (le_max_right _ _) ht
  have hxsq : s.x ^ 2 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by
    have e : s.x ^ 2 = (s.x ^ (eps / 3)) ^ (6 / eps) := by
      rw [← Real.rpow_mul hx0, show eps / 3 * (6 / eps) = ((2 : ℕ) : ℝ) by field_simp; norm_num,
        Real.rpow_natCast]
    rw [e, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil _)
  have hu := hT0 _ (le_trans (le_max_left _ _) ht)
  rw [le_div_iff₀ (by positivity)] at hu
  have hu0 : 0 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) := by positivity
  have he := Real.exp_pos (s.x ^ (eps / 3))
  have e1 : (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ =
      (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) * Real.exp (s.x ^ (eps / 3)) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hlog : A * Real.log s.x + 1 ≤ (A + 1) * s.x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < s.x)
    nlinarith
  have main : C * (A * Real.log s.x + 1) * s.x ≤ Real.exp (s.x ^ (eps / 3)) := by
    calc C * (A * Real.log s.x + 1) * s.x ≤ C * ((A + 1) * s.x) * s.x := by gcongr
      _ = C * (A + 1) * s.x ^ 2 := by ring
      _ ≤ C * (A + 1) * (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by gcongr
      _ ≤ Real.exp (s.x ^ (eps / 3)) := by
          rw [e1]
          nlinarith [mul_le_mul_of_nonneg_right hu he.le, mul_nonneg hu0 he.le]
  have hb : 0 ≤ s.b := (Real.exp_pos _).le
  have hb' : s.b' = s.x * s.b / Real.exp (s.x ^ (eps / 3)) := by
    simp only [Scale.b', Scale.a, Scale.X', hse]
  rw [hb']
  calc C * (A * Real.log s.x + 1) * (s.x * s.b / Real.exp (s.x ^ (eps / 3)))
      = C * (A * Real.log s.x + 1) * s.x / Real.exp (s.x ^ (eps / 3)) * s.b := by ring
    _ ≤ 1 * s.b := by
        gcongr
        rw [div_le_one he]
        exact main
    _ = s.b := one_mul _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem splits_of_conjugates_mem :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l),
      (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) →
      ∀ _ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        Formalism.WeaklyAdmissibleFiltrations.Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 := by
  intro l _ K LL h ft
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  refine ⟨LL.2, ?_⟩
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun σ => LL.1.val.comp σ
      invFun := fun τ => τ.codRestrict LL.1.toSubalgebra (h τ)
      left_inv := fun σ => ?_
      right_inv := fun τ => ?_ }
  · ext x; rfl
  · ext x; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScale
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem thinSize_dominates : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  intro eps _
  refine ⟨10000, fun D L P _ hx => ?_⟩
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hte := P.t_le_eta
  have h1 := P.teta
  rw [le_div_iff₀ hx0] at h1
  have hS := L.Sc_pos
  have hsq : (100 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hlog : (1 : ℝ) ≤ Real.log L.sc.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hk : (200 : ℝ) ≤ D.R.k := by
    refine le_trans ?_ P.k_ge_mx
    have a : (200 : ℝ) ≤ (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) := by nlinarith
    nlinarith
  have h2 : 200 * L.Sc ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul_of_nonneg_right hk hS.le) P.kS_le
  have h3 : 7 * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := mul_le_mul_of_nonneg_right ht (by linarith)
  have h4 : 7 * L.etaSz * 10000 ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul h3 hx (by norm_num) (by linarith)) h1
  exact ⟨by linarith, by linarith, hw1⟩

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.Ggeo

theorem bT_add_div_le_three_halves : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x →
    ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  intro D L P hx t
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Formalism.BasicNotions.Scale.b' Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.X'
    positivity
  have hbT := P.bT_le t
  have hrho := P.rho_le
  unfold Formalism.BasicNotions.LevelStarExponents.rhoP at hrho
  have hLaG : 0 < L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    by_contra hneg
    have hneg' : L.LaG ≤ 0 := le_of_not_gt hneg
    have h3 : L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg' hb'.le) (Nat.cast_nonneg _)
    linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) := by
    have := P.Crho_pos
    positivity
  set T := Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hT
  have hT4 : 4 * T ≤ L.sc.x ^ (-2 : ℝ) := by
    have h4 : 4 * Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * T := by
      rw [hT]
      ring
    linarith
  have hbT' : (L.bT t : ℝ) ≤ L.sc.b' + T * L.sc.b' := by
    have h5 : Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = T * L.sc.b' := by
      rw [hT]
      ring
    linarith
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 16 := by
    calc L.sc.x ^ (-2 : ℝ) = (L.sc.x ^ 2)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_two]
      _ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
      _ = 1 / 16 := by norm_num
  have hTb : T * L.sc.b' ≤ L.sc.b' / 64 := by
    have h6 : T ≤ 1 / 64 := by linarith
    nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  linarith

end GlobalTheory.Ggeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindows
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem jT1_mem_window_of_bounded_v : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ),
    (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) →
    (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s,
    (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ)
      else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨
    |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  intro R P j s S η hv hb u hu
  obtain ⟨c, hc⟩ := R.t_odd
  have ht1 : ((R.t : ℤ) - 1) / 2 = c := by rw [hc]; push_cast; omega
  have ht2 : ((R.t : ℤ) + 1) / 2 = c + 1 := by rw [hc]; push_cast; omega
  have htc : (R.t : ℤ) = 2 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨E, hE⟩ := P.e_int j
  have hEf : ⌊P.e j⌋ = E := by rw [hE]; simp
  have hV : ∀ i, 0 ≤ ⌊P.v i⌋ ∧ ⌊P.v i⌋ ≤ ((⌊S⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨V, hVi⟩ := P.v_int i
    obtain ⟨h0, h1⟩ := hv i
    rw [hVi] at h0 h1 ⊢
    simp only [Int.floor_intCast]
    push_cast at h0 h1
    have h0' : (0:ℤ) ≤ V := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    have h2 : ((V.toNat : ℕ) : ℝ) ≤ S := by
      have : ((V.toNat : ℕ) : ℝ) = (V : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0'
      rw [this]; exact h1
    have := Nat.le_floor h2
    omega
  have hB : ∀ i, -((⌊η⌋₊ : ℕ) : ℤ) ≤ ⌊P.b i⌋ - E ∧ ⌊P.b i⌋ - E ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨B, hBi⟩ := P.b_int i
    have h1 := hb i
    rw [hBi, hE] at h1
    rw [hBi]
    simp only [Int.floor_intCast]
    have h2 : (((B - E).natAbs : ℕ) : ℝ) ≤ η := by
      rw [Nat.cast_natAbs]; push_cast at h1 ⊢; exact h1
    have h3 := Nat.le_floor h2
    have h4 : |B - E| ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    exact abs_le.mp h4
  simp only [jT1, jR, jW, cloud, lows, block, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
    Finset.mem_univ, true_and, Multiset.mem_range] at hu
  cases s with
  | true =>
    simp only [szT, if_true, Bool.not_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [if_true, Multiset.mem_map, Multiset.mem_add, Finset.mem_val, Finset.mem_univ,
      true_and] at hu
    obtain ⟨x, (hx | hx) | hx, rfl⟩ := hu
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hV i
      left; rw [hEf, ht1]; constructor <;> omega
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hB i
      right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega
  | false =>
    simp only [szT, Bool.not_false, if_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [Bool.false_eq_true, if_false, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
      Finset.mem_univ, true_and] at hu
    obtain ⟨x, hx | hx, rfl⟩ := hu
    · obtain ⟨y, hy | hy, rfl⟩ := hx
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hV i
        left; rw [hEf, ht1]; constructor <;> omega
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hB i
        right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedFrobeniusEigenUnitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_frobenius_eigen_unit : ∀ (D : D7), SumRepresentations.tie0 D → SumRepresentations.adm7 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∀ p ∈ Pa, ∀ w : PlE D.host, D.naut.unr (D.naut.locG p.π w) → ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), ‖α‖ = 1 := by
  first | exact @GlobalTheory.PartUnitary.part_frobEig_norm | exact GlobalTheory.PartUnitary.part_frobEig_norm | (intros; apply GlobalTheory.PartUnitary.part_frobEig_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGaloisStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_match_of_hecke_galois : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  first | exact @GlobalTheory.NRows.point_determines | exact GlobalTheory.NRows.point_determines | (intros; apply GlobalTheory.NRows.point_determines <;> assumption)
end

