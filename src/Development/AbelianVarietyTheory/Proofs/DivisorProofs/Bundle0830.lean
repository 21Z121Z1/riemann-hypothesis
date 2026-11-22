import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadingBlockLowerEntriesToBlockCoords
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomain
section
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

noncomputable section

theorem lintegral_exp_muF_eq_setLIntegral_Om (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 =
      ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  have hT : Measurable (GlobalTheory.UpCoordCompare.toEntries X) :=
    (GlobalTheory.UpCoordCompare.contDiff_toEntries X).continuous.measurable
  have hf : Measurable fun z => ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((GlobalTheory.PoleDbar.measurable_rhF X x0.1).const_mul s).neg)
  have hd : Measurable fun z => ENNReal.ofReal (density X x0 z) := by
    have e : (fun z => ENNReal.ofReal (density X x0 z)) =
        (fun z => ENNReal.ofReal (densF X x0.1 z)) ∘ GlobalTheory.UpCoordCompare.toEntries X := by
      funext z
      simp only [Function.comp_apply, GlobalTheory.UpCoordCompare.densF_toEntries]
    rw [e]
    exact (OntoC.measurable_densF X x0.1).comp hT
  have hOm : MeasurableSet (Om X) := by
    have : Om X = GlobalTheory.UpCoordCompare.toEntries X ⁻¹' OmF X x0.1 := by
      ext z; exact (GlobalTheory.UpCoordCompare.toEntries_mem_OmF_iff X x0 z).symm
    rw [this]
    exact hT (ExF.isOpen_OmF X x0.1).measurableSet
  rw [← GlobalTheory.UpCoordCompare.map_mu X x0, lintegral_map hf hT, mu,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hOm fun z hz => ?_
  simp only [Pi.mul_apply, GlobalTheory.UpCoordCompare.rhF_toEntries X x0 hz]

end

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDivPredMemOfPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem log_div_pred_mem_of_prime {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log p / ((p : ℝ) - 1) ∧ Real.log p / ((p : ℝ) - 1) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  refine ⟨div_nonneg (Real.log_nonneg (by linarith)) hpos.le, ?_⟩
  rw [div_le_one hpos]
  exact Real.log_le_sub_one_of_pos (by linarith)

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLeLOfLeCond
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare.SizeRows

variable {D : D7} {large₂ : SizeData₂ D}

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (by positivity)

theorem condE_le_b (P : ParameterChoice' D large₂) : (LevelStarExponents.condE D : ℝ) ≤ large₂.sc.b := by
  have h := P.condE_le
  have hb := one_le_b large₂.sc
  have h1 : large₂.sc.b ^ ((1 : ℝ) / 2) ≤ large₂.sc.b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ large₂.t_win.1
  have hc : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

theorem log_le_L_of_le_cond (P : ParameterChoice' D large₂) {p : ℕ} (hp : 0 < p) (h : p ≤ LevelStarExponents.condE D) :
    Real.log p ≤ large₂.sc.L := by
  have h1 : (p : ℝ) ≤ Real.exp large₂.sc.L := le_trans (by exact_mod_cast h) (condE_le_b P)
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hp)).2 h1

theorem f_mul_N_le_b (P : ParameterChoice' D large₂) (h4 : 4 * placeRankTwoOne.NN D ^ 3 ≤ large₂.etaSz) :
    (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ≤ large₂.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have ht := large₂.t_win.1
  have he := large₂.etaSz_pos
  have h := P.eta_le
  rw [le_div_iff₀ (by positivity)] at h
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  unfold placeRankTwoOne.NN at h4
  have h5 : (D.R.N D.R.m : ℝ) ≤ large₂.etaSz := by linarith
  have h6 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h7 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk'
  calc (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) = (D.R.N D.R.m : ℝ) * (1 * D.R.f * 1) := by ring
    _ ≤ large₂.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by gcongr
    _ ≤ _ := h

theorem eTau_tauPl (z : RPl D.R) : (D.eTau (tauPl D z) : D.R.GG) = G.plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem not_top_of (z : RPl D.R) (hz : ¬ PlaceLogThetaBounds.IsTopPl (numDatumOfParameters D large₂) z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_tauPl]
  intro h
  unfold Host.topPlaces at h
  obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
  obtain ⟨b, s⟩ := z
  cases b
  · have h1 : D.R.tau1 t = D.R.tau1 s := he
    have h2 : t = s := D.R.toFrame.tau1_injective h1
    subst h2
    exact hz ⟨rfl, ht⟩
  · have h1 : D.R.tau1 t = D.R.tau2 s := he
    exact (factPlaces D.R.toFrame).2 _ _ h1

theorem sizeRows_numRec : ∀ (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D), ConjugateFieldBounds.ParamHyp large₂ EX 25 → PageRows large₂ EX → ∀ (u : D.what₂.Word), (∀ j ∈ (numDatumOfParameters D large₂).lifts, ∀ z, ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i ∧ (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) ≤ 3 * large₂.sc.a) → PlaceLogThetaBounds.SizeRows (numDatumOfParameters D large₂) (codeRec large₂ u) (D.mem u).A.T := by
  intro D large₂ EX ⟨⟨P⟩, hS, _⟩ ⟨⟨n, hn⟩, hg, _⟩ u hnu
  obtain ⟨-, s2, s3, s4, -, -, s7, -, s9, s10, -, -, -, s14⟩ := hS
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  have hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc := by
    rw [large₂.Sc_eq]
    show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _
    rw [← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]
  have hq := D.host.hyp.1.pos
  have hd := D.host.hyp.2.1.pos
  have hn0 : 0 < D.R.n := by unfold Ranks.n; positivity
  refine ⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, s7 u, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2
  · refine log_le_L_of_le_cond P hq ?_
    unfold LevelStarExponents.condE
    exact le_trans (Nat.le_mul_of_pos_left D.host.q D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)
  · refine log_le_L_of_le_cond P hd ?_
    unfold LevelStarExponents.condE
    exact Nat.le_mul_of_pos_left D.host.d (Nat.mul_pos D.host.QS_pos hq)
  · rw [large₂.logDerivative_at_one_eq] at s3
    exact s3
  · obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
    exact h1.trans (h2 i).1
  · intro z i j
    refine (large₂.be_close (tauPl D z) i j).trans ?_
    show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)
    have h := Nat.le_ceil (LevelStarExponents.h0 large₂)
    calc large₂.etaSz = (D.R.m : ℝ) * LevelStarExponents.h0 large₂ := by unfold LevelStarExponents.h0; field_simp
      _ ≤ _ := by gcongr
  · intro z i
    rw [hSc]
    obtain ⟨h1, h2⟩ := large₂.cloud_v (tauPl D z) i
    exact ⟨by exact_mod_cast h1, h2⟩
  · intro z i h1 h2
    obtain ⟨i, hi⟩ := i
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by simp only at h1; omega⟩
    have hl : l < D.R.k - 2 := by
      have : l + 1 + 1 < D.R.k := h2
      omega
    have e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩ := by
      rw [D.s.u_letter u (tauPl D z) l hl, D.hcW_v]
      unfold NumDatum.uW
      rw [dif_pos ⟨h1, h2⟩]
      show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _
      rw [hDel]
      rfl
    rw [hSc, e]
    obtain ⟨a1, a2⟩ := large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro t ht
    have h := (large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2
    have e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ) := by
      unfold NumDatum.bT
      push_cast
      erw [h]
      ring
    rw [e]
    exact ⟨large₂.bT_ge _, s14 _⟩
  · intro z hz hk2
    have hz' := not_top_of z hz
    rw [hSc]
    refine ⟨s9 _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩
    have h1 := P.cloud_place_bound _ (by omega) hz'
    have h2 := (large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2
    push_cast at h1
    show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _
    linarith

end GlobalTheory.ColumnNormCompare.SizeRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuation
section
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.AdelicDetSpan

variable {E : Type} [Field E] [NumberField E]

noncomputable def comp (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem comp_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    comp P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem val_det_le_one {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  let N : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨M i j, h i j⟩
  have e : M = v.integer.subtype.mapMatrix N := rfl
  rw [e, ← RingHom.map_det]
  exact N.det.2

theorem exists_clear (Q : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hy : Valued.v (comp Q y) ≤ 1) :
    ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      P.valuation E (b : E) * Valued.v (comp P y) ≤ 1 := by
  classical
  have hloc : ∀ P : HeightOneSpectrum (𝓞 E), ∃ c : 𝓞 E, c ∉ Q.asIdeal ∧
      P.valuation E (c : E) * Valued.v (comp P y) ≤ 1 := by
    intro P
    by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, by simpa using h1⟩
    have hPQ : P ≠ Q := by rintro rfl; exact h1 hy
    have hnle : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      hPQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hnle
    have hlt : P.valuation E (a : E) < 1 := (P.valuation_lt_one_iff_mem (K := E) a).2 haP
    have h0 : Valued.v (comp P y) ≠ 0 := by
      intro h; rw [h] at h1; exact h1 zero_le_one
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ h0)⁻¹
    refine ⟨a ^ m, fun h => haQ (Q.isPrime.mem_of_pow_mem m h), ?_⟩
    have : ((a ^ m : 𝓞 E) : E) = (a : E) ^ m := by simp
    rw [this, map_pow]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
    calc _ ≤ (Valued.v (comp P y))⁻¹ * Valued.v (comp P y) := mul_le_mul' hm.le le_rfl
      _ = 1 := inv_mul_cancel₀ h0
  choose c hcQ hc using hloc
  have hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ Valued.v (comp P y) ≤ 1}.Finite :=
    Filter.eventually_cofinite.1 y.2
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  refine ⟨∏ P ∈ hfin.toFinset, c P, ?_, fun P => ?_⟩
  · rw [Q.isPrime.prod_mem_iff]
    rintro ⟨P, -, h⟩
    exact hcQ P h
  · by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact mul_le_one' (hle _ _) h1
    · have hm : P ∈ hfin.toFinset := by simpa using h1
      rw [← Finset.prod_erase_mul _ _ hm]
      have : (((∏ x ∈ hfin.toFinset.erase P, c x) * c P : 𝓞 E) : E) =
        ((∏ x ∈ hfin.toFinset.erase P, c x : 𝓞 E) : E) * (c P : E) := by push_cast; rfl
      rw [this, map_mul, mul_assoc]
      exact mul_le_one' (hle _ _) (hc P)

theorem exists_approx_matrix (Q : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) (hg : h * g = 1) :
    ∃ X : Matrix (Fin n) (Fin n) E,
      (∀ i j, Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j) ≤ 1) ∧
      Valued.v (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det = 1 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => Pi.map fun _ : Fin n =>
      (algebraMap E (Q.adicCompletion E) : E → _)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) Q
  have hc : Continuous fun X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) => h * X :=
    continuous_const.matrix_mul continuous_id
  have hb : IsOpen {z : Q.adicCompletion E | Valued.v z < 1} := by
    have h := Valued.isOpen_ball (Q.adicCompletion E) 1
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  have hU : IsOpen {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
      (∀ i j, Valued.v ((h * X - 1) i j) < 1) ∧ Valued.v ((h * X).det - 1) < 1} := by
    refine IsOpen.inter ?_ (hb.preimage (hc.matrix_det.sub continuous_const))
    have : IsOpen (⋂ i, ⋂ j, {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
        Valued.v ((h * X - 1) i j) < 1}) :=
      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hb.preimage ((hc.sub continuous_const).matrix_elem i j)
    simp only [← Set.setOf_forall] at this
    exact this
  obtain ⟨X, h1, h2⟩ := hd.exists_mem_open hU ⟨g, ⟨fun i j => by rw [hg]; simp, by rw [hg]; simp⟩⟩
  refine ⟨X, fun i j => ?_, ?_⟩
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j) < 1 := h1 i j
    have e : (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j =
        (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j +
          (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ h3.le ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det - 1) < 1 := h2
    have := Valuation.map_eq_of_sub_lt Valued.v (x := (1 : Q.adicCompletion E)) (by rw [map_one]; exact h3)
    rwa [map_one] at this

theorem comp_mulVec {n : ℕ} (h : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (X : Matrix (Fin n) (Fin n) E) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    comp P (h.mulVec (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) =
      ((comp P).mapMatrix h * (algebraMap E (P.adicCompletion E)).mapMatrix X) i j := by
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, comp_alg]

theorem mem_span_detSet_iff : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  intro E _ _ n g L hL x
  classical
  have hL' : ∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
      Valued.v (comp Q ((g⁻¹).1.mulVec
        (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i)) ≤ 1 := hL
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  have hhg : ∀ Q : HeightOneSpectrum (𝓞 E),
      (comp Q).mapMatrix (g⁻¹).1 * (comp Q).mapMatrix g.1 = 1 := fun Q => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hdet : ∀ (Q : HeightOneSpectrum (𝓞 E)) (X : Matrix (Fin n) (Fin n) E),
      Q.valuation E X.det = Valued.v (comp Q g.1.det) *
        Valued.v ((comp Q).mapMatrix (g⁻¹).1 *
          (algebraMap E (Q.adicCompletion E)).mapMatrix X).det := fun Q X => by
    rw [← map_mul, RingHom.map_det, ← Matrix.det_mul, ← mul_assoc, ← map_mul, Units.mul_inv,
      map_one, one_mul, ← RingHom.map_det, val_alg]
  show _ ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (comp Q g.1.det)
  constructor
  · intro hx Q
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨v, hv, rfl⟩ := hd
      rw [hdet]
      refine mul_le_of_le_one_right' (val_det_le_one _ _ fun i j => ?_)
      rw [← comp_mulVec]
      exact (hL' _).1 (hv j) i Q
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul a b _ hb =>
      have e : a • b = (a : E) * b := rfl
      rw [e, map_mul]
      exact (mul_le_of_le_one_left' (hle Q a)).trans hb
  · intro hx
    have hloc : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧
        b • x ∈ Submodule.span (𝓞 E) (detSet L) := by
      intro Q
      obtain ⟨X, hX1, hX2⟩ := exists_approx_matrix Q _ _ (hhg Q)
      choose c hcQ hc using fun i j => exists_clear Q ((g⁻¹).1.mulVec
        (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i)
        (by rw [comp_mulVec]; exact hX1 i j)
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, b = ∏ p : Fin n × Fin n, c p.1 p.2 := ⟨_, rfl⟩
      have hbQ : b ∉ Q.asIdeal := by
        rw [hb, Q.isPrime.prod_mem_iff]
        rintro ⟨p, -, h⟩
        exact hcQ _ _ h
      have hb1 : Q.valuation E (b : E) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q (r := b)).2 hbQ
      have hbc : ∀ i j (P : HeightOneSpectrum (𝓞 E)),
          P.valuation E (b : E) ≤ P.valuation E (c i j : E) := by
        intro i j P
        obtain ⟨t, ht⟩ : c i j ∣ b := hb ▸ Finset.dvd_prod_of_mem
          (fun p : Fin n × Fin n => c p.1 p.2) (Finset.mem_univ (i, j))
        have : (b : E) = (c i j : E) * (t : E) := by rw [ht]; push_cast; rfl
        rw [this, map_mul]
        exact mul_le_of_le_one_right' (hle P t)
      have hd : ((b : E) • X).det ∈ detSet L := by
        refine ⟨fun j i => (b : E) * X i j, fun j => (hL' _).2 fun i P => ?_, rfl⟩
        have e : comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) ((b : E) * X k j)) i) =
            algebraMap E _ (b : E) * comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) := by
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, comp_alg, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [e, map_mul, val_alg]
        exact (mul_le_mul' (hbc i j P) le_rfl).trans (hc i j P)
      have hdv : Q.valuation E ((b : E) • X).det = Valued.v (comp Q g.1.det) := by
        rw [Matrix.det_smul, map_mul, map_pow, hb1, one_pow, one_mul, hdet, hX2, mul_one]
      obtain ⟨d, hdd⟩ : ∃ d, d = ((b : E) • X).det := ⟨_, rfl⟩
      rw [← hdd] at hd hdv
      have hg0 : Valued.v (comp Q g.1.det) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((g.isUnit.map Matrix.detMonoidHom).map (comp Q)).ne_zero
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [map_zero] at hdv
        exact hg0 hdv.symm
      obtain ⟨s, hsQ, hs⟩ := exists_clear Q (algebraMap E _ (x / d)) (by
        rw [comp_alg, val_alg, map_div₀, hdv]
        exact (div_le_one₀ (zero_lt_iff.2 hg0)).2 (hx Q))
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
        ((s : E) * (x / d)) (fun P => by
          have := hs P
          rwa [comp_alg, val_alg, ← map_mul] at this)
      refine ⟨s, hsQ, ?_⟩
      have e : s • x = a • d := by
        have e1 : s • x = (s : E) * x := rfl
        have e2 : a • d = algebraMap (𝓞 E) E a * d := rfl
        rw [e1, e2, ha]
        field_simp
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hd)
    let I : Ideal (𝓞 E) := (Submodule.span (𝓞 E) (detSet L)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E x)
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
      have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
      obtain ⟨b, hb, hbx⟩ := hloc ⟨M, hM.isPrime, hM0⟩
      exact hb (hIM hbx)
    have h1 : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 E) • x ∈ Submodule.span (𝓞 E) (detSet L) := h1
    rwa [one_smul] at h2

end GlobalTheory.AdelicDetSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatPrimeNotMemPrimeCubeOfIsUnramifiedAtStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt : ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  first | exact @GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | exact GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt | (intros; apply GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTensorLineBundleGlobalSectionsEquivStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB → Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  first | exact @GlobalTheory.SecTensor.tensorSecEquiv | exact GlobalTheory.SecTensor.tensorSecEquiv | (intros; apply GlobalTheory.SecTensor.tensorSecEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneCharacterModulusOneAllEmbeddingsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneCharacter_modulusOne_all_embeddings : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → StandardLatticesGL3.Mod1All (χ 𝔞) := by
  first | exact @GlobalTheory.CharModOne.mod1All_of_isChi | exact GlobalTheory.CharModOne.mod1All_of_isChi | (intros; apply GlobalTheory.CharModOne.mod1All_of_isChi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVectorStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  first | exact @GlobalTheory.NatAtStd.eNat_std | exact GlobalTheory.NatAtStd.eNat_std | (intros; apply GlobalTheory.NatAtStd.eNat_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatibleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numDatum_numbers_eq_host_of_compatible : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X), HostTie N s Pr → N.rd = D.host.rdE ∧ N.v = D.host.v ∧ N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D ∧ N.logOm = TaylorLogMetric.logOmVal D ∧ TaylorLogMetric.fF D = N.R.f ∧ X.f = N.R.f ∧ Module.finrank ℚ X.E = 2 * N.R.f ∧ |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd ∧ TaylorLogMetric.IsCurveIdeal D D.host.ccK := by
  first | exact @GlobalTheory.ColNorms.numbers_of_hostTie | exact GlobalTheory.ColNorms.numbers_of_hostTie | (intros; apply GlobalTheory.ColNorms.numbers_of_hostTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offDiagonalRamified_bound_along_family' : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family | exact GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family | (intros; apply GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family <;> assumption)
end

