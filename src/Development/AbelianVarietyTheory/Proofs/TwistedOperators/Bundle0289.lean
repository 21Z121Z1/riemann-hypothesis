import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationIntertwinesRealGroup
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientContinuous
section
noncomputable section

open MeasureTheory GlobalTheory.Chamber Finset
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FamCont

theorem deriv_pow_succ_mul {g : ℝ → ℂ} (hg : Differentiable ℝ g) (m : ℕ) :
    deriv (fun t : ℝ => (t : ℂ) ^ (m + 1) * g t) =
      fun t : ℝ => (t : ℂ) ^ m * (((m : ℂ) + 1) * g t + (t : ℂ) * deriv g t) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m) t := by
    simpa using (hasDerivAt_pow (m + 1) (t : ℂ)).comp_ofReal
  have h3 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1) * g t)
      (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m * g t + (t : ℂ) ^ (m + 1) * deriv g t) t := h1.mul (hg t).hasDerivAt
  rw [h3.deriv]
  push_cast; ring

theorem contDiff_linear_deriv_combination {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (a : ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => a * g t + (t : ℂ) * deriv g t) := by
  have hd := (contDiff_infty_iff_deriv.1 hg).2
  exact (contDiff_const.mul hg).add (Complex.ofRealCLM.contDiff.mul hd)

theorem iteratedDeriv_pow_mul (n : ℕ) : ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g →
    iteratedDeriv n (fun t : ℝ => (t : ℂ) ^ n * g t) 0 = n.factorial * g 0 := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [iteratedDeriv_succ', deriv_pow_succ_mul (hg.differentiable (by simp)), ih _ (contDiff_linear_deriv_combination hg _)]
    simp [Nat.factorial_succ]
    ring

theorem iteratedDeriv_sum_exp {ι : Type} (s : Finset ι) (e c : ι → ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ∑ i ∈ s, e i * Complex.exp (c i * t)) =
      fun t : ℝ => ∑ i ∈ s, e i * c i ^ n * Complex.exp (c i * (t : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : ∀ i ∈ s, HasDerivAt (fun t : ℝ => e i * c i ^ n * Complex.exp (c i * t))
        (e i * c i ^ (n + 1) * Complex.exp (c i * t)) t := fun i _ => by
      have h1 : HasDerivAt (fun t : ℝ => c i * (t : ℂ)) (c i) t := by
        simpa using ((hasDerivAt_id (t : ℂ)).const_mul (c i)).comp_ofReal
      have h2 : HasDerivAt (fun t : ℝ => e i * c i ^ n * Complex.exp (c i * t))
          (e i * c i ^ n * (Complex.exp (c i * t) * c i)) t := h1.cexp.const_mul (e i * c i ^ n)
      exact h2.congr_deriv (by ring)
    have hs := HasDerivAt.sum h
    rw [Finset.sum_fn] at hs
    exact hs.deriv

theorem card_eq_finrank {k : ℕ} {P : Finset (SV k)} (h : IsPar P) : Module.finrank ℝ (aP P) = P.card := by
  have li : LinearIndependent ℝ (fun u : (P : Set (SV k)) => vec (k := k) u) := by
    rw [linearIndependent_iff_notMem_span]
    rintro ⟨u, hu⟩
    have h' := h.vec_notMem hu
    convert h' using 3
    rw [aP]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, Subtype.exists,
      Finset.mem_coe, Finset.mem_erase, Subtype.mk.injEq]
    constructor
    · rintro ⟨a, ha, hne, rfl⟩; exact ⟨a, ⟨hne, ha⟩, rfl⟩
    · rintro ⟨a, ⟨hne, ha⟩, rfl⟩; exact ⟨a, ha, hne, rfl⟩
  have := finrank_span_eq_card li
  rw [aP, Set.image_eq_range, this]
  convert Fintype.card_coe P
  simp

theorem isGMFam_expFam {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X) :
    IsGMFam 𝔞 (expFam X) := by
  intro P hP
  refine ⟨?_, fun R hR l => ?_⟩
  · unfold expFam eL
    exact Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)))
  · simp only [expFam, eL]
    rw [hX P hP R hR, pr, Submodule.inner_starProjection_left_eq_right]

theorem smul_mem_generic {k : ℕ} {l : A0 k} (hl : l ∈ generic k) {t : ℝ} (ht : t ≠ 0) : t • l ∈ generic k := by
  intro P hP R hR u hu
  rw [real_inner_smul_left]
  exact mul_ne_zero ht (hl P hP R hR u hu)

theorem card_sdiff_of_mem_parP {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {Q P : Finset (SV k)} (hP : P ∈ parP 𝔞 Q) :
    (P \ Q).card = Module.finrank ℝ 𝔞 - Q.card := by
  obtain ⟨hP1, hP2, hP3⟩ := mem_parP.1 hP
  rw [card_sdiff_of_subset hP3, ← card_eq_finrank hP1, hP2]

theorem eps_smul {k : ℕ} (P Q : Finset (SV k)) (l : A0 k) (t : ℝ) :
    eps P Q (t • l) = ((t : ℂ) ^ (P \ Q).card)⁻¹ * eps P Q l := by
  have e1 : ∀ a : ℂ, (Complex.I * ((t : ℂ) * a))⁻¹ = (t : ℂ)⁻¹ * (Complex.I * a)⁻¹ := fun a => by
    rw [mul_left_comm, mul_inv]
  simp only [eps, epsOf, real_inner_smul_left, Complex.ofReal_mul]
  simp_rw [e1, prod_mul_distrib, prod_const, inv_pow]
  ring

theorem cM_expFam_zero (hFS : FamilySmooth) {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} (h𝔞 : IsLevi 𝔞) {Q : Finset (SV k)}
    (hQ : Q ∈ parF 𝔞 ∅) {X : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X) {l₀ : A0 k} (hl₀ : l₀ ∈ generic k) :
    cM 𝔞 Q (expFam X) 0 = (∑ P ∈ parP 𝔞 Q, eps P Q l₀ *
      (Complex.I * (⟪l₀, X P⟫_ℝ : ℂ)) ^ (Module.finrank ℝ 𝔞 - Q.card)) / (Module.finrank ℝ 𝔞 - Q.card).factorial := by
  set n := Module.finrank ℝ 𝔞 - Q.card
  obtain ⟨⟨hsm, heq⟩, -⟩ := hFS k 𝔞 h𝔞 _ (isGMFam_expFam hX) Q hQ
  set f : ℝ → ℂ := fun t => cM 𝔞 Q (expFam X) (t • l₀) with hfdef
  have hf : ContDiff ℝ ∞ f := hsm.comp (contDiff_id.smul contDiff_const)
  have hfun : (fun t : ℝ => (t : ℂ) ^ n * f t) = fun t : ℝ => ∑ P ∈ parP 𝔞 Q,
      eps P Q l₀ * Complex.exp ((Complex.I * (⟪l₀, X P⟫_ℝ : ℂ)) * (t : ℂ)) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℝ))
      ((Complex.continuous_ofReal.pow n).mul hf.continuous)
      (continuous_finset_sum _ fun P _ => continuous_const.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) ?_
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [hfdef]
    rw [heq (smul_mem_generic hl₀ ht), sumM, mul_sum]
    refine sum_congr rfl fun P hP => ?_
    rw [eps_smul, card_sdiff_of_mem_parP hP, expFam, eL, real_inner_smul_left, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht)), one_mul]
    congr 2
    push_cast
    ring
  have h1 := iteratedDeriv_pow_mul n f hf
  rw [hfun, iteratedDeriv_sum_exp] at h1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hfdef, zero_smul] at h1
  rw [h1, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))]

theorem continuous_cM_expFam_zero : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅,
    ∀ (Z : Type) [TopologicalSpace Z] (X : Z → Finset (SV k) → A0 k), (∀ z, IsOrth 𝔞 (X z)) →
    (∀ P ∈ parP 𝔞 Q, Continuous fun z => X z P) → Continuous fun z => cM 𝔞 Q (expFam (X z)) 0 := by
  intro hFS k 𝔞 h𝔞 Q hQ Z _ X hX hc
  obtain ⟨l₀, hl₀⟩ : (generic k).Nonempty := dense_generic.nonempty
  simp_rw [cM_expFam_zero hFS h𝔞 hQ (hX _) hl₀]
  refine Continuous.div_const (continuous_finset_sum _ fun P hP => ?_) _
  exact continuous_const.mul ((continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.inner (hc P hP)))).pow _)

end GlobalTheory.FamCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientTranslation
section
open MeasureTheory GlobalTheory.Chamber Filter Topology

noncomputable section

namespace GlobalTheory.Chamber

theorem sumM_expFam_shift {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (X Y : Finset (SV k) → A0 k) (h : A0 k)
    (hY : ∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) (l : A0 k) :
    sumM 𝔞 Q (expFam Y) l = eL l (𝔞.starProjection h) * sumM 𝔞 Q (expFam X) l := by
  unfold sumM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' := (mem_parP.1 hP).2.1
  have e : pr P h = 𝔞.starProjection h := by subst hP'; rfl
  simp only [expFam, hY P hP, e, eL, inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem cM_expFam_shift_zero : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅,
    ∀ X Y : Finset (SV k) → A0 k, IsOrth 𝔞 X → ∀ h : A0 k, (∀ P ∈ parP 𝔞 Q, Y P = X P + pr P h) →
      cM 𝔞 Q (expFam Y) 0 = cM 𝔞 Q (expFam X) 0 := by
  intro hFS k 𝔞 hL Q hQ X Y hX h hY
  have hc := (hFS k 𝔞 hL (expFam X) hX.isGMFam Q hQ).1
  have t1 : Tendsto (sumM 𝔞 Q (expFam X)) (𝓝[generic k] 0) (𝓝 (cM 𝔞 Q (expFam X) 0)) :=
    ((hc.1.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun l hl => hc.2 hl)
  have hg : Continuous fun l : A0 k => eL l (𝔞.starProjection h) := by
    unfold eL; fun_prop
  have t2 : Tendsto (fun l : A0 k => eL l (𝔞.starProjection h)) (𝓝[generic k] 0) (𝓝 1) := by
    have := (hg.tendsto 0).mono_left (nhdsWithin_le_nhds (s := generic k))
    simpa [eL] using this
  have t3 := t2.mul t1
  rw [one_mul] at t3
  unfold cM
  refine extendFrom_eq (dense_generic 0) ?_
  have e : sumM 𝔞 Q (expFam Y) = fun l => eL l (𝔞.starProjection h) * sumM 𝔞 Q (expFam X) l :=
    funext (sumM_expFam_shift 𝔞 Q X Y h hY)
  rw [e]
  exact t3

end GlobalTheory.Chamber
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridReal

open GlobalTheory.SignedHC

theorem num_real_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  intro D large₂ hS τ
  obtain ⟨⟨Pm, -, -⟩, -, -, hm44, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, -⟩ := GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr6 : 6 ≤ D.R.r := by unfold Ranks.r; omega
  set X : ℝ := (D.R.r : ℝ) + 1 with hX
  have hX7 : 7 ≤ X := by
    have : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    linarith
  have hX3 : 0 ≤ X ^ 3 := by positivity

  have hgapS : (2 : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap := by
    unfold Formalism.BasicNotions.LevelStarExponents.gapS
    have h1 : 0 ≤ Pm.Cgap * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 := by
      have := Pm.Cgap_pos; positivity
    have hN : (2 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; exact le_trans (by omega) (Nat.le_add_right _ _)
      exact_mod_cast this
    have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
    nlinarith

  have hgap : 1000 * X ^ 3 ≤ (G.ga : ℝ) := by
    have hB := ((GlobalTheory.ChiGrid.gapBound_iff D 1 (GlobalTheory.ChiGrid.gap D 1)).2 le_rfl).1
    have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = X := by unfold GlobalTheory.ChiGrid.nRk; push_cast; rfl
    rw [hn] at hB
    have h1 : 0 ≤ (1 : ℝ) * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 3 := by positivity
    have h2 : 0 ≤ (1 : ℝ) * X ^ 3 * Real.sqrt (GlobalTheory.ChiGrid.cloudLen D) := by
      have := Real.sqrt_nonneg (GlobalTheory.ChiGrid.cloudLen D : ℝ); positivity
    have h4 : (1000 : ℝ) ≤ X ^ 4 := by
      have : (7 : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX7 4
      norm_num at this; linarith
    have h7 : 1000 * X ^ 3 ≤ X ^ 7 := by
      have : X ^ 7 = X ^ 4 * X ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h4 hX3
    rw [hga]; linarith
  have hX1 : (1 : ℝ) ≤ 1000 * X ^ 3 := by
    have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ (by linarith)
    linarith

  have hga0 : (0 : ℝ) ≤ (G.ga : ℝ) := by positivity
  have hSb' : large₂.Sc + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := by rw [hga]; exact hSb
  have hSc := large₂.Sc_pos
  have hbga : (G.ga : ℝ) ≤ large₂.sc.b := by
    have : (G.ga : ℝ) ≤ ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
      nlinarith
    linarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hbsq : large₂.sc.b ≤ large₂.sc.b ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb1, ?_⟩
  ·
    intro i hi1 hi2
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    have hlt : a + 1 < D.R.k - 1 := by rw [hk] at hi2; omega
    have h := (Pm.sig_gaps τ).1 a hlt
    have e := hv ⟨a, by omega⟩
    have e' := hv ⟨a + 1, hlt⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have : ((G.v (a + 2 + 1) : ℤ) : ℝ) + 2 ≤ ((G.v (a + 2) : ℤ) : ℝ) := by
      rw [show a + 2 + 1 = a + 1 + 2 by omega]; linarith
    exact_mod_cast this
  ·
    have h := (Pm.sig_gaps τ).2.1 (by omega) (by omega)
    have e := hv ⟨D.R.k - 2, by omega⟩
    have e' := hb ⟨0, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    have : (2 : ℝ) ≤ ((G.v (D.R.k - 2 + 2) : ℤ) : ℝ) + ((G.b (0 + 1) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  ·
    intro l hl1 hl2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hl1
    have hlt : j + 1 < D.R.m := by rw [hm] at hl2; omega
    have h := (Pm.nodes_gap τ j hlt).1
    have hf := Pm.heightBound_ge_rank_cubic
    have e := hb ⟨j + 1, hlt⟩
    have e' := hb ⟨j, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have hY : 10 * X ≤ (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      have h44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
      have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
      have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have hY3 : (10 * X) ^ 3 ≤ ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hY 3
    have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
    have : ((G.b (j + 1) : ℤ) : ℝ) + 1000 * X ^ 3 ≤ ((G.b (j + 1 + 1) : ℤ) : ℝ) := by nlinarith
    exact this
  · exact hgap
  ·
    have h := (large₂.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
    rw [hv] at h
    simp only at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    exact_mod_cast h
  ·
    have h := (hpos τ ⟨0, by omega⟩).1
    have e := hb ⟨0, by omega⟩
    have h' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast h
    rw [e] at h'
    exact_mod_cast h'
  ·
    have h := (large₂.cloud_v τ ⟨0, by omega⟩).2
    rw [hv] at h
    simp only [zero_add] at h
    have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      unfold GridData.a; rw [hm]; push_cast; ring
    rw [e]; linarith
  ·
    have h := large₂.b_le τ ⟨D.R.m - 1, by omega⟩
    rw [hb] at h
    simp only at h
    rw [hm, show D.R.m = D.R.m - 1 + 1 by omega]
    exact h
  ·
    have h8 : 8 * X ≤ 1000 * X ^ 3 := by
      have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ (by linarith)
      have : X ^ 3 = X * X ^ 2 := by ring
      have hXX : X ≤ X ^ 3 := by rw [this]; nlinarith
      linarith
    have hb4 : large₂.sc.b ≤ large₂.sc.b ^ 4 := by
      have : large₂.sc.b ^ 4 = large₂.sc.b * large₂.sc.b ^ 3 := by ring
      rw [this]
      have : (1 : ℝ) ≤ large₂.sc.b ^ 3 := one_le_pow₀ hb1
      nlinarith
    linarith

end GlobalTheory.GridReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumInnerEqSumVectorThetaLiftsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  first | exact @GlobalTheory.LiftGram.inner_eq_sum_upLift | exact GlobalTheory.LiftGram.inner_eq_sum_upLift | (intros; apply GlobalTheory.LiftGram.inner_eq_sum_upLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPowStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_split | exact GlobalTheory.TrEll.realTorus_split | (intros; apply GlobalTheory.TrEll.realTorus_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationIntertwinesRealGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTranslatedRowEvaluation_intertwines_realGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ S ∈ EP R F, ∀ (g : X.B.I.Ginf) (y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)), ∃ y' : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), GlobalTheory.RowEvalHH.tensT X (fun τ => (y' τ : X.B.H (X.pl.symm τ))) = X.B.σs g (GlobalTheory.RowEvalHH.tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))) ∧ GlobalTheory.RowEvalHH.evF R X h t c S y' = X.B.R (g, 1) (GlobalTheory.RowEvalHH.evF R X h t c S y) := by
  first | exact @GlobalTheory.RowEvalHH.evF_equiv | exact GlobalTheory.RowEvalHH.evF_equiv | (intros; apply GlobalTheory.RowEvalHH.evF_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationMultilinearNormSqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTranslatedRowEvaluation_multilinear_norm_sq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ∀ S ∈ EP R F, ∃ (f : MultilinearMap ℂ (fun τ => ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)) (L2X X)) (K : ℝ), (∀ y, f y = GlobalTheory.RowEvalHH.evF R X h t c S y) ∧ ∀ y, ‖f y‖ ^ 2 = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  first | exact @GlobalTheory.RowEvalHHNorm.evF_multilinear_norm | exact GlobalTheory.RowEvalHHNorm.evF_multilinear_norm | (intros; apply GlobalTheory.RowEvalHHNorm.evF_multilinear_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoMean

theorem isThetaFunO_bounded {D : D7} (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := hF.quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ') = ratW W V γ' := rfl
  rw [e] at hx
  have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ') x))
  have := hC _ hx
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (emb V W P Q) := by
  unfold emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_meanX : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ F hF
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : FirstCountableTopology (WO V W) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := isThetaFunO_bounded V W ψ hψ F hF
  unfold meanX
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_) (integrable_const C) ?_
  · exact (hF.cont.comp ((continuous_emb V W P Q).add continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hC _
  · exact Filter.Eventually.of_forall fun y => hF.cont.comp (continuous_const.add continuous_id)

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  first | exact @GlobalTheory.ResHeisCont.continuous_res_heisO | exact GlobalTheory.ResHeisCont.continuous_res_heisO | (intros; apply GlobalTheory.ResHeisCont.continuous_res_heisO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedWeilFirstFactorApplyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_restrictedWeilFirstFactor_apply : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ x, Continuous fun m : GA D V => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) x := by
  first | exact @GlobalTheory.ResFirstCont.continuous_res_left | exact GlobalTheory.ResFirstCont.continuous_res_left | (intros; apply GlobalTheory.ResFirstCont.continuous_res_left <;> assumption)
end

