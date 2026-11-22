import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebra
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric Formalism.REAL

noncomputable section

namespace GlobalTheory.GaugeSubExists

open GlobalTheory.GaugeConst

variable {n : ℕ}

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℝ) (α := ℂ)
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  exact A.closed_of_finiteDimensional.mem_of_tendsto h1.tendsto_sum_nat
    (Eventually.of_forall fun m => A.sum_mem fun k _ => A.smul_mem _ (hp k))

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) ℂ) - 1 ∈ A
    simp
  mul_mem' := by
    intro g h hg hh
    change uMat g * uMat h - 1 ∈ A
    have : uMat g * uMat h - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      noncomm_ring
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := by
    intro g hg
    have hgi : uMat g⁻¹ * uMat g = 1 := g.1.inv_mul
    have hst : ∀ x ∈ A, LinearMap.mulLeft ℝ (uMat g) x ∈ A := by
      intro x hx
      have : LinearMap.mulLeft ℝ (uMat g) x = (uMat g - 1) * x + x := by
        rw [LinearMap.mulLeft_apply]; noncomm_ring
      rw [this]
      exact A.add_mem (hA _ hg _ hx) hx
    have hinj : Function.Injective ((LinearMap.mulLeft ℝ (uMat g)).restrict hst) := by
      intro x y hxy
      have h1 : uMat g * x.1 = uMat g * y.1 := congrArg Subtype.val hxy
      have h2 := congrArg (uMat g⁻¹ * ·) h1
      simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul] at h2
      exact Subtype.ext h2
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨_, hg⟩
    have h1 : uMat g * x.1 = uMat g - 1 := congrArg Subtype.val hx
    have h2 := congrArg (uMat g⁻¹ * ·) h1
    simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one] at h2
    change uMat g⁻¹ - 1 ∈ A
    rw [← neg_sub, ← h2]
    exact A.neg_mem x.2

theorem isClosed_algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (UJ ε)) :=
  A.closed_of_finiteDimensional.preimage ((continuous_uMat ε).sub continuous_const)

theorem exists_preimage {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (A : Submodule ℝ M) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) (hA : ∀ X ∈ A, f X ∈ A) {W : Set M} (hW : W ∈ 𝓝 (0 : M)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ f Y = a.1 := by
  obtain ⟨p, hp⟩ := A.subtype.exists_leftInverse_of_injective A.ker_subtype
  have hp' : ∀ x : A, p x.1 = x := fun x => LinearMap.congr_fun hp x
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ _
  have h1 : HasStrictFDerivAt (fun x : A => f x.1) A.subtypeL 0 :=
    HasStrictFDerivAt.comp (0 : A) (g := f) (f := Subtype.val) hf A.subtypeL.hasStrictFDerivAt
  have h2 := (LinearMap.toContinuousLinearMap p).hasStrictFDerivAt.comp (0 : A) h1
  have h3 : (LinearMap.toContinuousLinearMap p).comp A.subtypeL =
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) := by
    ext1 x; exact hp' x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [Submodule.coe_zero, h0, map_zero] at h4
  rw [← h4]
  have h6 : Subtype.val ⁻¹' W ∈ 𝓝 (0 : A) := continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  refine mem_of_superset (image_mem_map h6) ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact ⟨Y.1, Y.2, hY, (congrArg Subtype.val (hp' ⟨_, hA _ Y.2⟩)).symm⟩

open scoped Matrix.Norms.Frobenius in

theorem exists_log (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {W : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hW : W ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ NormedSpace.exp Y - 1 = a.1 :=
  exists_preimage A (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ)))
    (fun _ hX => exp_sub_one_mem A hA hX) hW

def expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (X : ↥(A ⊓ lieJ ε)) : algSub ε A hA :=
  ⟨expJ ε ⟨X.1, X.2.2⟩, exp_sub_one_mem A hA X.2.1⟩

theorem continuous_expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Continuous (expSub ε A hA) :=
  ((continuous_expJ ε).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

theorem expSub_image_mem_nhds (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {U : Set ↥(A ⊓ lieJ ε)} (hU : U ∈ 𝓝 (0 : ↥(A ⊓ lieJ ε))) :
    expSub ε A hA '' U ∈ 𝓝 (1 : algSub ε A hA) := by
  obtain ⟨e, he, h0⟩ := UpqExpChart.exists_chart (n := Fin n)
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have hs := e.open_source.mem_nhds h0
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype _ _ _).1 hU
  have h1 : expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source)) ∈ 𝓝 (1 : UJ ε) :=
    expJ_image_mem_nhds ε (continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem hT hs))
  have h2 : Subtype.val ⁻¹' (expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source))) ∈ 𝓝 (1 : algSub ε A hA) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds h1
  have hc : Continuous fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A) :=
    (((continuous_uMat ε).comp continuous_subtype_val).sub continuous_const).subtype_mk _
  have h3 : Tendsto (fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A)) (𝓝 1) (𝓝 0) :=
    hc.tendsto' 1 0 (Subtype.ext (sub_self (1 : Matrix (Fin n) (Fin n) ℂ)))
  filter_upwards [h2, h3.eventually (exists_log A hA hs)] with g hg1 hg2
  obtain ⟨X, hX, hXg⟩ := hg1
  obtain ⟨Y, hYA, hY, hYg⟩ := hg2
  have h4 : NormedSpace.exp X.1 = uMat g.1 := congrArg uMat hXg
  have h5 : NormedSpace.exp Y = uMat g.1 := sub_left_injective hYg
  have h6 : X.1 = Y := hinj hX.2 hY (h4.trans h5.symm)
  exact ⟨⟨X.1, h6 ▸ hYA, X.2⟩, hTU hX.1, Subtype.ext hXg⟩

theorem finrank_eq (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) {d : ℕ}
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hs : ∀ X, (X ∈ A ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℝ ↥(A ⊓ lieJ ε) = d := by
  have h1 : A ⊓ lieJ ε = Submodule.span ℝ (Set.range E) := Submodule.ext hs
  have h2 : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h := congrArg (fun Z => ((Z * (E k)ᴴ).trace).re) hc
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
      Complex.smul_re, hE] at h
    simpa using h
  rw [h1, finrank_span_eq_card h2, Fintype.card_fin]

open scoped Matrix.Norms.Frobenius in

theorem exists_limit (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (μ : Measure (algSub ε A hA)) [μ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun r : ℝ => (μ {g | Real.sqrt (Formalism.REAL.hs (uMat g.1 - 1)) ≤ r}).toReal /
        r ^ Module.finrank ℝ ↥(A ⊓ lieJ ε)) (𝓝[>] 0) (𝓝 c) := by
  let L₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have h := exists_limit_of_chart ↥(A ⊓ lieJ ε) (Matrix (Fin n) (Fin n) ℂ) (algSub ε A hA) μ
    (expSub ε A hA) (fun g => uMat g.1)
    (A ⊓ lieJ ε).subtypeₗᵢ (fun g => L₀ (uMat g.1)) (continuous_expSub ε A hA)
    (Subtype.ext (uMat_injective ε (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))))
    (HasStrictFDerivAt.comp (0 : ↥(A ⊓ lieJ ε)) (g := NormedSpace.exp) (f := Subtype.val)
      CompactDualExists.exp_strict (A ⊓ lieJ ε).subtypeL.hasStrictFDerivAt)
    (hL₀.comp ((continuous_uMat ε).comp continuous_subtype_val)).continuousAt
    (by ext1 A; exact Matrix.one_mul A) (fun g h => rfl)
    (fun r hr => expSub_image_mem_nhds ε A hA (ball_mem_nhds 0 hr))
    ((uJEmb n ε).1.isInducing.comp IsInducing.subtypeVal)
  simp only [sqrt_hs]
  exact h

theorem exists_isGaugeSub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  intro n ε A d E hA hE hs
  have hcl := isClosed_algSub ε A hA
  haveI : LocallyCompactSpace (algSub ε A hA) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb : MeasurableEmbedding (Subtype.val : algSub ε A hA → UJ ε) :=
    MeasurableEmbedding.subtype_coe hcl.measurableSet
  obtain ⟨c, hc, h⟩ := exists_limit ε A hA Measure.haar
  rw [finrank_eq ε A E hE hs] at h
  set B := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hBdef
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  have hB : 0 < B.toReal := ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' hBt
  have hq : 0 < B.toReal / c := div_pos hB hc
  set ν : Measure (algSub ε A hA) := (B.toReal / c).toNNReal • Measure.haar with hν
  haveI : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.2 hq).ne'
  haveI : SecondCountableTopology (algSub ε A hA) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨ν.map Subtype.val, hemb.sigmaFinite_map, ?_, fun s hs => ?_, ?_⟩
  · rw [hemb.map_apply]
    convert measure_empty (μ := ν)
    ext g
    exact ⟨fun hg => hg g.2, False.elim⟩
  · rw [Measure.map_map (measurable_const_mul s) hemb.measurable]
    conv_rhs => rw [← map_mul_left_eq_self ν (⟨s, hs⟩ : algSub ε A hA)]
    rw [Measure.map_map hemb.measurable (measurable_const_mul _)]
    rfl
  · have h1 := ENNReal.tendsto_ofReal (h.const_mul (B.toReal / c))
    rw [div_mul_cancel₀ _ hc.ne', ENNReal.ofReal_toReal hBt] at h1
    refine h1.congr' ?_
    filter_upwards [h.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with r h2 hr
    have hr' : (0 : ℝ) < r := hr
    have h3 := (ENNReal.toReal_pos_iff.1 ((div_pos_iff_of_pos_right (pow_pos hr' d)).1 h2)).2.ne
    rw [hemb.map_apply, hν, Measure.coe_nnreal_smul_apply, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_div_of_pos (pow_pos hr' d), ENNReal.ofReal_toReal h3, mul_div_assoc]
    rfl

end GlobalTheory.GaugeSubExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeight
section
open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Finset

namespace GlobalTheory.HaarWeight

theorem filter_lt_succ {p n : ℕ} (h : n < p) :
    (univ.filter fun b : Fin p => b.1 < n + 1) = insert ⟨n, h⟩ (univ.filter fun b : Fin p => b.1 < n) := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem filter_le_eq {p : ℕ} (a : Fin p) :
    (univ.filter fun b : Fin p => b ≤ a) = univ.filter fun b : Fin p => b.1 < a.1 + 1 := by
  ext b
  simp only [mem_filter, mem_univ, true_and, Fin.le_def]
  omega

private theorem one_le_partial_lemma (T : ℕ → ℝ) (m : ℕ → ℕ) (M p : ℕ) (hT : ∀ a, 0 ≤ T a)
    (hN : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T b) (hm : ∀ a, m a ≤ M) :
    ∀ k ≤ p, ∀ j ≤ M, (∏ b ∈ range k, T b) ^ j ≤
      (∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a := by
  intro k
  induction k with
  | zero => intro _ j _; simp
  | succ k ih =>
    intro hk j hj
    have hP1 : 1 ≤ ∏ b ∈ range (k + 1), T b := hN k (by omega)
    have hQ := ih (by omega) (m k) (hm k)
    have hnn : 0 ≤ (∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k :=
      mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (hT k) _)
    calc (∏ b ∈ range (k + 1), T b) ^ j ≤ (∏ b ∈ range (k + 1), T b) ^ (m k + M) :=
          pow_le_pow_right₀ hP1 (by have := hm k; omega)
      _ = (∏ b ∈ range k, T b) ^ m k * ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := by
          rw [pow_add, Finset.prod_range_succ]; ring
      _ ≤ ((∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a) *
            ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := mul_le_mul_of_nonneg_right hQ hnn
      _ = (∏ a ∈ range (k + 1), ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range (k + 1), T a ^ m a := by
          rw [Finset.prod_range_succ (fun a => ∏ b ∈ range (a + 1), T b),
            Finset.prod_range_succ (fun a => T a ^ m a)]
          ring

theorem one_le_partial {p : ℕ} (T : Fin p → ℝ) (m : Fin p → ℕ) (M : ℕ)
    (hN : ∀ a : Fin p, 1 ≤ ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) (hT : ∀ a, 0 ≤ T a)
    (hm : ∀ a, m a ≤ M) :
    1 ≤ (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) ^ M * ∏ a, T a ^ m a := by
  classical
  let T' : ℕ → ℝ := fun b => if h : b < p then T ⟨b, h⟩ else 1
  let m' : ℕ → ℕ := fun b => if h : b < p then m ⟨b, h⟩ else 0
  have hT' : ∀ b, 0 ≤ T' b := by
    intro b
    simp only [T']
    split_ifs
    · exact hT _
    · norm_num
  have hm' : ∀ b, m' b ≤ M := by
    intro b
    simp only [m']
    split_ifs
    · exact hm _
    · exact Nat.zero_le _
  have hTT : ∀ b : Fin p, T b = T' b := fun b => by simp [T', b.2]
  have hmm : ∀ b : Fin p, m b = m' b := fun b => by simp [m', b.2]
  have hpre : ∀ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b =
      ∏ b ∈ range (a.1 + 1), T' b := by
    intro a
    have ha := a.2
    rw [filter_le_eq, Finset.prod_filter]
    simp_rw [hTT]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < a.1 + 1 then T' i else 1) p, ← Finset.prod_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  have hN' : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T' b := fun a ha => (hpre ⟨a, ha⟩) ▸ hN ⟨a, ha⟩
  have key := one_le_partial_lemma T' m' M p hT' hN' hm' p le_rfl 0 (Nat.zero_le _)
  rw [pow_zero] at key
  have e1 : (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) =
      ∏ a ∈ range p, ∏ b ∈ range (a + 1), T' b := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ b ∈ range (i + 1), T' b) p]
    exact Finset.prod_congr rfl fun a _ => hpre a
  have e2 : (∏ a : Fin p, T a ^ m a) = ∏ a ∈ range p, T' a ^ m' a := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => T' i ^ m' i) p]
    exact Finset.prod_congr rfl fun a _ => by rw [hTT, hmm]
  rw [e1, e2]
  exact key

theorem sum_exponent {r : ℕ} (c : Composition (r + 1)) : ∀ n, n ≤ c.length →
    ∑ b ∈ univ.filter (fun b : Fin c.length => b.1 < n),
      (2 * r + 1 + c.blocksFun b - 2 * c.sizeUpTo (b.1 + 1)) * c.blocksFun b =
      c.sizeUpTo n * (2 * r + 1 - c.sizeUpTo n) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < c.length := by omega
    rw [filter_lt_succ hn', Finset.sum_insert (by simp), ih (by omega)]
    have hs := c.sizeUpTo_succ' ⟨n, hn'⟩
    have hle := c.sizeUpTo_le (n + 1)
    have hpos := c.one_le_blocksFun ⟨n, hn'⟩
    simp only at hs
    rw [hs] at hle ⊢
    generalize c.sizeUpTo n = x at hle ⊢
    generalize c.blocksFun ⟨n, hn'⟩ = y at hle hpos ⊢
    have h1 : x ≤ 2 * r + 1 := by omega
    have h2 : 2 * (x + y) ≤ 2 * r + 1 + y := by omega
    have h3 : x + y ≤ 2 * r + 1 := by omega
    zify [h1, h2, h3]
    ring

theorem endMin_sq {E : Type} [Field E] {r : ℕ} (rd : ℝ) (γ : PN.Pts E r) (a : Fin γ.1.length)
    (v : InfinitePlace E) :
    (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2 =
      ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
        ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * endIdx γ b))⁻¹ * v (γ.2 b)) ^ (2 * γ.1.blocksFun b) := by
  have ha := a.2
  have hsum := sum_exponent γ.1 (a.1 + 1) (by omega)
  rw [← filter_le_eq] at hsum
  unfold endIdx
  have hrd : ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * γ.1.sizeUpTo (b.1 + 1)))⁻¹) ^ (2 * γ.1.blocksFun b) =
      (rd ^ (2 * (γ.1.sizeUpTo (a.1 + 1) * (2 * r + 1 - γ.1.sizeUpTo (a.1 + 1)))))⁻¹ := by
    simp_rw [inv_pow, ← pow_mul]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← hsum, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun b _ => by ring
  have hmin : v (endMin γ a) ^ 2 = ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      v (γ.2 b) ^ (2 * γ.1.blocksFun b) := by
    unfold endMin Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [map_mul, map_pow]
    have hsg : v (((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign (γ.1.blocksFun b) : ℤ) : E)) = 1 := by
      rw [Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign]
      push_cast
      rw [map_pow]
      have hm1 : v (-1) = 1 := by
        have h1 : v (-1) * v (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
        have h0 : 0 ≤ v (-1) := by
          first
            | exact v.1.nonneg (-1)
            | exact apply_nonneg v (-1)
            | positivity
        nlinarith
      rw [hm1, one_pow]
    rw [hsg, one_mul, ← pow_mul, mul_comm]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, hrd, hmin]

theorem gram_pow_le_haar : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  intro E _ _ _ r k TT rd H γ hrd hN hD
  have hw0 : ∀ (w : InfinitePlace E) (x : E), 0 ≤ w x := fun w x => by
    first
      | exact w.1.nonneg x
      | exact apply_nonneg w x
      | positivity
  let Tw : Fin γ.1.length → InfinitePlace E → ℝ := fun a w =>
    (rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)
  let U : Fin γ.1.length → ℝ := fun a => ∏ w : InfinitePlace E, Tw a w ^ (2 * γ.1.blocksFun a)
  let mm : Fin γ.1.length → ℕ := fun a => 2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1
  have hTw : ∀ a w, 0 ≤ Tw a w := fun a w => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hU : ∀ a, 0 ≤ U a := fun a => Finset.prod_nonneg fun w _ => pow_nonneg (hTw a w) _
  have hNa : ∀ a, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b =
      ∏ w : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 := by
    intro a
    simp only [U]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun w _ => (endMin_sq rd γ a w).symm
  have hmM : ∀ a, mm a ≤ 6 * (2 * r + 2) := by
    intro a
    simp only [mm]
    have h1 := γ.1.sizeUpTo_le (a.1 + 1)
    have h2 := γ.1.sizeUpTo_succ' a
    unfold endIdx
    omega
  have key := one_le_partial U mm (6 * (2 * r + 2)) (fun a => by rw [hNa]; exact hN a) hU hmM
  have hND : (∏ a : Fin γ.1.length, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b) =
      NDPt rd γ := by
    unfold NDPt
    exact Finset.prod_congr rfl fun a _ => hNa a
  rw [hND] at key
  have hNDnn : 0 ≤ NDPt rd γ := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (pow_nonneg (hw0 _ _) _)
  have hY : ∏ a, U a ^ mm a = ∏ w : InfinitePlace E, ∏ a : Fin γ.1.length,
      Tw a w ^ (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1)) := by
    simp only [U, mm]
    simp_rw [← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
  have hn : nPt rd k TT γ = NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a := by
    rw [hY]
    unfold nPt NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hG0 : 0 ≤ NGPt rd TT γ := Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hYnn : 0 ≤ ∏ a, U a ^ mm a := Finset.prod_nonneg fun a _ => pow_nonneg (hU a) _
  have h1 : 1 ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
    calc 1 ≤ NDPt rd γ ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a := key
      _ ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNDnn hD _) hYnn
  rw [hn]
  calc NGPt rd TT γ ^ (k - 1) = NGPt rd TT γ ^ (k - 1) * 1 := (mul_one _).symm
    _ ≤ NGPt rd TT γ ^ (k - 1) * (H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hG0 _)
    _ = H ^ (6 * (2 * r + 2)) * (NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a) := by ring

end GlobalTheory.HaarWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem inv_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (g : Formalism.REAL.UJ ε) (hg : uMat g - 1 ∈ A) : uMat g⁻¹ - 1 ∈ A := by

  have hmap : ∀ W : A, uMat g * (W : Matrix (Fin n) (Fin n) ℂ) ∈ A := by
    intro W
    have : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = (uMat g - 1) * W + W := by noncomm_ring
    rw [this]
    exact A.add_mem (hA _ hg _ W.2) W.2
  let T : A →ₗ[ℝ] A :=
    LinearMap.codRestrict A ((LinearMap.mulLeft ℝ (uMat g)).comp A.subtype) hmap
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro W hW
    have h0 : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = 0 := congrArg Subtype.val hW
    apply Subtype.ext
    calc (W : Matrix (Fin n) (Fin n) ℂ) = uMat g⁻¹ * (uMat g * W) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨W, hW⟩ := (LinearMap.injective_iff_surjective (f := T)).mp hinj ⟨-(uMat g - 1), A.neg_mem hg⟩
  have hW' : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = -(uMat g - 1) := congrArg Subtype.val hW
  have hinv : uMat g⁻¹ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (1 + (W : Matrix (Fin n) (Fin n) ℂ))) := by
          rw [Matrix.mul_add, Matrix.mul_one, hW', show uMat g + -(uMat g - 1) = 1 by abel,
            Matrix.mul_one]
      _ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
  rw [hinv, add_sub_cancel_left]
  exact W.2

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      rw [uMat_mul]; noncomm_ring
    change uMat (g * h) - 1 ∈ A
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := fun {g} hg => inv_sub_one_mem A hA g hg

theorem isClosed_algSub (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (Formalism.REAL.UJ ε)) := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g - 1) :=
    (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  exact A.closed_of_finiteDimensional.preimage hc

end GlobalTheory.GaugeSubLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatouStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  first | exact @GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le | exact GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le | (intros; apply GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le <;> assumption)
end

