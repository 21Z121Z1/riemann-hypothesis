import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Dec.TauExt

variable {n : ℕ} {ε : Fin n → Bool}

theorem conj_mul (a b : Matrix (Fin n) (Fin n) ℂ) : (a * b).map star = a.map star * b.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem conj_one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem conj_conj (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star).map star = a := by
  ext i j; simp

theorem conj_Jm : (Jm ε).map star = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; by_cases h' : ε i = true <;> simp [Jm, h']
  · simp [Jm, h]

theorem conj_mem {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k.map star ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have h : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
    have e : star (k.map star) = (star k).map star := by ext i j; simp
    rw [e, ← conj_mul, h, conj_one]
  · have := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hk.2
    simpa only [conj_mul, conj_Jm] using this

theorem mem_KC {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

theorem one_mem_K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem isOpen_units : IsOpen {y : Fin n → Fin n → ℂ | IsUnit (Matrix.of y)} := by
  simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isOpen_ne_fun (Continuous.matrix_det (A := fun y : Fin n → Fin n → ℂ => Matrix.of y) continuous_id)
    continuous_const

theorem conj_torus (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star =
      Matrix.diagonal fun a => Complex.exp (((-θ) a : ℂ) * Complex.I) := by
  rw [Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

section Mul

variable {B : Type} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] {τ : Matrix (Fin n) (Fin n) ℂ → B}

omit [CompleteSpace B] in
theorem differentiableOn_mul
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a) (hb : IsUnit b) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (a * Matrix.of y * b)) {y | Matrix.of y ∈ KC ε} := by
  have h : Differentiable ℂ fun y : Fin n → Fin n → ℂ => fun i j => (a * Matrix.of y * b) i j := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hd.comp h.differentiableOn fun y hy => (ha.mul hy.1).mul hb

theorem mul_on_KC
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    (hm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, τ (a * b) = τ a * τ b) :
    ∀ a ∈ KC ε, ∀ b ∈ KC ε, τ (a * b) = τ a * τ b := by
  have hd' : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | Matrix.of y ∈ KC ε} :=
    hd.mono fun y hy => hy.1
  have h1 : ∀ a ∈ Kset ε, ∀ b ∈ KC ε, τ (a * b * 1) - τ a * τ b = 0 := fun a ha =>
    GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' n ε B (fun y => τ (a * y * 1) - τ a * τ y)
      ((differentiableOn_mul hd (mem_KC ha).1 isUnit_one).sub (hd'.const_mul _))
      fun k hk => by rw [Matrix.mul_one, hm a ha k hk, sub_self]
  intro a ha b hb
  have h2 := GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' n ε B (fun y => τ (1 * y * b) - τ y * τ b)
    ((differentiableOn_mul hd isUnit_one hb.1).sub (hd'.mul_const _))
    (fun k hk => by simpa using h1 k hk b hb) a ha
  simpa [sub_eq_zero] using h2

end Mul

theorem adj_on_KC {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    (hK : ∀ y ∈ Kset ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ) :
    ∀ y ∈ KC ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ := by
  intro y hy u v
  have hc : ∀ u v : W, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => ⟪u, τ (Matrix.of y) v⟫_ℂ)
      {y | IsUnit (Matrix.of y)} := fun u v =>
    ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ W v)).differentiable.comp_differentiableOn hd
  have ht : Differentiable ℂ fun y : Fin n → Fin n → ℂ => fun i j => y j i := by fun_prop
  have h1 : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => star ⟪u, τ (Matrix.of y)ᴴ v⟫_ℂ)
      {y | Matrix.of y ∈ KC ε} := by
    intro z hz
    have hz' : IsUnit (Matrix.of fun i j => (star z) j i) := by
      exact hz.1.star
    have h2 := (((hc u v).differentiableAt (isOpen_units.mem_nhds hz')).comp (star z) (ht (star z))).star_star
    rw [star_star] at h2
    exact h2.differentiableWithinAt
  have h3 := GlobalTheory.T.eq_zero_on_KC_of_eq_zero_on_Kset' n ε ℂ (fun y => ⟪v, τ y u⟫_ℂ - star ⟪u, τ yᴴ v⟫_ℂ)
    (((hc v u).mono fun y hy => hy.1).sub h1)
    (fun k hk => by rw [← hK k hk, Complex.star_def, inner_conj_symm, sub_self]) y hy
  rw [← inner_conj_symm, sub_eq_zero.1 h3, Complex.star_def, Complex.conj_conj]

theorem tauExists : TauExists := by
  intro n ε abelian₂ H _ _ σ S w ⟨⟨h1, hmul⟩, hiso, hcont⟩ ⟨hfin, hst, hirr, _, hdom⟩ hw hwt
  classical
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  let π : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun k =>
    if h : k ∈ Kset ε then ((σ (k.map star)).comp S.subtypeL).codRestrict S
      fun v => hst _ (conj_mem h) _ v.2 else 0
  have hπ : ∀ k ∈ Kset ε, ∀ v : S, (π k v : H) = σ (k.map star) v := fun k hk v => by
    simp only [π, dif_pos hk]; rfl
  have hπ1 : π 1 = 1 := by
    ext v
    rw [hπ 1 one_mem_K, conj_one, h1]; rfl
  have hπm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, π (a * b) = π a * π b := by
    intro a ha b hb
    ext v
    rw [hπ _ (Kset_mul ε ha hb), conj_mul, hmul _ (conj_mem ha) _ (conj_mem hb), ContinuousLinearMap.mul_apply,
      hπ a ha, hπ b hb]
    rfl
  have hπc : ContinuousOn π (Kset ε) := by
    refine continuousOn_clm_apply.2 fun v => ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr ((hcont v).comp ?_ fun k hk => conj_mem hk) fun k hk => hπ k hk v
    exact (continuous_id.matrix_map continuous_star).continuousOn
  obtain ⟨τ, hd, hτ⟩ := GlobalTheory.T.holomorphic_extension_compact_rep n ε (S →L[ℂ] S) π hπ1 hπm hπc
  have hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v := fun k hk v => by
    rw [hτ k hk, hπ k hk]
  have hτ1 : τ 1 = 1 := by rw [hτ 1 one_mem_K, hπ1]
  have hτm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, τ (a * b) = τ a * τ b := fun a ha b hb => by
    rw [hτ _ (Kset_mul ε ha hb), hτ a ha, hτ b hb, hπm a ha b hb]
  have hrep : IsCRepOn (KC ε) τ := ⟨hτ1, mul_on_KC hd hτm⟩
  have hwτ : ∀ (μ : Fin n → ℝ) (v : S), IsWtOn (Kset ε) τ (-μ) v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
    intro μ v
    constructor
    · intro h θ hθ
      have hθ' := conj_mem hθ
      rw [conj_torus] at hθ'
      have := congrArg Subtype.val (h (-θ) hθ')
      rw [hτσ _ hθ', conj_torus, neg_neg] at this
      simpa using this
    · intro h θ hθ
      have hθ' := conj_mem hθ
      rw [conj_torus] at hθ'
      apply Subtype.ext
      rw [hτσ _ hθ, conj_torus, h (-θ) hθ']
      simp
  refine ⟨τ, ⟨hfin, hrep, fun u v => ?_, adj_on_KC hd fun k hk u v => ?_, fun S' hS' => ?_, hw,
    (hwτ abelian₂ w).2 hwt, ?_⟩, hτσ⟩
  · exact ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ S v)).differentiable.comp_differentiableOn
      (hd.mono fun y hy => hy.1)
  · have hk' : kᴴ ∈ Kset ε := Kset_star ε hk
    have hi : ∀ x : S, ‖τ k x‖ = ‖x‖ := fun x => by
      rw [Submodule.coe_norm, hτσ k hk, hiso _ (conj_mem hk), Submodule.coe_norm]
    have e : τ k (τ kᴴ v) = v := by
      have : k * kᴴ = 1 := Unitary.mul_star_self_of_mem hk.1
      rw [← ContinuousLinearMap.mul_apply, ← hτm k hk _ hk', this, hτ1]; rfl
    conv_lhs => rw [← e]
    exact LinearIsometry.inner_map_map ⟨(τ k).toLinearMap, hi⟩ u _
  · have hs : IsKStableOn ε σ (S'.map S.subtype) := by
      rintro g hg _ ⟨v, hv, rfl⟩
      refine ⟨τ (g.map star) v, hS' _ (conj_mem hg) v hv, ?_⟩
      have := hτσ _ (conj_mem hg) v
      rwa [conj_conj] at this
    rcases hirr _ (S.map_subtype_le S') hs with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · refine GlobalTheory.T.lowest_weight_vector_fixed_by_lower_unitriangular n ε abelian₂ S τ w hrep (hd.differentiableAt (isOpen_units.mem_nhds ?_))
      ((hwτ abelian₂ w).2 hwt) fun μ v hv h => hdom μ v v.2 (fun e => hv (Subtype.ext e)) ((hwτ μ v).1 h)
    exact (isUnit_one : IsUnit (1 : Matrix (Fin n) (Fin n) ℂ))

end GlobalTheory.Dec.TauExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralCompactLeQuotientMeasureBessel
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.LocEmb

variable {k r : ℕ}

theorem det_ne_zero_of_mem {g : Mat k r} (hg : g ∈ GG k r) : g.det ≠ 0 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact hH this.symm

theorem isClosed_GG : IsClosed (GG k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem continuousOn_inv : ContinuousOn (fun b : Mat k r => b⁻¹) {b | b.det ≠ 0} := by
  have : (fun b : Mat k r => b⁻¹) = fun b => (b.det)⁻¹ • b.adjugate := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun b hb => hb)
    continuous_id.matrix_adjugate.continuousOn

end GlobalTheory.SgInf.LocEmb

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LocEmb
variable {k r : ℕ}

def quotSet (K : Set (Mt k r)) : Set (Mt k r) :=
  (fun p : Mt k r × Mt k r => ((Matrix.of p.1 : Mat k r) * (Matrix.of p.2 : Mat k r)⁻¹ : Mat k r)) '' (K ×ˢ K)

theorem isCompact_quotSet {K : Set (Mt k r)} (hK : IsCompact K)
    (hd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0) : IsCompact (quotSet K) := by
  refine (hK.prod hK).image_of_continuousOn ?_
  have hc1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have hc2' : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have hc2 : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹) (K ×ˢ K) :=
    continuousOn_inv.comp hc2'.continuousOn fun p hp => hd p.2 hp.2
  exact hc1.continuousOn.mul hc2

end GlobalTheory.SgInf.LocEmb

theorem GlobalTheory.SgInf.lint_compact_le_quot : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r))
    (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS →
    IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F →
    (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  intro k r S μG μS ν K₀ hS hG hSH hU hQ hK₀
  set K : Set (Mt k r) := K₀ ∩ {x | (Matrix.of x : Mat k r) ∈ GG k r} with hKdef
  have hGc : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := LocEmb.isClosed_GG
  have hK : IsCompact K := hK₀.inter_right hGc
  have hKd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0 := fun x hx => LocEmb.det_ne_zero_of_mem hx.2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨μS (LocEmb.quotSet K), (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r S μS hS hSH).1 _ (LocEmb.isCompact_quotSet hK hKd), ?_⟩
  intro F hF hinv

  have hfib : ∀ x : Mt k r, ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
      μS (LocEmb.quotSet K) * F x := by
    intro x
    set A : Set (Mt k r) := {s | (Matrix.of s : Mat k r) ∈ S ∧
      (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K} with hA
    have h1 : ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
        ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := by
      refine lintegral_mono_ae ?_
      have hnull : μS {x | Matrix.of x ∉ S} = 0 := hSH.2.2.1
      filter_upwards [(ae_iff (p := fun s : Mt k r => (Matrix.of s : Mat k r) ∈ S)).2 hnull] with s hs'
      by_cases hsK : (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K
      · rw [Set.indicator_of_mem hsK, Set.indicator_of_mem (show s ∈ A from ⟨hs', hsK⟩)]
        exact le_of_eq (hinv _ hs' x)
      · rw [Set.indicator_of_notMem hsK]; simp
    have h2 : μS A ≤ μS (LocEmb.quotSet K) := by
      rcases A.eq_empty_or_nonempty with hAe | ⟨s₀, hs₀S, hs₀K⟩
      · rw [hAe, measure_empty]; simp
      set t : Mat k r := Matrix.of s₀ with ht
      have htS : t⁻¹ ∈ S := hS.2.2.2.2 _ hs₀S
      have hdx : (Matrix.of x : Mat k r).det ≠ 0 := by
        have := hKd _ hs₀K
        have h' : (Matrix.of (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r) : Mat k r) =
          (Matrix.of s₀ : Mat k r) * Matrix.of x := rfl
        rw [h', Matrix.det_mul] at this
        exact right_ne_zero_of_mul this
      have hsub : A ⊆ rmulM t⁻¹ ⁻¹' LocEmb.quotSet K := by
        intro s ⟨_, hsK⟩
        refine ⟨((fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r),
          (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r)), ⟨hsK, hs₀K⟩, ?_⟩
        show (Matrix.of s : Mat k r) * Matrix.of x * ((Matrix.of s₀ : Mat k r) * Matrix.of x)⁻¹ =
          (Matrix.of s : Mat k r) * t⁻¹
        rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of s : Mat k r),
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdx), Matrix.mul_one]
      calc μS A ≤ μS (rmulM t⁻¹ ⁻¹' LocEmb.quotSet K) := measure_mono hsub
        _ ≤ (μS.map (rmulM t⁻¹)) (LocEmb.quotSet K) :=
          Measure.le_map_apply (continuous_rmulM _).measurable.aemeasurable _
        _ = μS (LocEmb.quotSet K) := by rw [hU.1 _ htS]
    calc _ ≤ ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := h1
      _ ≤ F x * μS A := lintegral_indicator_const_le _ _
      _ ≤ F x * μS (LocEmb.quotSet K) := by gcongr
      _ = μS (LocEmb.quotSet K) * F x := mul_comm _ _
  have hnullG : μG {x | Matrix.of x ∉ GG k r} = 0 := hG.2.2.1
  calc ∫⁻ x in K₀, F x ∂μG = ∫⁻ x, K₀.indicator F x ∂μG :=
        (lintegral_indicator hK₀.isClosed.measurableSet F).symm
    _ ≤ ∫⁻ x, K.indicator F x ∂μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [(ae_iff (p := fun x : Mt k r => (Matrix.of x : Mat k r) ∈ GG k r)).2 hnullG] with x hx'
        by_cases h0 : x ∈ K₀
        · rw [Set.indicator_of_mem h0, Set.indicator_of_mem (show x ∈ K from ⟨h0, hx'⟩)]
        · rw [Set.indicator_of_notMem h0]; simp
    _ = ∫⁻ x, (∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν :=
        hQ _ (hF.indicator hKm)
    _ ≤ ∫⁻ x, μS (LocEmb.quotSet K) * F x ∂ν := lintegral_mono hfib
    _ = μS (LocEmb.quotSet K) * ∫⁻ x, F x ∂ν := lintegral_const_mul _ hF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.RadCov

section Defs

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

def lowers (F : ℕ → Submodule R (Fin n → K)) (c : ℕ) : Submodule R (Matrix (Fin n) (Fin n) K) where
  carrier := {T | ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b}
  zero_mem' := fun b y _ => by simp
  add_mem' := fun {S T} hS hT b y hy => by
    rw [Matrix.add_mulVec]
    exact add_mem (hS b y hy) (hT b y hy)
  smul_mem' := fun r T hT b y hy => by
    rw [Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (hT b y hy)

theorem mem_lowers {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {T : Matrix (Fin n) (Fin n) K} :
    T ∈ lowers F c ↔ ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b := Iff.rfl

def IsDualFlag [StarRing K] (J : Matrix (Fin n) (Fin n) K) (F : ℕ → Submodule R (Fin n → K)) (m : ℕ) : Prop :=
  Monotone F ∧ F 0 = ⊥ ∧ (∀ b, m ≤ b → F b = F m) ∧
    ∀ b, b ≤ m → ∀ y, y ∈ F (m - b) ↔ y ∈ F m ∧ ∀ x ∈ F b, star x ⬝ᵥ (J *ᵥ y) = 0

def Biorth (r : ℕ → ℕ) (m : ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) K)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) K) : Prop :=
  (∀ b, T' b * T b = 1) ∧ (∀ b b', b ≠ b' → T' b * T b' = 0) ∧ ∑ b ∈ Finset.range m, T b * T' b = 1

theorem lowers_succ_le {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) (c : ℕ) :
    lowers F (c + 1) ≤ lowers F c := by
  intro T hT
  rw [mem_lowers] at hT ⊢
  intro b y hy
  exact hT b y (hF (by omega) hy)

theorem lowers_anti {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) : Antitone (lowers F) :=
  antitone_nat_of_succ_le (lowers_succ_le hF)

theorem lowers_mul {F : ℕ → Submodule R (Fin n → K)} {c c' : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F c') : X * Y ∈ lowers F (c + c' + 1) := by
  rw [mem_lowers] at hX hY ⊢
  intro b y hy
  rw [← Matrix.mulVec_mulVec]
  apply hX b
  apply hY (b + c + 1)
  have e : b + c + 1 + c' + 1 = b + (c + c' + 1) + 1 := by omega
  rw [e]
  exact hy

theorem lowers_mul_zero {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F 0) :
    X * Y ∈ lowers F (c + 1) ∧ Y * X ∈ lowers F (c + 1) := by
  have h1 := lowers_mul hX hY
  have h2 := lowers_mul hY hX
  rw [Nat.add_zero] at h1
  rw [Nat.zero_add] at h2
  exact ⟨h1, h2⟩

theorem lowers_eq_bot {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (h0 : F 0 = ⊥)
    (hm : ∀ b, m ≤ b → F b = F m) (hsp : Submodule.span K (F m : Set (Fin n → K)) = ⊤) :
    lowers F m = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [mem_lowers] at hT
  have hzero : ∀ y ∈ (F m : Set (Fin n → K)), T *ᵥ y = 0 := by
    intro y hy
    have hy' : y ∈ F (0 + m + 1) := by
      rw [hm (0 + m + 1) (by omega)]
      exact hy
    have h := hT 0 y hy'
    rw [h0] at h
    exact (Submodule.mem_bot R).1 h
  have hlin : Matrix.toLin' T = 0 := by
    apply LinearMap.ext_on hsp
    intro y hy
    simpa [Matrix.toLin'_apply] using hzero y hy
  have hT0 : T = 0 := by
    apply Matrix.toLin'.injective
    rw [hlin, map_zero]
  exact (Submodule.mem_bot R).2 hT0

theorem lowers_adj [StarRing K] {J : Matrix (Fin n) (Fin n) K} (hJ : Jᴴ = J)
    {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (hF : IsDualFlag J F m) {c : ℕ}
    {T T' : Matrix (Fin n) (Fin n) K} (hT : T ∈ lowers F c) (hadj : J * T' = Tᴴ * J)
    (htop : ∀ y ∈ F m, T' *ᵥ y ∈ F m) : T' ∈ lowers F c := by
  obtain ⟨hmono, h0, hstab, hdual⟩ := hF
  have hleM : ∀ k, F k ≤ F m := by
    intro k
    rcases le_total k m with h | h
    · exact hmono h
    · exact (hstab k h).le
  rw [mem_lowers] at hT ⊢
  intro b y hy
  have hyM : y ∈ F m := hleM _ hy
  rcases le_total m b with hb | hb
  · rw [hstab b hb]
    exact htop y hyM
  ·
    have key : ∀ x ∈ F (m - b), star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = 0 := by
      intro x hx
      have e : star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = star (T *ᵥ x) ⬝ᵥ (J *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.star_mulVec]
      rw [e]
      rcases le_or_gt (b + c + 1) m with hc | hc
      · have hTx : T *ᵥ x ∈ F (m - (b + c + 1)) := by
          apply hT
          have e' : m - (b + c + 1) + c + 1 = m - b := by omega
          rw [e']
          exact hx
        have hy' : y ∈ F (m - (m - (b + c + 1))) := by
          rw [show m - (m - (b + c + 1)) = b + c + 1 by omega]
          exact hy
        exact ((hdual _ (Nat.sub_le _ _) y).1 hy').2 _ hTx
      ·
        have hTx : T *ᵥ x ∈ F 0 := hT 0 x (hmono (by omega) hx)
        rw [h0] at hTx
        rw [(Submodule.mem_bot R).1 hTx, star_zero, zero_dotProduct]
    have hd := hdual (m - b) (Nat.sub_le _ _) (T' *ᵥ y)
    rw [show m - (m - b) = b by omega] at hd
    exact hd.2 ⟨htop y hyM, key⟩

end Defs

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def locFlag (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun y : Fin n → E => P⁻¹ *ᵥ fun l => φ (y l)) '' (F b : Set _))

def PlaceMatch {ι : Type} (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Function.Bijective (fun v => InfinitePlace.mk (φ v)) ∧
    ∀ v, ((InfinitePlace.mk (φ v)).embedding = φ v ∧ X (InfinitePlace.mk (φ v)) = P v) ∨
      ((InfinitePlace.mk (φ v)).embedding = (starRingEnd ℂ).comp (φ v) ∧
        X (InfinitePlace.mk (φ v)) = (P v).map (starRingEnd ℂ))

def pieceHt [StarRing E] (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) : ℝ :=
  Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F (b + 1)) / Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F b)

def covStd (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ℝ :=
  GlobalTheory.FlagBase.covAt E j (GlobalTheory.FlagBase.latAt E j Λ fun _ a b => if a = b then 1 else 0)

end Loc

end GlobalTheory.RadCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSidesStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantMomentBound_both_sides : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S → MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧ MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  first | exact @GlobalTheory.Amp.MomBoth.momBd_both | exact GlobalTheory.Amp.MomBoth.momBd_both | (intros; apply GlobalTheory.Amp.MomBoth.momBd_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalFormStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_lebesgueCommonStabilizerNormalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → (lebR0 k r j β).map (conjM g₀) = lebR0 k r j β := by
  first | exact @GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero | exact GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero | (intros; apply GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumData_mass_be_eq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  first | exact @GlobalTheory.DefectShare.mass_defect_order_le | exact GlobalTheory.DefectShare.mass_defect_order_le | (intros; apply GlobalTheory.DefectShare.mass_defect_order_le <;> assumption)
end

