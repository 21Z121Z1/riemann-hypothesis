import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0039
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
section
open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

variable (L : Type) [Field L] [NumberField L]

def compAt (v : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) : v.adicCompletion L :=
  (a : AdeleRing (𝓞 L) L).2 v

theorem compAt_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (AdeleRing (𝓞 L) L)ˣ) :
    compAt L v (a * b) = compAt L v a * compAt L v b := rfl

theorem compAt_one (v : HeightOneSpectrum (𝓞 L)) : compAt L v 1 = 1 := rfl

def levSub (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) : Subgroup (AdeleRing (𝓞 L) L)ˣ where
  carrier := {a | ∀ v, Valued.v (compAt L v a) = 1 ∧ (v ∈ S → Valued.v (compAt L v a - 1) ≤ WithZero.exp (-(N : ℤ)))}
  one_mem' := fun v => by
    refine ⟨by rw [compAt_one, map_one], fun _ => ?_⟩
    rw [compAt_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := fun {a b} ha hb v => by
    rw [compAt_mul]
    refine ⟨by rw [map_mul, (ha v).1, (hb v).1, one_mul], fun hv => ?_⟩
    have e : compAt L v a * compAt L v b - 1 = compAt L v a * (compAt L v b - 1) + (compAt L v a - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((ha v).2 hv))
    rw [map_mul, (ha v).1, one_mul]
    exact (hb v).2 hv
  inv_mem' := fun {a} ha v => by
    have h1 : compAt L v a * compAt L v a⁻¹ = 1 := by rw [← compAt_mul, mul_inv_cancel, compAt_one]
    have hv1 : Valued.v (compAt L v a⁻¹) = 1 := by
      have := congrArg Valued.v h1
      rwa [map_mul, (ha v).1, one_mul, map_one] at this
    refine ⟨hv1, fun hv => ?_⟩
    have e : compAt L v a⁻¹ - 1 = -(compAt L v a⁻¹ * (compAt L v a - 1)) := by
      linear_combination h1
    rw [e, Valuation.map_neg, map_mul, hv1, one_mul]
    exact (ha v).2 hv

end GlobalTheory.LevelChars

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  classical
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : NeZero (Nat.card (G ⧸ H)) := ⟨Nat.card_pos.ne'⟩
  let f : {ψ : G →* ℂˣ | H ≤ ψ.ker} → (G ⧸ H → rootsOfUnity (Nat.card (G ⧸ H)) ℂ) := fun ψ q =>
    ⟨QuotientGroup.lift H ψ.1 ψ.2 q, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hf : Function.Injective f := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ h
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have := congrArg (fun F => ((F (QuotientGroup.mk g) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simpa [f] using this
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

theorem heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by
  intro L _ _ I _ φ n S N hS
  classical
  rcases Set.eq_empty_or_nonempty {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧
    ∀ v ∈ S, χ.LevelLe v N} with h | ⟨χ0, hχ0⟩
  · rw [h]; exact Set.finite_empty
  haveI := hC L S N hS
  refine ((finite_chars ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N)).preimage (f := fun χ : Formalism.L2.Host.HChar L => (χ * χ0⁻¹).1)
    (fun χ _ χ' _ h => mul_right_cancel (Subtype.ext h))).subset ?_
  intro χ hχ
  show _ ≤ MonoidHom.ker _
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA L S N (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one,
      one_mul]

end GlobalTheory.LevelChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEpsteinZetaContinuation
section
open Complex Filter Asymptotics

namespace GlobalTheory

open Set MeasureTheory
open scoped Topology

theorem summable_shiftedLattice_normSq_rpow (w₁ w₂ x₀ : ℂ)
    (h : (starRingEnd ℂ w₁ * w₂).im ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => (‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) ^ (-σ) := by
  have hli : ∀ a b : ℝ, a • w₁ + b • w₂ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg Complex.re hab
    have h2 := congrArg Complex.im hab
    simp at h1 h2 h
    have h' : w₁.re * w₂.im - w₁.im * w₂.re ≠ 0 := by
      intro h0; apply h; linarith
    constructor
    · apply mul_right_cancel₀ h'
      linear_combination w₂.im * h1 - w₂.re * h2
    · apply mul_right_cancel₀ h'
      linear_combination w₁.re * h2 - w₁.im * h1
  let L : PeriodPair := ⟨w₁, w₂, LinearIndependent.pair_iff.mpr hli⟩
  have hs := ZLattice.summable_norm_sub_rpow L.lattice (-(2 * σ)) (by simp; linarith) (-x₀)
  let φ : ℤ × ℤ → L.lattice := fun p =>
    ⟨p.1 * w₁ + p.2 * w₂, PeriodPair.mem_lattice.mpr ⟨p.1, p.2, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro p q hpq
    have e : (p.1 * w₁ + p.2 * w₂ : ℂ) = q.1 * w₁ + q.2 * w₂ := congrArg Subtype.val hpq
    have := hli (p.1 - q.1) (p.2 - q.2) (by simp; linear_combination e)
    simp only [sub_eq_zero, Int.cast_inj] at this
    exact Prod.ext this.1 this.2
  refine (hs.comp_injective hφ).congr fun p => ?_
  simp only [Function.comp, φ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  · congr 1; ring
  · push_cast; ring

theorem summable_exp_neg_pi_mul_of_summable_rpow {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) {t : ℝ} (ht : 0 < t) :
    Summable fun i => Real.exp (-Real.pi * t * q i) := by
  refine Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) (fun i => ?_)
    (hs.mul_left (2 / (Real.pi * t) ^ 2))
  have hx : 0 < Real.pi * t * q i := by have := hq i; positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx.le 2
  have h2 : -Real.pi * t * q i = -(Real.pi * t * q i) := by ring
  have h3 : (2 / (Real.pi * t) ^ 2) * q i ^ (-(2 : ℝ))
      = ((Real.pi * t * q i) ^ 2 / (Nat.factorial 2 : ℕ))⁻¹ := by
    have := hq i
    rw [Real.rpow_neg (hq i).le, Real.rpow_two]
    simp only [Nat.factorial_two, Nat.cast_ofNat]
    field_simp
  rw [h2, h3, Real.exp_neg]
  exact inv_anti₀ (by positivity) h1

theorem continuousOn_tsum_exp_neg_pi_mul {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) :
    ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t / 2 := half_pos ht
  have : ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi (t / 2)) := by
    refine continuousOn_tsum (fun i => by fun_prop)
      (summable_exp_neg_pi_mul_of_summable_rpow hq hs ht') fun i x hx => ?_
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have h1 : t / 2 < x := hx
    have := mul_pos (mul_pos Real.pi_pos (sub_pos.mpr h1)) (hq i)
    linarith
  exact (this.continuousAt (Ioi_mem_nhds (half_lt_self ht))).continuousWithinAt

theorem isBigO_exp_neg_div_rpow {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (fun t : ℝ => Real.exp (-c / t)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine ((isLittleO_exp_neg_mul_rpow_atTop hc b).isBigO.comp_tendsto
    tendsto_inv_nhdsGT_zero).congr' (.of_forall fun t => ?_)
    (eventually_mem_nhdsWithin.mono fun t ht => ?_)
  · simp [div_eq_mul_inv]
  · simp only [Function.comp]
    rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]

theorem exists_entire_dirichlet_of_theta {ι : Type*} [Countable ι] {q : ι → ℝ}
    (hq : ∀ i, 0 < q i) (hs : ∀ σ : ℝ, 1 < σ → Summable fun i => q i ^ (-σ)) {V c : ℝ}
    (hc : 0 < c)
    (htop : (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) =O[atTop]
      (fun t => Real.exp (-c * t)))
    (hbot : (fun t : ℝ => (∑' i, Real.exp (-Real.pi * t * q i)) - 1 / (t * V)) =O[𝓝[>] 0]
      (fun t => Real.exp (-c / t))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / V : ℝ) ∧ Z (-1) = 0 ∧
      ∀ s : ℂ, 1 < s.re → Summable (fun i => ((q i : ℝ) : ℂ) ^ (-s)) ∧
        Z s = (s - 1) * ∑' i, ((q i : ℝ) : ℂ) ^ (-s) := by
  set θ : ℝ → ℝ := fun t => ∑' i, Real.exp (-Real.pi * t * q i) with hθ
  have hθc : ContinuousOn θ (Ioi 0) := continuousOn_tsum_exp_neg_pi_mul hq (hs 2 one_lt_two)
  let g : ℝ → ℂ := indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-1 : ℂ))
  let A : ℂ := (V : ℂ)⁻¹
  let f : ℝ → ℂ := fun t => (θ t : ℂ) - A • g t
  have hfc : LocallyIntegrableOn f (Ioi 0) := by
    refine LocallyIntegrableOn.sub
      ((continuous_ofReal.comp_continuousOn hθc).locallyIntegrableOn measurableSet_Ioi)
      (LocallyIntegrableOn.smul ?_ A)
    have h0 : LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) :=
      ContinuousOn.locallyIntegrableOn (continuousOn_of_forall_continuousAt fun t ht =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)) measurableSet_Ioi
    intro x hx
    obtain ⟨u, hu, hu'⟩ := h0 x hx
    exact ⟨u, hu, hu'.indicator measurableSet_Ioc⟩
  have hftop : f =O[atTop] fun t => Real.exp (-c * t) := by
    refine (isBigO_ofReal_left.mpr htop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [f, g, indicator_of_notMem (fun h : t ∈ Ioc (0:ℝ) 1 => h.2.not_gt ht)]
  have hfbot : ∀ b : ℝ, f =O[𝓝[>] 0] fun t => t ^ (-b) := by
    intro b
    refine ((isBigO_ofReal_left.mpr hbot).congr' ?_ EventuallyEq.rfl).trans
      (isBigO_exp_neg_div_rpow hc b)
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [f, g, A, indicator_of_mem ht, cpow_neg_one, smul_eq_mul, θ]
    push_cast
    ring
  have hdiff : Differentiable ℂ (mellin f) := fun s =>
    mellin_differentiableAt_of_isBigO_rpow_exp hc hfc hftop (hfbot (s.re - 1)) (sub_one_lt _)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨fun s => (Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * ((s - 1) * mellin f s + A), ?_, ?_, ?_, ?_⟩
  · refine (Differentiable.mul (differentiable_id.const_cpow (Or.inl hpi))
      differentiable_one_div_Gamma).mul ?_
    exact ((differentiable_id.sub_const 1).mul hdiff).add_const A
  · simp [A, div_eq_mul_inv]
  · have : Gamma (-1) = 0 := by simpa using Gamma_neg_nat_eq_zero 1
    simp [this]
  · intro s hs1
    have hs0 : 0 < s.re := by linarith
    have hsum : HasSum (fun i => (Real.pi : ℂ) ^ (-s) * Gamma s * (1 : ℂ) / (q i : ℂ) ^ s)
        (mellin (fun t => (θ t : ℂ)) s) := by
      refine hasSum_mellin_pi_mul (a := fun _ => 1) (fun i => Or.inr (hq i)) hs0
        (fun t ht => ?_) ?_
      · have := (summable_exp_neg_pi_mul_of_summable_rpow hq (hs 2 one_lt_two) ht).hasSum
        rw [← hasSum_ofReal] at this
        convert this using 3 with i
        rw [one_mul]; congr 2; ring
      · refine (hs s.re hs1).congr fun i => ?_
        rw [Real.rpow_neg (hq i).le, norm_one, one_div]
    have hg := hasMellin_cpow_Ioc (-1) (s := s) (by simp; linarith)
    have hgA := hasMellin_const_smul hg.1 A
    have hfm : MellinConvergent f s :=
      mellinConvergent_of_isBigO_rpow_exp hc hfc hftop (hfbot 0) hs0
    have hadd := (hasMellin_add hfm hgA.1).2
    have e1 : (fun t => f t + A • g t) = fun t => (θ t : ℂ) := by
      funext t; simp [f]
    rw [hgA.2, hg.2] at hadd
    have hadd' : mellin (fun t => (θ t : ℂ)) s = mellin f s + A • (1 / (s + -1)) := by
      rw [← e1]; exact hadd
    have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
    have hp : (Real.pi : ℂ) ^ s ≠ 0 := by simp [cpow_eq_zero_iff]
    have hs1' : s - 1 ≠ 0 := by
      intro h0; rw [sub_eq_zero.mp h0] at hs1; simp at hs1
    have hsum2 : HasSum (fun i => ((q i : ℝ) : ℂ) ^ (-s))
        ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * mellin (fun t => (θ t : ℂ)) s) := by
      refine HasSum.congr_fun (hsum.mul_left ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹)) fun i => ?_
      rw [cpow_neg, cpow_neg]
      field_simp
    refine ⟨hsum2.summable, ?_⟩
    rw [hsum2.tsum_eq, hadd', ← sub_eq_add_neg, smul_eq_mul]
    field_simp

theorem epsteinZeta_shifted_continuation : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  intro w₁ w₂ x₀ h hx
  obtain ⟨c, hc, htop, hbot⟩ := GlobalTheory.T.lattice_theta_asymptotics w₁ w₂ x₀ h hx
  exact exists_entire_dirichlet_of_theta
    (q := fun p : ℤ × ℤ => ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)
    (fun p => pow_pos (norm_pos_iff.mpr (hx p.1 p.2)) 2)
    (fun σ hσ => summable_shiftedLattice_normSq_rpow w₁ w₂ x₀ h hσ) hc htop hbot

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBigCellIffCellDiscNeZero
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace Matrix

namespace GlobalTheory.FlagPts

theorem mem_span_tail_iff {W : Type} [AddCommGroup W] {k : Type} [Field k] [Module k W] {d : ℕ}
    (e : Basis (Fin d) k W) (m : ℕ) (v : W) :
    v ∈ Submodule.span k (e '' {a | m ≤ (a : ℕ)}) ↔ ∀ c : Fin d, (c : ℕ) < m → e.repr v c = 0 := by
  rw [Basis.mem_span_image]
  constructor
  · intro h c hc
    by_contra hne
    have := h (Finsupp.mem_support_iff.2 hne)
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro h c hc
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hc
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    exact hc (h c (by omega))

theorem truncMat_mulVec_eq_zero_iff {R : Type} [CommRing R] {d : ℕ} (m : ℕ)
    (M : Matrix (Fin d) (Fin d) R) (y : Fin d → R) :
    truncMat m M *ᵥ y = 0 ↔
      (∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) ∧ ∀ c : Fin d, (c : ℕ) < m → (M *ᵥ y) c = 0 := by
  have hlow (c : Fin d) (hc : (c : ℕ) < m) :
      (truncMat m M *ᵥ y) c = ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e := by
    simp only [Matrix.mulVec, dotProduct, truncMat]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : (e : ℕ) < m
    · simp [hc, he]
    · have hce : c ≠ e := fun h => he (h ▸ hc)
      simp [he, hce]
  have hhigh (c : Fin d) (hc : ¬ (c : ℕ) < m) : (truncMat m M *ᵥ y) c = y c := by
    simp only [Matrix.mulVec, dotProduct, truncMat]
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro e _ hec
      simp [hc, Ne.symm hec]
    · simp
  have hsum (h : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) (c : Fin d) :
      ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e = (M *ᵥ y) c := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : (e : ℕ) < m
    · simp [he]
    · simp [he, h e (by omega)]
  constructor
  · intro h
    have h1 : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0 := fun e he => by
      rw [← hhigh e (by omega)]; exact congrFun h e
    refine ⟨h1, fun c hc => ?_⟩
    rw [← hsum h1 c, ← hlow c hc]
    exact congrFun h c
  · rintro ⟨h1, h2⟩
    funext c
    by_cases hc : (c : ℕ) < m
    · rw [hlow c hc, hsum h1 c]; exact h2 c hc
    · rw [hhigh c hc]; exact h1 c (by omega)

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem repr_eq_frameMat_mulVec (b g : Frames k V) (i : ι) (v : V i) (c : Fin (finrank k (V i))) :
    (b i).repr v c = (frameMat b g i *ᵥ (g i).equivFun v) c := by
  have h := congrArg (fun w => (b i).repr w c) ((g i).sum_equivFun v)
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, frameMat]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem disjoint_step_iff_det_truncMat_ne_zero (b g : Frames k V) (i : ι) (m : ℕ) :
    Disjoint (g.flags.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)})) ↔
      (truncMat m (frameMat b g i)).det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff, Submodule.disjoint_def]
  constructor
  · rintro h ⟨y, hy0, hy⟩
    apply hy0
    rw [truncMat_mulVec_eq_zero_iff] at hy
    have hv : (g i).equivFun ((g i).equivFun.symm y) = y := LinearEquiv.apply_symm_apply _ _
    have h0 := h ((g i).equivFun.symm y)
      (mem_step_flags.2 fun a ha => by rw [← Basis.equivFun_apply, hv]; exact hy.1 a ha)
      ((mem_span_tail_iff (b i) m _).2 fun c hc => by
        rw [repr_eq_frameMat_mulVec b g, hv]; exact hy.2 c hc)
    rw [← hv, h0, map_zero]
  · intro h v hv1 hv2
    by_contra hv
    refine h ⟨(g i).equivFun v, fun h0 => hv ((g i).equivFun.map_eq_zero_iff.1 h0), ?_⟩
    rw [truncMat_mulVec_eq_zero_iff]
    refine ⟨fun e he => ?_, fun c hc => ?_⟩
    · rw [Basis.equivFun_apply]; exact mem_step_flags.1 hv1 e he
    · rw [← repr_eq_frameMat_mulVec b g]; exact (mem_span_tail_iff (b i) m v).1 hv2 c hc

theorem mem_bigCell_iff_cellDisc_ne_zero (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (b g : Frames k V) : g.flags ∈ bigCell b ↔ cellDisc b g ≠ 0 := by
  simp only [bigCell, Set.mem_setOf_eq, disjoint_step_iff_det_truncMat_ne_zero, cellDisc,
    Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h i m
    exact h i m
  · intro h i m
    by_cases hm : m ≤ finrank k (V i)
    · exact h i ⟨m, by omega⟩
    · have heq : truncMat m (frameMat b g i) = truncMat (finrank k (V i)) (frameMat b g i) := by
        ext c e
        have hc := c.2
        have he := e.2
        simp only [truncMat]
        rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨hc, he⟩]
      rw [heq]
      exact h i ⟨finrank k (V i), by omega⟩

example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b g : Frames k V),
    g.flags ∈ bigCell b ↔ cellDisc b g ≠ 0 := mem_bigCell_iff_cellDisc_ne_zero

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTensorResidueNonzeroOfSplitStatement
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rTensor_residue_nonzero_of_split : ∀ {O R k : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Field k] [Module.Free ℤ O] [Module.Finite ℤ O]
    (ρ₀ : R →+* k), (∀ x, ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal R) → ∀ (e : R ⊗[ℤ] O)
    (f : R ⊗[ℤ] O →ₗ[R] R), f e = 1 → ρ₀.toIntAlgHom.toLinearMap.rTensor O e ≠ 0 := by
  first | exact @GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one | exact GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one | (intros; apply GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplane
section
open Metric Filter Topology Set

namespace GlobalTheory

theorem riemann_extension_coordinate_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  intro n U k f hU hd hb
  refine ⟨fun z => if z k = 0 then limUnder (𝓝[≠] (0 : ℂ)) (fun t => f (Function.update z k t)) else f z,
    ?_, fun z _ hz => by simp [hz]⟩
  have hO : IsOpen {z : Fin n → ℂ | z ∈ U ∧ z k ≠ 0} :=
    hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases h0 : z₀ k = 0
  · obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hV)
    have hr : 0 < ε / 3 := by positivity
    have h2 : ball z₀ (2 * (ε / 3)) ⊆ U ∩ V := (ball_subset_ball (by linarith)).trans hball
    have hG := ((GlobalTheory.T.differentiableAt_coordinate_cauchy_integral n U k f z₀ (ε / 3) hr h0 hU
      ((closedBall_subset_ball (by linarith)).trans (hball.trans inter_subset_left)) hd).const_smul
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (GlobalTheory.T.cauchy_slice_eq_removable_extension n U k f z₀ (ε / 3) M hr h0 hU (h2.trans inter_subset_left) hd
      (fun z hz hzk => hM z (h2 hz).2 (h2 hz).1 hzk) z hz).symm
  · have hf : DifferentiableAt ℂ f z₀ := hd.differentiableAt (hO.mem_nhds ⟨hz₀, h0⟩)
    refine hf.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds ⟨hz₀, h0⟩] with z hz
    simp [hz.2]
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubsingletonJacquetIff
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CuspEntries

theorem blk_two_stdSum {r t N : ℕ} (h : r + t = N) (a : Fin N) :
    blk (two (stdSum h)) a = decide (r ≤ (a : ℕ)) := by
  obtain ⟨a, rfl⟩ := (stdSum h).surjective a
  rcases a with a | a
  · rw [← two_false, blk_apply, two_false]
    simp [stdSum]
  · rw [← two_true, blk_apply, two_true]
    simp [stdSum]

theorem mem_unipRad_two_stdSum {R : Type} [CommRing R] {r t N : ℕ} (h : r + t = N) (u : GL (Fin N) R) :
    u ∈ unipRad R (two (stdSum h)) ↔ ∀ a b : Fin N, ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) →
      (u : Matrix (Fin N) (Fin N) R) a b = (1 : Matrix (Fin N) (Fin N) R) a b := by
  rw [CuspMax.mem_unipRad_iff_entries]
  refine forall₂_congr fun a b => imp_congr_left (not_congr ?_)
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega

end GlobalTheory.CuspEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimAffinePointsStatement
section
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_affine_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J], topologicalKrullDim (AffPts k J) = (Fintype.card J : ℕ) := by
  first | exact @GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card | exact GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card | (intros; apply GlobalTheory.FlagPts.topologicalKrullDim_affPts_eq_card <;> assumption)
end

