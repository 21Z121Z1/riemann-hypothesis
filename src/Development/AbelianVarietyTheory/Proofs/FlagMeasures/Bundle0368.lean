import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeak
section
open MeasureTheory Matrix Filter Topology

namespace GlobalTheory

theorem tendsto_integral_normalised_pow_peak :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  intro X _ _ _ _ μ hμ K x₀ f hK hKc hx₀ hpos hf hf1 hf01 hsep E _ _ _ F hF
  have hKae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hKc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hKae
  have hFm : AEStronglyMeasurable F μ := by
    have h := hF.aestronglyMeasurable_of_isCompact (μ := μ) hK hKm
    rwa [hμK] at h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ hx₀)

  have hfm_int : ∀ m : ℕ, Integrable (fun x => f x ^ m) μ := by
    intro m
    refine Integrable.of_bound (hf.pow m).aestronglyMeasurable 1 ?_
    filter_upwards [hKae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf01 x hx).1 m)]
    exact pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2

  have hlow : ∀ η : ℝ, 0 ≤ η → ∀ m : ℕ,
      η ^ m * μ.real {x | η < f x} ≤ ∫ y, f y ^ m ∂μ := by
    intro η hη m
    have hWm : MeasurableSet {x | η < f x} := measurableSet_lt measurable_const hf.measurable
    have h := integral_indicator_const (μ := μ) (η ^ m) hWm
    rw [smul_eq_mul] at h
    rw [mul_comm, ← h]
    refine integral_mono_ae ((integrable_const (η ^ m)).indicator hWm) (hfm_int m) ?_
    filter_upwards [hKae] with x hx
    by_cases hxW : x ∈ {x | η < f x}
    · rw [Set.indicator_apply, if_pos hxW]
      exact pow_le_pow_left₀ hη (le_of_lt hxW) m
    · rw [Set.indicator_apply, if_neg hxW]
      exact pow_nonneg (hf01 x hx).1 m
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨u, hu_open, hx₀u, hu⟩ :=
    mem_nhdsWithin.mp ((hF x₀ hx₀) (Metric.ball_mem_nhds (F x₀) (half_pos hε)))
  obtain ⟨δ, hδ1, hδ⟩ := hsep u (hu_open.mem_nhds hx₀u)
  obtain ⟨d, hd0, hd1, hδd⟩ : ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ δ ≤ d :=
    ⟨max δ 0, le_max_right _ _, max_lt hδ1 one_pos, le_max_left _ _⟩
  obtain ⟨η, hη0, hdη, hη1⟩ : ∃ η : ℝ, 0 < η ∧ d < η ∧ η < 1 :=
    ⟨(d + 1) / 2, by linarith, by linarith, by linarith⟩
  have hWpos : 0 < μ {x | η < f x} :=
    hpos _ (isOpen_lt continuous_const hf) (by show η < f x₀; rw [hf1]; exact hη1)
  have hW : 0 < μ.real {x | η < f x} := ENNReal.toReal_pos hWpos.ne' (measure_ne_top μ _)
  have hr : Tendsto (fun m : ℕ => (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x})
      atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd0 hη0.le)
      ((div_lt_one hη0).mpr hdη)).const_mul (2 * C + 1)).div_const (μ.real {x | η < f x})
    simpa using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hr (Iio_mem_nhds (half_pos hε)))
  refine ⟨N, fun m hm => ?_⟩
  have hIpos : 0 < ∫ y, f y ^ m ∂μ :=
    lt_of_lt_of_le (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  set c : X → ℂ := fun x => ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) with hc
  have hc_cont : Continuous c :=
    Complex.continuous_ofReal.comp ((hf.pow m).div_const _)
  have hcnorm : ∀ x ∈ K, ‖c x‖ = f x ^ m / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hc, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le)]
  have hcle : ∀ x ∈ K, ‖c x‖ ≤ 1 / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hcnorm x hx]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2) hIpos.le
  have hc_int : Integrable c μ := by
    refine Integrable.of_bound hc_cont.aestronglyMeasurable (1 / ∫ y, f y ^ m ∂μ) ?_
    filter_upwards [hKae] with x hx
    exact hcle x hx
  have hcF_int : Integrable (fun x => c x • F x) μ := by
    refine Integrable.of_bound (hc_cont.aestronglyMeasurable.smul hFm)
      (1 / (∫ y, f y ^ m ∂μ) * C) ?_
    filter_upwards [hKae] with x hx
    rw [norm_smul]
    exact mul_le_mul (hcle x hx) (hC x hx) (norm_nonneg _) (by positivity)

  have hint1 : ∫ x, c x ∂μ = 1 := by
    show ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_div, div_self hIpos.ne', Complex.ofReal_one]
  have hkey : (∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) - F x₀
      = ∫ x, c x • (F x - F x₀) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hcF_int (hc_int.smul_const (F x₀)), integral_smul_const, hint1, one_smul]
  set B : ℝ := (2 * C + 1) * d ^ m / ∫ y, f y ^ m ∂μ with hB
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (by linarith) (pow_nonneg hd0 m)) hIpos.le
  have hbound : ∀ᵐ x ∂μ, ‖c x • (F x - F x₀)‖
      ≤ (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B := by
    filter_upwards [hKae] with x hx
    have h0 : 0 ≤ f x ^ m / ∫ y, f y ^ m ∂μ :=
      div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le
    rw [norm_smul, hcnorm x hx]
    by_cases hxu : x ∈ u
    · have hlt : ‖F x - F x₀‖ < ε / 2 := by
        have h := hu ⟨hxu, hx⟩
        simpa [dist_eq_norm] using h
      have := mul_le_mul_of_nonneg_left hlt.le h0
      linarith
    · have hfx : f x ≤ d := le_trans (hδ x hx hxu) hδd
      have hpow : f x ^ m ≤ d ^ m := pow_le_pow_left₀ (hf01 x hx).1 hfx m
      have hFd : ‖F x - F x₀‖ ≤ 2 * C + 1 := by
        have := norm_sub_le (F x) (F x₀)
        linarith [hC x hx, hC x₀ hx₀]
      have h1 : f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖ ≤ B := by
        calc f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖
            = (‖F x - F x₀‖ * f x ^ m) / ∫ y, f y ^ m ∂μ := by ring
          _ ≤ ((2 * C + 1) * d ^ m) / ∫ y, f y ^ m ∂μ :=
            div_le_div_of_nonneg_right
              (mul_le_mul hFd hpow (pow_nonneg (hf01 x hx).1 m) (by linarith)) hIpos.le
      have h2 : 0 ≤ f x ^ m / (∫ y, f y ^ m ∂μ) * (ε / 2) := mul_nonneg h0 (by linarith)
      linarith
  have hBle : B ≤ (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x} := by
    rw [hB, div_pow, mul_div_assoc', div_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (pow_nonneg hd0 m))
      (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  have hBlt : B < ε / 2 := lt_of_le_of_lt hBle (hN m hm)
  have hg_int : Integrable (fun x => (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) μ :=
    (((hfm_int m).div_const _).mul_const _).add (integrable_const _)
  rw [dist_eq_norm, hkey]
  calc ‖∫ x, c x • (F x - F x₀) ∂μ‖
      ≤ ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) ∂μ :=
        norm_integral_le_of_norm_le hg_int hbound
    _ = ε / 2 + B := by
        rw [integral_add (((hfm_int m).div_const _).mul_const _) (integrable_const _),
          integral_mul_const, integral_div, div_self hIpos.ne', integral_const]
        simp
    _ < ε := by linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevel
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.DualMod

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst)

theorem hform_mulVec_conj {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have hd : ∀ (J : Matrix n n A) (x y : n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
    intro J x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [hd, hd, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hA_unitary (x : I.Gf) (u v : VA I) : hA I (I.fmat x *ᵥ u) (I.fmat x *ᵥ v) = hA I u v := by
  have h : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hA
  rw [hform_mulVec_conj, h]

theorem zmod_add {g : ℕ} {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) :
    ZMod' I g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, by ring⟩

theorem zmod_mul {g : ℕ} {a c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) :
    ZMod' I g (c * a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  exact ⟨c * s, mul_mem hc hs, by ring⟩

theorem zmod_zero (g : ℕ) : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by simp [hA, Formalism.UG.hform]
theorem hA_zero_right (y : VA I) : hA I y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mL_left {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I m y) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_left, map_natCast]
    exact ⟨hA I x y, hA_int I hx hy, rfl⟩
  | zero => rw [hA_zero_left]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_left]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I ((c : I.E ⊗[I.F] Af I.F) • a) y)
    rw [hA_smul_left]; exact zmod_mul I (sigA_mem I c.2) ha

theorem hA_mL_right {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I y m) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_right]
    exact ⟨hA I y x, hA_int I hy hx, rfl⟩
  | zero => rw [hA_zero_right]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_right]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I y ((c : I.E ⊗[I.F] Af I.F) • a))
    rw [hA_smul_right]; exact zmod_mul I c.2 ha

theorem mL_le (g : ℕ) : mL I g ≤ I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hx g

end Gen

theorem dual_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  intro D X u wt ιA hW hι c p b bd hb hbd hm i j
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hι
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1
  have hYd : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).2
  have hm1 : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j ∈ mL X.B.I X.B.g := by
    rw [hb j]; exact (hm j).1
  have hm2 : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g := by
    rw [hbd i]; exact (hm i).2
  have key : ZMod' X.B.I X.B.g
      (hA X.B.I (embA X wt ιA (bd i)) (embA X wt ιA (b j)) - if i = j then X.ew else 0) := by
    generalize hm' : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j = m' at hm1
    generalize hmm : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i = m at hm2
    have e1 : embA X wt ιA (b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j + m' := by rw [← hm']; abel
    have e2 : embA X wt ιA (bd i) = X.B.I.fmat (X.xu u) *ᵥ X.bwd i + m := by rw [← hmm]; abel
    rw [e1, e2, hA_add_left, hA_add_right, hA_add_right, hA_unitary]
    have e3 : hA X.B.I (X.bwd i) (X.bw j) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
        (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') - (if i = j then X.ew else 0) =
        (hA X.B.I (X.bwd i) (X.bw j) - (if i = j then X.ew else 0)) +
          hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
          (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') := by ring
    rw [e3]
    refine zmod_add _ (zmod_add _ (X.bw_dual i j) (hA_mL_right _ hm1 (hYd i)))
      (zmod_add _ (hA_mL_left _ hm2 (hY j)) (hA_mL_left _ hm2 (mL_le _ _ hm1)))
  obtain ⟨t, ht, he⟩ := key
  refine ⟨ιA t, (hι.2 t).1 ht, ?_⟩
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) =
      ιA (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [map_natCast, X.g_eq]
  have hif : (if i = j then ιA X.ew else 0) = ιA (if i = j then X.ew else 0) := by
    split_ifs <;> simp
  rw [← h2, hg, hif, ← map_sub, he, map_mul]

end GlobalTheory.St.G.DualMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurable
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem yv_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  intro k r z z' γ hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yv k r z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r r z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z' (Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z').2.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z (γ * Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z).2.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset k r z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yv k r z z' γ (Matrix.of x.1) ∧ Yv k r z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakProperties
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem sum_normSq_col {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (i : Fin n) :
    ∑ j, ‖g j i‖ ^ 2 = 1 := by
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg
  have h2 : (star g * g) i i = 1 := by rw [h1]; simp
  rw [Matrix.mul_apply] at h2
  have h3 : ((∑ j, ‖g j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h3

theorem norm_entry_le_one {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (j i : Fin n) :
    ‖g j i‖ ≤ 1 := by
  have h := sum_normSq_col hg i
  have h2 : ‖g j i‖ ^ 2 ≤ ∑ j, ‖g j i‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖g j i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  rw [h] at h2
  nlinarith [norm_nonneg (g j i)]

theorem re_trace_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace g).re = ∑ i, (g i i).re := by
  simp [Matrix.trace, Complex.re_sum]

theorem eq_one_of_re_trace {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))
    (ht : (Matrix.trace g).re = n) : g = 1 := by
  have hle : ∀ i, (g i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans (norm_entry_le_one hg i i)
  have hsum : ∑ i : Fin n, (1 - (g i i).re) = 0 := by
    rw [Finset.sum_sub_distrib, ← re_trace_eq, ht]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))).1 hsum
  have hre : ∀ i, (g i i).re = 1 := fun i => by
    have := hz i (Finset.mem_univ i)
    linarith
  have hnorm : ∀ i, ‖g i i‖ = 1 := fun i => le_antisymm (norm_entry_le_one hg i i)
    (by simpa [hre i] using Complex.re_le_norm (g i i))
  have hdiag : ∀ i, g i i = 1 := fun i => by
    have h1 : ‖g i i‖ ^ 2 = (g i i).re ^ 2 + (g i i).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hnorm i, hre i] at h1
    have him : (g i i).im = 0 := by nlinarith
    exact Complex.ext (by simpa using hre i) (by simpa using him)
  ext j i
  by_cases hji : j = i
  · subst hji
    simp [hdiag j]
  · have hs := sum_normSq_col hg i
    have h0 : ∑ k ∈ Finset.univ.erase i, ‖g k i‖ ^ 2 = 0 := by
      have := Finset.add_sum_erase Finset.univ (fun k => ‖g k i‖ ^ 2) (Finset.mem_univ i)
      rw [hs, hnorm i] at this
      linarith
    have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h0
    have := hz2 j (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
    have hn : ‖g j i‖ = 0 := by simpa using this
    rw [Matrix.one_apply_ne hji]
    exact norm_eq_zero.1 hn

theorem peak_continuous (n : ℕ) : Continuous (peak n) := by
  unfold peak
  have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace g).re :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  fun_prop

theorem peak_one {n : ℕ} (hn : 0 < n) : peak n 1 = 1 := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [peak, Matrix.trace_one, this]

theorem abs_re_trace_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    |(Matrix.trace g).re| ≤ n := by
  rw [re_trace_eq]
  calc |∑ i, (g i i).re| ≤ ∑ i, |(g i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (norm_entry_le_one hg i i)
    _ = n := by simp

theorem peak_mem_Icc {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    0 ≤ peak n g ∧ peak n g ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_le.1 (abs_re_trace_le hg)
  have h1 : -1 ≤ (Matrix.trace g).re / n := by
    rw [le_div_iff₀ hn']; linarith [h.1]
  have h2 : (Matrix.trace g).re / n ≤ 1 := by
    rw [div_le_iff₀ hn']; linarith [h.2]
  unfold peak
  constructor <;> linarith

theorem peak_lt_one {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (h1 : g ≠ 1) :
    peak n g < 1 := by
  refine lt_of_le_of_ne (peak_mem_Icc hn hg).2 fun he => h1 (eq_one_of_re_trace hg ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold peak at he
  have : (Matrix.trace g).re / n = 1 := by linarith
  field_simp at this
  linarith

theorem peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧
    (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
      0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧
    ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1,
      ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
        g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  intro n hn
  refine ⟨peak_continuous n, peak_one hn, fun g hg => peak_mem_Icc hn hg, fun U hU => ?_⟩
  have hK : IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) :=
    (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).inter_right isOpen_interior.isClosed_compl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  rcases Set.eq_empty_or_nonempty
      ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) with he | hne
  · refine ⟨0, by norm_num, fun g hg hgU => ?_⟩
    have : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ :=
      ⟨hg, fun hi => hgU (interior_subset hi)⟩
    rw [he] at this
    exact this.elim
  · obtain ⟨g₀, hg₀, hmax⟩ := hK.exists_isMaxOn hne (peak_continuous n).continuousOn
    have hne1 : g₀ ≠ 1 := fun h => hg₀.2 (h ▸ h1)
    refine ⟨peak n g₀, peak_lt_one hn hg₀.1 hne1, fun g hg hgU => ?_⟩
    exact hmax ⟨hg, fun hi => hgU (interior_subset hi)⟩

end GlobalTheory.KFinAvg
end
end

