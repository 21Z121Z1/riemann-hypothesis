import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
import Formalism.HermitianCurvature.Bundle0006
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.StatementTL

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRealisation
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section L2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gramL {ι : Type} (μ : Measure ℂ) (F G : ι × ℂ → ℂ → H) (p q : ι × ℂ) : ℂ :=
  ∫ D, ⟪F p D, G q D⟫_ℂ ∂μ

theorem inner_toLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ D, ⟪f D, g D⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun D => ⟪f D, g D⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem blockPSD_gramL {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H)
    (memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ)
    (memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ) (Xs : Finset ℂ) (hXs : ∀ x ∈ Xs, x ≠ 0) :
    KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A) := by
  have hmem : ∀ p ∈ Y ×ˢ Xs, MemLp (U p) 2 μ ∧ MemLp (A p) 2 μ := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hx := hXs _ hp.2
    exact ⟨memU _ hp.1 _ hx, memA _ hp.1 _ hx⟩
  let v : {x // x ∈ (Y ×ˢ Xs).disjSum (Y ×ˢ Xs)} → Lp H 2 μ := fun x =>
    Sum.elim (fun p => if hp : MemLp (U p) 2 μ then hp.toLp (U p) else 0)
      (fun q => if hq : MemLp (A q) 2 μ then hq.toLp (A q) else 0) x.1
  unfold KB.BlockPSD TB.PSDOn
  open scoped ComplexOrder in
  refine (congrArg Matrix.PosSemidef ?_).mpr (Matrix.posSemidef_gram ℂ v)
  ext i j
  obtain ⟨x, hx⟩ := i
  obtain ⟨y, hy⟩ := j
  rcases x with p | q <;> rcases y with p' | q'
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2,
      inner_toLp h1 h2, gramL]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2, gramL]
    rw [← inner_conj_symm, inner_toLp h2 h1]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inr, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]

theorem exists_compact_tail (μ : Measure ℂ) [NullSingletonClass μ] (φ : ℂ → ℝ) (hφ : Integrable φ μ) (η : ℝ) (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D in Kᶜ, φ D ∂μ < η := by
  let K : ℕ → Set ℂ := fun n => {D | ((n : ℝ) + 1)⁻¹ ≤ ‖D‖ ∧ ‖D‖ ≤ (n : ℝ) + 1}
  have hKc : ∀ n, IsCompact (K n) := fun n => by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1)).subset fun D hD => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hD.2
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n h => by
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.mpr (by positivity))
  have hmono : Monotone K := by
    intro m n hmn D hD
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
    exact ⟨le_trans (inv_anti₀ (by positivity) h) hD.1, hD.2.trans h⟩
  have hKm : ∀ n, MeasurableSet (K n)ᶜ := fun n => (hKc n).isClosed.measurableSet.compl
  have hanti : Antitone fun n => (K n)ᶜ := fun m n h => Set.compl_subset_compl.mpr (hmono h)
  have hinter : ⋂ n, (K n)ᶜ = {0} := by
    ext D
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hD
      obtain ⟨n, hn⟩ := exists_nat_ge (max ‖D‖ ‖D‖⁻¹)
      have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
      apply h n
      refine ⟨?_, ?_⟩
      · have h1 : ‖D‖⁻¹ ≤ (n : ℝ) + 1 :=
          (le_max_right _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
        exact inv_le_of_inv_le₀ hpos h1
      · exact (le_max_left _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
    · rintro rfl n
      exact hK0 n
  have ht := tendsto_setIntegral_of_antitone hKm hanti ⟨0, hφ.integrableOn⟩
  have h0 : ∫ x in ({0} : Set ℂ), φ x ∂μ = 0 := by
    rw [Measure.restrict_eq_zero.mpr (measure_singleton 0), integral_zero_measure]
  rw [hinter, h0] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨K n, hKc n, hK0 n, hn⟩

theorem tendsto_integral_inner_germ {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB1p : 0 < max B 0 + 1 := by positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = ε / (4 * (max B 0 + 1)) := ⟨_, rfl⟩
  have hlamp : 0 < lam := by rw [hlam]; positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := (memLp_two_iff_integrable_sq hg.1).1 hg
  obtain ⟨K, hK, h0K, hKt⟩ := exists_compact_tail μ _ hg2 (lam * ε / 2) (by positivity)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hgK : IntegrableOn (fun D => |g D|) K μ := ((hg.restrict K).integrable one_le_two).abs
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ D in K, |g D| ∂μ := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hI]; exact setIntegral_nonneg hKm fun D _ => abs_nonneg _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * (I + 1)) := ⟨_, rfl⟩
  have hδp : 0 < δ := by rw [hδ]; positivity
  filter_upwards [hF, hG, hloc K hK h0K δ hδp] with x hFx hGb hFK
  obtain ⟨hFm, hFB⟩ := hFx
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hFm.1).1 hFm
  have i1 : Integrable (fun D => δ * K.indicator (fun D => |g D|) D) μ :=
    (hgK.integrable_indicator hKm).const_mul δ
  have i2 : Integrable (fun D => lam * ‖F x D‖ ^ 2) μ := hF2.const_mul lam
  have i3 : Integrable (fun D => Kᶜ.indicator (fun D => g D ^ 2) D / lam) μ :=
    (hg2.indicator hKm.compl).div_const lam
  have i4 : Integrable (fun D => (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) μ :=
    (i2.add i3).div_const 2
  have hpt : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤ δ * K.indicator (fun D => |g D|) D +
      (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2 := by
    filter_upwards [hGb, hFK] with D hb hk
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * g D :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    have hg0 : 0 ≤ g D := (norm_nonneg _).trans hb
    by_cases hDK : D ∈ K
    · have hFD := hk hDK
      rw [Set.indicator_of_mem hDK, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hDK), abs_of_nonneg hg0]
      have : ‖F x D‖ * g D ≤ δ * g D := mul_le_mul_of_nonneg_right hFD hg0
      have : 0 ≤ lam * ‖F x D‖ ^ 2 := by positivity
      have : (lam * ‖F x D‖ ^ 2 + 0 / lam) / 2 ≥ 0 := by rw [zero_div, add_zero]; positivity
      linarith
    · rw [Set.indicator_of_notMem hDK, Set.indicator_of_mem (Set.mem_compl hDK)]
      have key : lam * ‖F x D‖ ^ 2 + g D ^ 2 / lam - 2 * (‖F x D‖ * g D) = (lam * ‖F x D‖ - g D) ^ 2 / lam := by
        field_simp
        ring
      have : 0 ≤ (lam * ‖F x D‖ - g D) ^ 2 / lam := by positivity
      have : δ * 0 = 0 := mul_zero δ
      linarith
  have hInt : ∫ D, (δ * K.indicator (fun D => |g D|) D +
      (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) ∂μ =
      δ * I + (lam * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D in Kᶜ, g D ^ 2 ∂μ) / lam) / 2 := by
    rw [integral_add i1 i4, integral_const_mul, integral_indicator hKm, integral_div, integral_add i2 i3,
      integral_const_mul, integral_div, integral_indicator hKm.compl, hI]
  have e1 : δ * I ≤ ε / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e2 : lam * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hle : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ max B 0 + 1 := by linarith [le_max_left B 0]
    calc lam * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ lam * (max B 0 + 1) := mul_le_mul_of_nonneg_left hle hlamp.le
      _ = ε / 4 := by rw [hlam]; field_simp
  have e3 : (∫ D in Kᶜ, g D ^ 2 ∂μ) / lam < ε / 2 := by
    rw [div_lt_iff₀ hlamp]
    linarith
  calc ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ ∫ D, ‖⟪F x D, G x D⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ D, (δ * K.indicator (fun D => |g D|) D +
        (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (i1.add i4) hpt
    _ = _ := hInt
    _ < ε := by linarith

end L2

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieListProducts

theorem alg_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : ℂ) (A₁ A₂ : M) :
    (a • A₁ - b • A₂) + Complex.I • (a • A₂ + b • A₁) = (a + b * Complex.I) • (A₁ + Complex.I • A₂) := by
  have h : Complex.I • Complex.I • A₂ = -A₂ := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [smul_add, add_smul, mul_smul, h]
  module

theorem alg_bracket {R : Type*} [Ring R] [Algebra ℂ R] (A₁ A₂ B₁ B₂ : R) :
    (A₁ + Complex.I • A₂) * (B₁ + Complex.I • B₂) - (B₁ + Complex.I • B₂) * (A₁ + Complex.I • A₂) =
      ((A₁ * B₁ - B₁ * A₁) - (A₂ * B₂ - B₂ * A₂)) + Complex.I • ((A₁ * B₂ - B₂ * A₁) + (A₂ * B₁ - B₁ * A₂)) := by
  have h : ∀ x : R, Complex.I • Complex.I • x = -x := fun x => by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, h]
  module

section Lie

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem lie_zero : InLieW k r z 0 := by
  refine ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩

theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    have h1 := hX.1.1
    have h2 := hY.1.1
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).1, (hY.1.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).2, (hY.1.2 a ha).2, add_zero]
  · rw [Matrix.add_mulVec, hX.2, hY.2, add_zero]

theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
    rw [this, ← smul_add, hX.1.1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).2, smul_zero]
  · rw [Matrix.smul_mulVec, hX.2, smul_zero]

theorem lie_sub {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X - Y) := by
  have := lie_add hX (lie_smul hY (-1))
  simpa [sub_eq_add_neg] using this

theorem conj_lie {X : Mx k r} (hX : InLieW k r z X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have h : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1.1
  rw [Qx8.hpk_inv, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.one_mul]

theorem hpart1_lie {X : Mx k r} (hX : InLieW k r z X) : hpart1 (Hpk k r) X = X := by
  unfold hpart1
  rw [conj_lie hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_lie {X : Mx k r} (hX : InLieW k r z X) : hpart2 (Hpk k r) X = 0 := by
  unfold hpart2
  rw [conj_lie hX, add_neg_cancel, smul_zero]

theorem hpart1_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart1 (Hpk k r) (X₁ + Complex.I • X₂) = X₁ := by
  rw [CapelliCoordinates.hpart1_add, CapelliCoordinates.hpart1_smul, hpart1_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hpart2_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart2 (Hpk k r) (X₁ + Complex.I • X₂) = X₂ := by
  rw [CapelliCoordinates.hpart2_add, CapelliCoordinates.hpart2_smul, hpart2_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hsum (Z : Mx k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp [Complex.I_ne_zero]
  rw [e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem gl_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    InGlW k r z (X₁ + Complex.I • X₂) := by
  unfold InGlW
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]
  exact ⟨h1, h2⟩

theorem ec_comb {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (π : Mx k r → (W →L[ℂ] W))
    {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    ecOp π (X₁ + Complex.I • X₂) = dOp π X₁ + Complex.I • dOp π X₂ := by
  unfold ecOp
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]

end Lie

end LieListProducts

open LieListProducts in
theorem qr_ecLie_of : Qr.DOpLin → Qr.DOpBracket → Qr.EcLie := by
  intro hLin hBr W _ _ _ k r z π hπ Z Z' hZ hZ'
  obtain ⟨hX₁, hX₂⟩ := hZ
  obtain ⟨hY₁, hY₂⟩ := hZ'
  have eZ := hsum Z
  have eZ' := hsum Z'
  set X₁ := hpart1 (Hpk k r) Z
  set X₂ := hpart2 (Hpk k r) Z
  set Y₁ := hpart1 (Hpk k r) Z'
  set Y₂ := hpart2 (Hpk k r) Z'
  have dadd : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X + Y) = dOp π X + dOp π Y :=
    fun X Y hX hY => (hLin W k r z π hπ X Y hX hY).1
  have dsm : ∀ X (s : ℝ), InLieW k r z X → dOp π ((s : ℂ) • X) = (s : ℂ) • dOp π X := fun X s hX => by
    rw [(hLin W k r z π hπ X X hX hX).2 s, Complex.coe_smul]
  have dsub : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X - Y) = dOp π X - dOp π Y := fun X Y hX hY => by
    have e : X - Y = X + (((-1 : ℝ) : ℂ)) • Y := by simp [sub_eq_add_neg]
    rw [e, dadd _ _ hX (lie_smul hY _), dsm _ _ hY]
    simp [sub_eq_add_neg]
  have ecZ : ecOp π Z = dOp π X₁ + Complex.I • dOp π X₂ := rfl
  have ecZ' : ecOp π Z' = dOp π Y₁ + Complex.I • dOp π Y₂ := rfl
  refine ⟨?_, fun c => ?_, ?_⟩
  · have e : Z + Z' = (X₁ + Y₁) + Complex.I • (X₂ + Y₂) := by
      rw [← eZ, ← eZ', smul_add]; abel
    rw [e]
    refine ⟨gl_comb (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), ?_⟩
    rw [ec_comb π (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), dadd _ _ hX₁ hY₁, dadd _ _ hX₂ hY₂, ecZ, ecZ', smul_add]
    abel
  · have e : c • Z = ((c.re : ℂ) • X₁ - (c.im : ℂ) • X₂) + Complex.I • ((c.re : ℂ) • X₂ + (c.im : ℂ) • X₁) := by
      rw [alg_smul, Complex.re_add_im, eZ]
    have l1 := lie_sub (lie_smul hX₁ c.re) (lie_smul hX₂ c.im)
    have l2 := lie_add (lie_smul hX₂ c.re) (lie_smul hX₁ c.im)
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ (lie_smul hX₁ c.re) (lie_smul hX₂ c.im),
      dadd _ _ (lie_smul hX₂ c.re) (lie_smul hX₁ c.im), dsm X₁ c.re hX₁, dsm X₂ c.im hX₂, dsm X₂ c.re hX₂, dsm X₁ c.im hX₁, alg_smul, Complex.re_add_im, ecZ]
  · have b11 := hBr W k r z π hπ X₁ Y₁ hX₁ hY₁
    have b22 := hBr W k r z π hπ X₂ Y₂ hX₂ hY₂
    have b12 := hBr W k r z π hπ X₁ Y₂ hX₁ hY₂
    have b21 := hBr W k r z π hπ X₂ Y₁ hX₂ hY₁
    have e : Z * Z' - Z' * Z = ((X₁ * Y₁ - Y₁ * X₁) - (X₂ * Y₂ - Y₂ * X₂)) +
        Complex.I • ((X₁ * Y₂ - Y₂ * X₁) + (X₂ * Y₁ - Y₁ * X₂)) := by
      rw [← alg_bracket, eZ, eZ']
    have l1 := lie_sub b11.1 b22.1
    have l2 := lie_add b12.1 b21.1
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ b11.1 b22.1, dadd _ _ b12.1 b21.1, b11.2, b22.2, b12.2, b21.2, ecZ, ecZ']
    exact (alg_bracket (dOp π X₁) (dOp π X₂) (dOp π Y₁) (dOp π Y₂)).symm

namespace LieListProducts

theorem unitB_mul {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ)
    (ho : ∀ a b, herm H (Bs a) (Bs b) = if a = b then 1 else 0) (a b c d : Fin m) :
    unitB H Bs a b * unitB H Bs c d = if b = c then unitB H Bs a d else 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, Qx8.unitB_mulVec H Bs c d, Matrix.mulVec_smul, Qx8.unitB_mulVec, ho]
  by_cases h : b = c
  · rw [if_pos h, if_pos h.symm, one_smul, Qx8.unitB_mulVec]
  · rw [if_neg h, if_neg (Ne.symm h), zero_smul, smul_zero, Matrix.zero_mulVec]

theorem list_prod_apply {W : Type*} [AddCommGroup W] [Module ℂ W] (L : List (Module.End ℂ W)) (v : W) :
    (L.map fun T : Module.End ℂ W => fun y : W => T y).foldr (fun T h => T h) v = L.prod v := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    rw [ih]
    rfl

end LieListProducts

open LieListProducts in
theorem qr_frameGl_of : Qr.EcLie → Qr.FrameGl := by
  intro hE W _ _ _ k r m z π Bs hπ hB
  have hgl : ∀ a b, InGlW k r z (unitB (Hpk k r) Bs a b) := fun a b => frame_lie hB a b
  have h0 : InGlW k r z 0 ∧ ecOp π (0 : Mx k r) = 0 := by
    have h := (hE W k r z π hπ 0 0 ?_ ?_).2.1 0
    · simpa using h
    all_goals
      unfold InGlW
      rw [hpart1_lie (z := z) lie_zero, hpart2_lie (z := z) lie_zero]
      exact ⟨lie_zero, lie_zero⟩
  have hsub : ∀ Z Z', InGlW k r z Z → InGlW k r z Z' → ecOp π (Z - Z') = ecOp π Z - ecOp π Z' := by
    intro Z Z' hZ hZ'
    have h1 := (hE W k r z π hπ Z' Z' hZ' hZ').2.1 (-1)
    have h2 := (hE W k r z π hπ Z ((-1 : ℂ) • Z') hZ h1.1).1.2
    rw [h1.2] at h2
    simpa [sub_eq_add_neg] using h2
  have hite : ∀ (p : Prop) [Decidable p] (Z : Mx k r), InGlW k r z Z →
      InGlW k r z (if p then Z else 0) ∧ ecOp π (if p then Z else 0) = if p then ecOp π Z else 0 := by
    intro p _ Z hZ
    by_cases h : p
    · simpa [h] using hZ
    · simpa [h] using h0
  refine ⟨fun a b c d => ?_, fun w v => ?_⟩
  · have h := (hE W k r z π hπ _ _ (hgl a b) (hgl c d)).2.2.2
    rw [unitB_mul _ _ hB.2.1, unitB_mul _ _ hB.2.1, hsub _ _ (hite _ _ (hgl a d)).1 (hite _ _ (hgl c b)).1,
      (hite _ _ (hgl a d)).2, (hite _ _ (hgl c b)).2] at h
    unfold EB
    ext x
    have hx := congrArg (fun T : W →L[ℂ] W => T x) h
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] at hx ⊢ <;> exact hx.symm
  · unfold capRep qmF qdet qminor
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Module.End.mul_apply, ← list_prod_apply, List.map_ofFn]
    have e : ((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) = (((Equiv.Perm.sign σ : ℤ) : ℂ)) • (1 : Module.End ℂ W) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [e, LinearMap.smul_apply, Module.End.one_apply]
    congr 3
    funext j y
    simp only [Function.comp, Tm, id, LinearMap.add_apply]
    rw [ecRep_eq hπ.1 hπ.2 (hgl _ _).1 (hgl _ _).2]
    congr 1
    by_cases h : σ j = j
    · simp [h, Algebra.algebraMap_eq_smul_one]
    · simp [h]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfXOfParts
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

noncomputable section

theorem lift_of_x_of_parts : TL.LiftXOfParts := by
  intro hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨_, _, hAct, hQQ, _, _, _, hLS⟩ := hD
  obtain ⟨B0, _, hB⟩ := hX Wp Wq P Bs X
  obtain ⟨hFB, hEq, hRad⟩ := hB Y
  set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE
  set s : ℂ := M.sgn P l0 with hs
  have hx : st.x Y = L.GGi * st.QQ Y 1 1 := by
    rw [hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1) := by
    rw [hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  refine hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_
  · refine ⟨MvPolynomial.C s, by simp, fun g => by simp⟩
  · intro p hp g hg J
    simp only [pow_zero, mul_one, smul_apply]
    rw [hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx'
    simp only [pow_zero, mul_one, smul_apply]
    rw [hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]
    have hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2 := hx'.2.2
    simp only [Q.fnVal]
    congr 1
    have hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp

end

end Formalism.FourierDecayAlt.P
end

