import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0010
import Formalism.FlagUnipotentLattices.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0009

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfDecayThreshold
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def rrk_Psi {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (φ : G → ℂ) (z : G) : ℝ≥0∞ :=
  ∫⁻ g, ‖φ g‖ₑ * ‖φ (g⁻¹ * z)‖ₑ ∂μ

section Abs

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G}
  [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

theorem rrk_Kab_sq (h : rr_FD μ Γ D) (hφm : Measurable φ) (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x : G) :
    ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ = ∑' γ : Γ, rrk_Psi μ φ (x⁻¹ * (γ : G) * x) := by
  rw [← rrka_lint h hφm hsa x]
  unfold rrk_Kab
  simp_rw [← ENNReal.tsum_mul_left]
  have hm : ∀ γ : Γ, AEMeasurable (fun y => ‖φ (x⁻¹ * y)‖ₑ * ‖φ (y⁻¹ * (γ : G) * x)‖ₑ) μ := fun γ =>
    ((hφm.comp (measurable_const_mul x⁻¹)).enorm.mul
      (hφm.comp ((measurable_inv.mul_const (γ : G)).mul_const x)).enorm).aemeasurable
  rw [lintegral_tsum hm]
  refine tsum_congr fun γ => ?_
  unfold rrk_Psi
  rw [← lintegral_mul_left_eq_self (fun y => ‖φ (x⁻¹ * y)‖ₑ * ‖φ (y⁻¹ * (γ : G) * x)‖ₑ) x]
  refine lintegral_congr fun g => ?_
  simp [mul_assoc]

end Abs

def ConvDec (X : CData) (q₀ : ℕ) (h' : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ z : X.I.GA,
    rrk_Psi (X.I.muA X.μf) X.φ z ≤
      ENNReal.ofReal (M * ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (cartanDistance (X.I.ε v) (z.1 v))))) ∧
    (rrk_Psi (X.I.muA X.μf) X.φ z ≠ 0 → z.2 ∈ X.I.Kset)

def AllCount (X : CData) (B : ℝ) : Prop :=
  ∀ᵐ x ∂X.μ, ∃ Ac : ℝ, 0 ≤ Ac ∧ ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset X.I.GFset,
    (∀ γ ∈ S, (x⁻¹ * (γ : X.I.GA) * x).2 ∈ X.I.Kset ∧ ∀ v, X.dist x γ v ≤ r v) →
    (S.card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v)

def ConvDecay (X : CData) (q₀ : ℕ) (h' : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ z : X.I.GA,
    rrk_Psi (X.I.muA X.μf) X.φ z ≤
      ENNReal.ofReal (M * ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (cartanDistance (X.I.ε v) (z.1 v)))))

theorem rrk_Psi_supp (X : CData) (he : ∀ x, X.e x ≠ 0 → x ∈ X.I.Kset) (z : X.I.GA)
    (hz : rrk_Psi (X.I.muA X.μf) X.φ z ≠ 0) : z.2 ∈ X.I.Kset := by
  by_contra hc
  apply hz
  unfold rrk_Psi
  have h0 : ∀ g : X.I.GA, ‖X.φ g‖ₑ * ‖X.φ (g⁻¹ * z)‖ₑ = 0 := by
    intro g
    by_contra hne
    have h1 : X.φ g ≠ 0 := fun e => hne (by simp [e])
    have h2 : X.φ (g⁻¹ * z) ≠ 0 := fun e => hne (by simp [e])
    have e1 : X.e g.2 ≠ 0 := fun e => h1 (by unfold CData.φ phe; rw [e, mul_zero])
    have e2 : X.e (g⁻¹ * z).2 ≠ 0 := fun e => h2 (by unfold CData.φ phe; rw [e, mul_zero])
    have k1 := he _ e1
    have k2 := he _ e2
    apply hc
    have hmul : z.2 = g.2 * (g⁻¹ * z).2 := by
      show z.2 = g.2 * (g.2⁻¹ * z.2)
      group
    rw [hmul]
    exact (Formalism.UG.stabGL X.I.Lf).mul_mem k1 k2
  simp [h0]

theorem ConvDec_of_decay (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) {q₀ : ℕ} {h' : ℝ} (h : ConvDecay X q₀ h') :
    ConvDec X q₀ h' := by
  obtain ⟨M, hM, hb⟩ := h
  exact ⟨M, hM, fun z => ⟨hb z, rrk_Psi_supp X hX.1.2.2.2.2.2.2.1.2.2.2.2.1 z⟩⟩

open Classical in

theorem abs_kernel_L2_of_count_and_decay (X : CData) (hd : RegData X) (hφ : PhiIdem X) {q₀ : ℕ} (hq : ∀ v, q0At X.I v = q₀) {h' B : ℝ}
    (hB : 0 < B) (hthr : 16 * B * Real.sqrt (2 * (q₀ : ℝ)) ≤ h') (hc : ConvDec X q₀ h') (hn : AllCount X B) :
    AbsKernelSquareIntegrable X := by
  obtain ⟨hH, hF, -⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have h1 := rr_FD_of X.I X.μf X.fund hF
  obtain ⟨M, hM, hΨ⟩ := hc
  unfold AbsKernelSquareIntegrable
  filter_upwards [hn] with x hx
  obtain ⟨Ac, hAc, hcnt⟩ := hx
  have e : ∫⁻ y, (∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * y)‖ₑ) ^ 2 ∂X.μ =
      ∑' γ : X.I.GFset, rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) :=
    rrk_Kab_sq h1 hφ.1 hφ.2.1 x
  rw [e]
  set bd : X.I.GFset → ℝ := fun γ => ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (X.dist x γ v))) with hbd
  have hbdn : ∀ γ, 0 ≤ bd γ := fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  set Cst : ℝ := max (Ac * (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card (InfinitePlace X.I.F)) Ac with hCst
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (M * Cst)) ENNReal.ofReal_ne_top ?_
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s : Finset X.I.GFset => ?_
  set S : Finset X.I.GFset := s.filter (fun γ : X.I.GFset => rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hS
  have hterm : ∀ γ ∈ s, rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≤
      (if rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then ENNReal.ofReal (M * bd γ) else 0) := by
    intro γ _
    by_cases h0 : rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
    · simp [h0]
    · rw [if_pos h0]
      exact (hΨ _).1
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hM (hbdn γ)), ← Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hM)
  have hcS : ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, X.dist x γ v ≤ r v).card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v) := by
    intro r hr
    refine hcnt r hr _ fun γ hγ => ?_
    have h3 := Finset.mem_filter.1 hγ
    exact ⟨(hΨ _).2 (Finset.mem_filter.1 h3.1).2, h3.2⟩
  rcases Nat.eq_zero_or_pos q₀ with h0 | hpos
  · refine le_trans ?_ (le_max_right _ _)
    have hd0 : ∀ γ v, X.dist x γ v = 0 := fun γ v => cartan_distance_eq_zero_of_definite (by rw [← h0, ← hq v]; rfl) _
    have hb1 : ∀ γ ∈ S, bd γ ≤ 1 := by
      intro γ _
      refine Finset.prod_le_one (fun v _ => (Real.exp_pos _).le) fun v _ => ?_
      rw [hd0 γ v]
      simp [Formalism.HermitianLatticeCounting.S7.decExp]
    have h2 := hcS (fun _ => 0) (fun _ => le_rfl)
    have hall : (S.filter fun γ => ∀ v, X.dist x γ v ≤ (fun _ => (0 : ℝ)) v) = S :=
      Finset.filter_true_of_mem fun γ _ v => (hd0 γ v).le
    rw [hall] at h2
    simp only [Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at h2
    calc ∑ γ ∈ S, bd γ ≤ ∑ _γ ∈ S, (1 : ℝ) := Finset.sum_le_sum hb1
      _ = (S.card : ℝ) := by simp
      _ ≤ Ac := h2
  · refine le_trans ?_ (le_max_left _ _)
    exact Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.allSumRate (InfinitePlace X.I.F) X.I.GFset S (X.dist x) Ac B h' q₀ hpos hAc hB hthr
      (fun γ _ v => cartan_distance_nonneg _ _) hcS

theorem kernel_diagonal_of_lattice_count (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (hu : UnimodA X) {h' B : ℝ} (hB : 0 < B) (hthr : 16 * B * Real.sqrt (2 * (X.qq : ℝ)) ≤ h')
    (hc : ConvDec X X.qq h') (hn : AllCount X B) : X.KernelDiag :=
  kernel_diagonal_of_local_projector_of_abs_kernel_L2 D hloc X hX h1 hu
    (abs_kernel_L2_of_count_and_decay X (RegData_of_HypB X hX) (PhiIdem_of D hloc X hX h1) (X.qq_spec hX).1 hB hthr hc hn)

theorem rrk_thr (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h2 : X.GapAboveSquareRootThreshold 363) :
    16 * (2 * (X.I.n : ℝ) ^ 2) * Real.sqrt (2 * (X.qq : ℝ)) ≤ X.h / 8 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.I.F) := inferInstance
  have h := h2 v
  rw [(X.qq_spec hX).1 v] at h
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : Real.sqrt 2 ≤ 363 / 256 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hq : 0 ≤ Real.sqrt (X.qq : ℝ) := Real.sqrt_nonneg _
  have hn : 0 ≤ (X.I.n : ℝ) ^ 2 := by positivity
  have hp : 0 ≤ (X.I.n : ℝ) ^ 2 * Real.sqrt (X.qq : ℝ) := mul_nonneg hn hq
  nlinarith [mul_le_mul_of_nonneg_right hs hp]

theorem kernel_diagonal_of_decay_threshold (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hn1 : 1 ≤ X.I.n) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold 363) (hu : UnimodA X) (hc : ConvDecay X X.qq (X.h / 8))
    (hn : AllCount X (2 * (X.I.n : ℝ) ^ 2)) : X.KernelDiag :=
  kernel_diagonal_of_lattice_count D hloc X hX h1 hu
    (by have : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn1
        positivity) (rrk_thr X hX h2) (ConvDec_of_decay X hX hc) hn

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.NearCountOfLayers
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_isNear (X : CData) (εN : ℝ) (x : X.I.GA) (γ : X.I.GFset) : Prop :=
  (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0

def CSize.NearLayers {X : CData} (S : CSize X) (εN δ : ℝ) : Prop :=
  (∀ x ∈ S.I0, ∀ γ : X.I.GFset, γ ≠ X.one' → (∀ v, X.dist x γ v ≤ εN) → X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0) ∧
    ∀ (J : ℕ) (c : Composition J), ∀ x ∈ S.str J c, S.tau J c x ∈ cn_Reg c.length ∧
      ∃ (e : Fin (Fintype.card (cn_Root c.length)) ≃ cn_Root c.length) (β : ℕ → Type) (π : ∀ i, X.I.GFset → β i),
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' → π 0 γ = π 0 γ') ∧
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' →
          π (Fintype.card (cn_Root c.length)) γ = π (Fintype.card (cn_Root c.length)) γ' → γ = γ') ∧
        ∀ (i : Fin (Fintype.card (cn_Root c.length))) (T : Finset X.I.GFset), (∀ γ ∈ T, cn_isNear X εN x γ) →
          (∀ y ∈ T, ∀ z ∈ T, π i y = π i z) → (∀ y ∈ T, ∀ z ∈ T, π (i + 1) y = π (i + 1) z → y = z) →
          ∃ laM : ℝ, cn_la (S.tau J c x) (e i) / 2 ≤ laM ∧
            (T.card : ℝ) ≤ (1 + 2 * (∏ _v : InfinitePlace X.I.F, 3 * δ) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) / laM) ^
              (cn_dim c.blocksFun (X.I.n - 2 * J) (e i) * Fintype.card (InfinitePlace X.I.F))

theorem CSize.nearCount_of_layers {X : CData} (S : CSize X) {εN δ : ℝ} (hδ : 0 ≤ δ) (h : S.NearLayers εN δ) :
    S.NearCount εN δ := by
  refine ⟨h.1, fun J c x hx T hT => ?_⟩
  obtain ⟨hreg, e, β, π, h0, hr, hl⟩ := h.2 J c x hx
  set b : cn_Root c.length → ℝ := fun ρ =>
    (1 + 12 * δ / cn_la (S.tau J c x) ρ) ^ (cn_dim c.blocksFun (X.I.n - 2 * J) ρ * X.I.f) with hb
  have hb0 : ∀ ρ, 0 ≤ b ρ := fun ρ => by
    have := (cn_la_mem hreg ρ).1
    positivity
  set cc : ℕ → ℝ := fun i => if hi : i < Fintype.card (cn_Root c.length) then b (e ⟨i, hi⟩) else 1 with hcc
  have hcc0 : ∀ i, 0 ≤ cc i := fun i => by
    simp only [hcc]
    split_ifs
    · exact hb0 _
    · norm_num
  have key := Formalism.HermitianLatticeCounting.Final.S7.fibreCount X.I.GFset T (Fintype.card (cn_Root c.length)) β π cc hcc0 (fun y hy z hz => h0 y z (hT y hy) (hT z hz))
    (fun y hy z hz => hr y z (hT y hy) (hT z hz)) (fun i hi T' hT' ha hd => by
      obtain ⟨laM, hla, hc⟩ := hl ⟨i, hi⟩ T' (fun γ hγ => hT γ (hT' hγ)) ha hd
      have hpos := (cn_la_mem hreg (e ⟨i, hi⟩)).1
      have h1 := Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.layerCount (InfinitePlace X.I.F) (cn_dim c.blocksFun (X.I.n - 2 * J) (e ⟨i, hi⟩)) δ
        (cn_la (S.tau J c x) (e ⟨i, hi⟩)) laM hδ hpos hla
      refine le_trans hc (le_trans h1 ?_)
      simp only [hcc, dif_pos hi, hb]
      refine pow_le_pow_right₀ ?_ (Nat.mul_le_mul_left _ (card_infinite_places_le_degree X.I))
      have : 0 ≤ 12 * δ / cn_la (S.tau J c x) (e ⟨i, hi⟩) := by positivity
      linarith)
  refine le_trans key (le_of_eq ?_)
  rw [Finset.prod_range]
  have : ∀ i : Fin (Fintype.card (cn_Root c.length)), cc i = b (e i) := fun i => by simp only [hcc, dif_pos i.2]
  rw [Finset.prod_congr rfl fun i _ => this i, Equiv.prod_comp e b]
  rfl

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionCountCuspOfTrivialIdempotent
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem rr_ae_ae_mul {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] {Z : Set G} (hZ : μ Z = 0) : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z := by
  set Z' := toMeasurable μ Z with hZ'
  have hm : MeasurableSet Z' := measurableSet_toMeasurable μ Z
  have h0 : μ Z' = 0 := by rw [hZ', measure_toMeasurable]; exact hZ
  set S : Set (G × G) := (fun p : G × G => p.2 * p.1) ⁻¹' Z' with hS
  have hSm : MeasurableSet S := (measurable_snd.mul measurable_fst) hm
  have hS0 : (μ.prod ν) S = 0 := by
    rw [Measure.prod_apply_symm hSm]
    have : ∀ y : G, μ ((fun x => (x, y)) ⁻¹' S) = 0 := fun y => by
      have : (fun x => (x, y)) ⁻¹' S = (fun x => y * x) ⁻¹' Z' := rfl
      rw [this, measure_preimage_mul]; exact h0
    simp [this]
  have hae : ∀ᵐ p ∂μ.prod ν, p ∉ S := compl_mem_ae_iff.2 (by simpa using hS0)
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with x hx
  filter_upwards [hx] with m hmx hmem
  exact hmx (subset_toMeasurable μ Z hmem)

theorem rr_e_zero (X : CData) (hp : X.I.IsPosType X.e) (h1 : X.e 1 = 0) (y : X.I.Gf) : X.e y = 0 := by
  have := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hp) y
  rw [h1] at this
  simpa using this

theorem rr_T_zero (X : CData) (he : ∀ y, X.e y = 0) (T : X.L2 →L[ℂ] X.L2) (hT : X.IsOp T) : T = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  have h : ∀ x, ⟪x, T y⟫_ℂ = 0 := fun x => by
    rw [hT.2 x y]
    simp [CData.φ, phe, he]
  exact inner_self_eq_zero.1 (h _)

theorem rr_Re_zero (X : CData) (he : ∀ y, X.e y = 0) (hRe : X.I.IsRConvF X.μf X.fund X.R X.e X.Re) : X.Re = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  have h : ∀ x, ⟪x, X.Re y⟫_ℂ = 0 := fun x => by
    rw [hRe.2 x y]
    simp [he]
  exact inner_self_eq_zero.1 (h _)

theorem rr_ext_null (X : CData) (hd : RegData X) (Fv : X.L2) (h0 : (Fv : X.I.GA → ℂ) =ᵐ[X.μ] 0) :
    (X.I.muA X.μf) {y | X.I.ext Fv y ≠ 0} = 0 := by
  obtain ⟨hH, hF, -⟩ := hd
  have := hH
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  set Z₀ : Set X.I.GA := {t | (Fv : X.I.GA → ℂ) t ≠ 0} with hZ₀
  have hz : (X.I.muA X.μf) (Z₀ ∩ X.fund) = 0 := by
    rw [← Measure.restrict_apply' hF.1]
    exact h0
  have hsub : {y | X.I.ext Fv y ≠ 0} ⊆ ⋃ γ : rr_GF X.I, (fun y => (γ : X.I.GA) * y) ⁻¹' (Z₀ ∩ X.fund) := by
    intro y hy
    obtain ⟨γ, h1, h2, h3⟩ := rr_rep_spec hfd y
    refine mem_iUnion.2 ⟨⟨γ, h1⟩, ?_, h3⟩
    show (Fv : X.I.GA → ℂ) (γ * y) ≠ 0
    rw [← h2]
    exact hy
  refine measure_mono_null hsub ?_
  rw [measure_iUnion_null_iff]; intro γ
  rw [measure_preimage_mul]; exact hz

theorem rr_cusp_of_null (X : CData) (hd : RegData X) (Fv : X.L2) (h0 : (Fv : X.I.GA → ℂ) =ᵐ[X.μ] 0) :
    X.I.IsCuspFn (X.I.muA X.μf) (X.I.ext Fv) := by
  intro W _ ν hν
  have hz := rr_ext_null X hd Fv h0
  obtain ⟨hH, -, -⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : IsFiniteMeasure ν := hν.1
  filter_upwards [rr_ae_ae_mul (X.I.muA X.μf) ν hz] with x hx
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hx] with m hm
  by_contra hne
  exact hm hne

theorem projection_count_cusp_of_trivial_idempotent (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.e 1 = 0) :
    X.ProjStep ∧ X.CountedStep ∧ X.CuspStep := by
  have he := rr_e_zero X hX.1.2.2.2.2.2.2.1.2.2.2.1 h1
  have hRe := rr_Re_zero X he hX.2.1.2.2.2.2.2.2
  refine ⟨fun T hT => ?_, fun T hT _ => ?_, fun T hT _ Fv hFv => ?_⟩
  · rw [rr_T_zero X he T hT]
    exact IsStarProjection.zero _
  · have hT0 := rr_T_zero X he T hT
    have hΦ : ∀ Φ : X.I.eHom X.σs X.μf X.fund X.R X.Re, (Φ : X.Hs →L[ℂ] X.L2) = 0 := by
      rintro ⟨Φ, hΦ⟩
      obtain ⟨S, -, rfl⟩ := Submodule.mem_map.1 hΦ
      simp [hRe]
    have hr : ∀ v : X.rg T, (v : X.L2) = 0 := by
      rintro ⟨_, y, rfl⟩
      simp [hT0]
    have s1 : Subsingleton (X.I.eHom X.σs X.μf X.fund X.R X.Re) :=
      ⟨fun a b => Subtype.ext (by rw [hΦ a, hΦ b])⟩
    have s2 : Subsingleton (X.rg T) := ⟨fun a b => Subtype.ext (by rw [hr a, hr b])⟩
    refine ⟨0, fun Φ => ?_⟩
    rw [hr, hΦ]
    simp
  · have hT0 := rr_T_zero X he T hT
    obtain ⟨y, rfl⟩ := hFv
    have : ((T : X.L2 →ₗ[ℂ] X.L2) y) = 0 := by simp [hT0]
    rw [this]
    exact rr_cusp_of_null X (RegData_of_HypB X hX) 0 (Lp.coeFn_zero _ _ _)

end Formalism.MainNotions.LeviCoordinates

end
end

