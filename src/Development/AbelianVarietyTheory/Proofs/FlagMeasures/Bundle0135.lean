import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.CutQuot

section Abstract

variable {X : Type*} [MeasurableSpace X] {T : X → X → X} {G R : Set X} {μG μR ν : Measure X}

theorem null_of_stable (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    {B : Set X} (hB : MeasurableSet B) (hst : ∀ s ∈ R, ∀ x ∈ B, T s x ∈ B) (hn : μG B = 0) : ν B = 0 := by
  have h1 := hW (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hn] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤
      ∫⁻ x, (∫⁻ s, B.indicator (1 : X → ℝ≥0∞) (T s x) ∂μR) ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae ?_)
      filter_upwards [hR] with s hs
      rw [Set.indicator_of_mem (hst s hs x hx)]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [← h1, lintegral_indicator_const hB, nonpos_iff_eq_zero, mul_eq_zero] at h2
  exact h2.resolve_left (by simpa using h0)

theorem exists_cut [SigmaFinite μG] [SFinite μR] (hT : Measurable (Function.uncurry T))
    (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    (hG : ∀ᵐ x ∂ν, x ∈ G)
    (hinv : ∀ ρ ∈ R, ∀ x, ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ s, f (T s (T ρ x)) ∂μR = ∫⁻ s, f (T s x) ∂μR) :
    ∃ φ : X → ℝ≥0∞, Measurable φ ∧ (∀ x, ∫⁻ ρ, φ (T ρ x) ∂μR ≤ 1) ∧
      ∀ F : X → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x ∈ G, F (T ρ x) = F x) →
        ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  obtain ⟨g, hg0, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set ψ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞) with hψ
  have hψm : Measurable ψ := hgm.coe_nnreal_ennreal
  have hTx : ∀ x, Measurable fun s => T s x := fun x => hT.comp (measurable_id.prodMk measurable_const)
  set I : X → ℝ≥0∞ := fun x => ∫⁻ s, ψ (T s x) ∂μR with hI
  have hIm : Measurable I := Measurable.lintegral_prod_left (f := fun s x => ψ (T s x)) (hψm.comp hT)
  have hI0 : ∀ x, I x ≠ 0 := by
    intro x hx
    have h := (lintegral_eq_zero_iff (hψm.comp (hTx x))).1 hx
    apply h0
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with s hs
    have := hg0 (T s x)
    simp [hψ] at hs
    exact this.ne' hs
  have hIfin : ∀ᵐ x ∂ν, I x < ∞ := by
    refine ae_lt_top hIm ?_
    rw [← hW ψ hψm]
    exact (hgi.trans ENNReal.one_lt_top).ne
  have key : ∀ x, ∫⁻ ρ, ψ (T ρ x) * (I (T ρ x))⁻¹ ∂μR = I x * (I x)⁻¹ := by
    intro x
    rw [show I x * (I x)⁻¹ = ∫⁻ ρ, ψ (T ρ x) * (I x)⁻¹ ∂μR from
      (lintegral_mul_const (I x)⁻¹ (f := fun s => ψ (T s x)) (hψm.comp (hTx x))).symm]
    refine lintegral_congr_ae ?_
    filter_upwards [hR] with s hs
    have : I (T s x) = I x := hinv s hs x ψ hψm
    rw [this]
  have hφm : Measurable fun x => ψ x * (I x)⁻¹ := hψm.mul hIm.inv
  refine ⟨fun x => ψ x * (I x)⁻¹, hφm, fun x => ?_, fun F hF hFi => ?_⟩
  · rw [key]; exact ENNReal.mul_inv_le_one _
  · show _ = ∫⁻ x, ψ x * (I x)⁻¹ * F x ∂μG
    rw [hW (fun x => ψ x * (I x)⁻¹ * F x) (hφm.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [hG, hIfin] with x hx hx'
    have h1 : ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F (T s x) ∂μR =
        ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F x ∂μR := by
      refine lintegral_congr_ae ?_
      filter_upwards [hR] with s hs
      rw [hFi s hs x hx]
    rw [h1, lintegral_mul_const (F x) (f := fun s => ψ (T s x) * (I (T s x))⁻¹) (hφm.comp (hTx x)), key,
      ENNReal.mul_inv_cancel (hI0 x) hx'.ne, one_mul]

end Abstract

theorem mul_mem_iff {k r : ℕ} {s : Mat k r} (hs : s ∈ GG k r) (x : Mat k r) :
    s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← hs']
    simp only [Matrix.mul_assoc]
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem measurable_G (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq (f := fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x)
    ((h.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h) continuous_const

theorem continuous_act (k r : ℕ) :
    Continuous (Function.uncurry fun s x : Mt k r => lmulM (Matrix.of s) x) := by
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact (h.comp continuous_fst).matrix_mul (h.comp continuous_snd)

theorem cut_quotient : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  intro k r R μG μR ν hR hG hμ hU hW
  haveI := hG.1
  haveI := hμ.1
  set T : Mt k r → Mt k r → Mt k r := fun s x => lmulM (Matrix.of s) x with hT
  have hTm : Measurable (Function.uncurry T) := (continuous_act k r).measurable
  have hae : ∀ᵐ s ∂μR, s ∈ {x : Mt k r | Matrix.of x ∈ R} := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν := hW
  have hmem : ∀ s : Mt k r, Matrix.of s ∈ R → ∀ x : Mt k r,
      (Matrix.of (T s x) ∈ GG k r ↔ Matrix.of x ∈ GG k r) := fun s hs x =>
    mul_mem_iff (hR.1 hs) (Matrix.of x)
  have h1 : ν {x | Matrix.of x ∉ GG k r} = 0 :=
    null_of_stable hae hμ.2.1 hW' (measurable_G k r).compl
      (fun s hs x hx h => hx ((hmem s hs x).1 h)) hG.2.2.1
  have h1' : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := h1
  refine ⟨h1, fun A hA hst hn => ?_, ?_⟩
  · have h2 : ν (A ∩ {x : Mt k r | Matrix.of x ∈ GG k r}) = 0 :=
      null_of_stable hae hμ.2.1 hW' (hA.inter (measurable_G k r))
        (fun s hs x hx => ⟨(hst _ hs x hx.2).2 hx.1, (hmem s hs x).2 hx.2⟩)
        (measure_mono_null Set.inter_subset_left hn)
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h2 h1)
    by_cases h : Matrix.of x ∈ GG k r
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · obtain ⟨φ, hφ, hle, hF⟩ := exists_cut hTm hae hμ.2.1 hW' h1' (by
      intro ρ hρ x f hf
      have hTx : Measurable fun s => T s x := hTm.comp (measurable_id.prodMk measurable_const)
      have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
      have hr : Measurable (rmulM (k := k) (r := r) (Matrix.of ρ)) :=
        by
        have hc' : Continuous (rmulM (k := k) (r := r) (Matrix.of ρ)) := hc.matrix_mul continuous_const
        exact hc'.measurable
      conv_rhs => rw [← hU.1 (Matrix.of ρ) hρ]
      rw [lintegral_map (f := fun s => f (T s x)) (hf.comp hTx) hr]
      refine lintegral_congr fun s => congrArg f ?_
      exact (Matrix.mul_assoc (Matrix.of s) (Matrix.of ρ) (Matrix.of x)).symm)
    exact ⟨φ, ⟨hφ, fun x _ => hle x⟩, fun F hFm hFi => hF F hFm fun ρ hρ x hx => hFi _ hρ x hx⟩

end GlobalTheory.Amp.CutQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DoubledFlag

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.DoubledFlag.sum_range_double {M : Type} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) :
    ∑ s ∈ range (2 * a + 1), f s = ∑ i : Fin a, (f i + f (2 * a - i)) + f a := by
  rw [show 2 * a + 1 = (a + 1) + a by ring, Finset.sum_range_add, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => f i + f (2 * a - i)), Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun x => f (a + 1 + x)) a]
  have h : ∀ x ∈ range a, f (a + 1 + (a - 1 - x)) = f (2 * a - x) := fun x hx => by
    rw [Finset.mem_range] at hx; congr 1; omega
  rw [Finset.sum_congr rfl h]
  abel

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = _root_.GlobalTheory.FlagMeas.dimN n j ∧ _root_.GlobalTheory.Count.layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  intro n a j D ν hj hD hD0 hν0 hν hna hsym
  have hJ : ν a = ∑ i, j i := by
    have h1 : ∀ m, m ≤ a → ν m = ∑ i ∈ range m, if h : i < a then j ⟨i, h⟩ else 0 := by
      intro m hm
      induction m with
      | zero => simp [hν0]
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega), dif_pos (by omega)]
        exact hν ⟨m, by omega⟩
    rw [h1 a le_rfl, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < a then j ⟨i, h⟩ else 0)]
    simp
  have hmid : ν (a + 1) + ν a = n := by
    have h := (hsym a le_rfl).2
    rwa [show 2 * a + 1 - a = a + 1 by omega] at h
  have hlow : ∀ i : Fin a, (ν (i + 1) - ν i) * ν i = j i * ν i := by
    intro i; rw [hν i, Nat.add_sub_cancel_left]
  have hhigh : ∀ i : Fin a, (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i) + j i * ν (i + 1)
      = j i * n := by
    intro i
    have hi := i.isLt
    have h1 := (hsym i (by omega)).2
    have h2 := (hsym (i + 1) (by omega)).2
    have h3 := hν i
    rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
    rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
    rw [show ν (2 * a - i + 1) - ν (2 * a - i) = j i by omega, ← mul_add, h2]
  have hsq : ν a * ν a = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    have hsplit : ∀ i k : Fin a, j i * j k = ((if i < k then j i * j k else 0) +
        (if k < i then j k * j i else 0)) + (if i = k then j i ^ 2 else 0) := by
      intro i k
      rcases lt_trichotomy i k with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp [sq]
      · simp [h, h.ne', not_lt.2 h.le]; ring
    rw [hJ, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsplit i k]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_filter, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
    ring
  refine ⟨?_, ?_⟩
  · rw [_root_.GlobalTheory.DoubledFlag.sum_range_double]
    have hF : ∑ i : Fin a, ((ν (i + 1) - ν i) * ν i + (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i))
        + ∑ i, j i ^ 2 = n * ν a := by
      rw [← Finset.sum_add_distrib, hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := hhigh i
      rw [hν i] at h
      rw [hlow i]
      nlinarith
    unfold _root_.GlobalTheory.FlagMeas.dimN
    rw [← hJ]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * ν a := ⟨n - 2 * ν a, by omega⟩
    rw [show ν (a + 1) - ν a = m by omega, show m + 2 * ν a - 2 * ν a = m by omega]
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ → ℝ, D = fun s => Real.exp (d s) :=
      ⟨fun s => Real.log (D s), funext fun s => (Real.exp_log (hD s)).symm⟩
    have hd0 : d 0 = 0 := by simpa using hD0
    have hdsym : ∀ s, s ≤ a → d (2 * a + 1 - s) = d s := fun s hs => by
      simpa using (hsym s hs).1
    have hc : ∀ i : Fin a, (Real.exp (d (i + 1)) / Real.exp (d i)) ^ (-(1 : ℝ) / j i)
        = Real.exp ((d i - d (i + 1)) / j i) := by
      intro i
      rw [← Real.exp_sub, ← Real.exp_mul]
      congr 1
      ring
    have htail : ∀ i : Fin a, ∑ k ∈ univ.filter (fun k => i < k), (j k : ℝ) = ν a - ν ((i : ℕ) + 1) := by
      intro i
      have hi := i.isLt
      have e : ∀ k : Fin a, (j k : ℝ) = ν ((k : ℕ) + 1) - ν k := fun k => by
        rw [hν k]; push_cast; ring
      simp only [e, Finset.sum_filter, Fin.lt_iff_val_lt_val]
      rw [Fin.sum_univ_eq_sum_range (fun x => if (i : ℕ) < x then (ν (x + 1) : ℝ) - ν x else 0) a,
        ← Finset.sum_filter,
        show (range a).filter (fun x => (i : ℕ) < x) = Ico ((i : ℕ) + 1) a by
          ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_sub (fun x => (ν x : ℝ)),
        Finset.sum_range_sub (fun x => (ν x : ℝ))]
      ring
    simp only [hc]
    unfold _root_.GlobalTheory.Count.layerProd
    simp only [id, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_sum, ← Real.exp_neg,
      pow_one, mul_one]
    rw [Real.exp_eq_exp, ← hJ, _root_.GlobalTheory.DoubledFlag.sum_range_double, eq_neg_iff_add_eq_zero, ← add_assoc,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr (s₁ := (univ : Finset (Fin a))) rfl (g := fun i : Fin a =>
        (2 * (ν ((i : ℕ) + 1) : ℝ) * d ((i : ℕ) + 1) - n * d ((i : ℕ) + 1)) - (2 * (ν i : ℝ) * d i - n * d i)) ?_,
      Fin.sum_univ_eq_sum_range (fun x => (2 * (ν (x + 1) : ℝ) * d (x + 1) - n * d (x + 1)) - (2 * (ν x : ℝ) * d x - n * d x)),
      Finset.sum_range_sub (fun x => 2 * (ν x : ℝ) * d x - n * d x)]
    · have hm : (ν (a + 1) : ℝ) = n - ν a := by rw [eq_sub_iff_add_eq]; exact_mod_cast hmid
      have hda : d (a + 1) = d a := by rw [← hdsym a le_rfl]; congr 1; omega
      rw [hm, hda, hν0, hd0]
      push_cast
      ring
    · intro i _
      have hi := i.isLt
      have hji : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
      have h1 := (hsym i (by omega)).2
      have h2 := (hsym (i + 1) (by omega)).2
      rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
      rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
      have e1 : (ν (2 * a - i + 1) : ℝ) = n - ν i := by rw [eq_sub_iff_add_eq]; exact_mod_cast h1
      have e2 : (ν (2 * a - i) : ℝ) = n - ν ((i : ℕ) + 1) := by rw [eq_sub_iff_add_eq]; exact_mod_cast h2
      have e3 : (ν ((i : ℕ) + 1) : ℝ) = ν i + j i := by exact_mod_cast hν i
      have f1 : d (2 * a - i + 1) = d i := by rw [← hdsym i (by omega)]; congr 1; omega
      have f2 : d (2 * a - i) = d ((i : ℕ) + 1) := by rw [← hdsym (i + 1) (by omega)]; congr 1; omega
      rw [Finset.sum_congr rfl (g := fun k => 4 * (d i - d ((i : ℕ) + 1)) * (j k : ℝ))
          fun k _ => by push_cast; field_simp; ring, ← Finset.mul_sum, htail i, e1, e2, f1, f2, e3]
      push_cast [Nat.cast_sub hna]
      field_simp
      ring

end GlobalTheory.DoubledFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOnKCOfEqZeroOnKset
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec.KCIdent

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder in

theorem exists_herm_log {n : ℕ} (y J : Matrix (Fin n) (Fin n) ℂ) (hy : IsUnit y)
    (hJ : Commute (yᴴ * y) J) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ, Lᴴ = L ∧ Commute L J ∧ NormedSpace.exp L = yᴴ * y := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ yᴴ * y := star_mul_self_nonneg y
  have hu : IsUnit (yᴴ * y) := hy.star.mul hy
  have hsp : IsStrictlyPositive (yᴴ * y) := IsStrictlyPositive.iff_of_unital.mpr ⟨h0, hu⟩
  refine ⟨CFC.log (yᴴ * y), ?_, Commute.cfc_real hJ Real.log, CFC.exp_log (yᴴ * y) hsp⟩
  exact (IsSelfAdjoint.log : IsSelfAdjoint (CFC.log (yᴴ * y)))

theorem differentiable_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • X) i j) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  intro z
  have hz : DifferentiableAt ℂ (fun w : ℂ => NormedSpace.exp (w • X)) z :=
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) X z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiableAt.comp z hz

theorem eq_zero_on_KC_of_eq_zero_on_Kset : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : Matrix (Fin n) (Fin n) ℂ → E), DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => F (Matrix.of y)) {y | Matrix.of y ∈ GlobalTheory.Dec.KC ε} → (∀ k ∈ Formalism.REAL.Kset ε, F k = 0) → ∀ y ∈ GlobalTheory.Dec.KC ε, F y = 0 := by
  intro n ε E _ _ _ F hF hK y hy
  unfold GlobalTheory.Dec.KC at hy
  obtain ⟨hyu, hyJ⟩ := hy
  have hJh : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hyhJ : yᴴ * Jm ε = Jm ε * yᴴ := by
    have h := congrArg Matrix.conjTranspose hyJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hc : Commute (yᴴ * y) (Jm ε) := by
    show yᴴ * y * Jm ε = Jm ε * (yᴴ * y)
    rw [mul_assoc, hyJ, ← mul_assoc, hyhJ, mul_assoc]
  obtain ⟨L, hLh, hLJ, hLe⟩ := exists_herm_log y (Jm ε) hyu hc
  obtain ⟨E', hE'⟩ : ∃ f : ℂ → Matrix (Fin n) (Fin n) ℂ, f = fun w => NormedSpace.exp (w • L) :=
    ⟨_, rfl⟩
  have hmul : ∀ a b : ℂ, E' a * E' b = E' (a + b) := by
    intro a b
    simp only [hE', add_smul]
    exact (Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left a).smul_right b)).symm
  have hstar : ∀ w : ℂ, (E' w)ᴴ = E' (star w) := by
    intro w
    simp only [hE']
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hLh]
  have hEJ : ∀ w : ℂ, E' w * Jm ε = Jm ε * E' w := by
    intro w
    simp only [hE']
    exact (hLJ.smul_left w).exp_left.eq
  have hE0 : E' 0 = 1 := by simp [hE']
  have hEone : E' 1 = yᴴ * y := by
    simp only [hE', one_smul]
    exact hLe
  have hEu : ∀ w : ℂ, IsUnit (E' w) := by
    intro w
    simp only [hE']
    exact Matrix.isUnit_exp _
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ, u = y * E' (-(1 / 2)) := ⟨_, rfl⟩
  have hhalf : star (-(1 / 2 : ℂ)) = -(1 / 2) := by simp
  have hu1 : uᴴ * u = 1 := by
    rw [hu, Matrix.conjTranspose_mul, hstar, hhalf]
    have e1 : E' (-(1 / 2)) * yᴴ * (y * E' (-(1 / 2))) = E' (-(1 / 2)) * (yᴴ * y) * E' (-(1 / 2)) := by
      simp only [mul_assoc]
    have e2 : (-(1 / 2 : ℂ) + 1 + -(1 / 2)) = 0 := by ring
    rw [e1, ← hEone, hmul, hmul, e2, hE0]
  have huJ : u * Jm ε = Jm ε * u := by
    rw [hu, mul_assoc, hEJ, ← mul_assoc, hyJ, mul_assoc]
  have huU : IsUnit u := by
    rw [hu]
    exact hyu.mul (hEu _)
  have hKC : ∀ z : ℂ, u * E' z ∈ GlobalTheory.Dec.KC ε := by
    intro z
    unfold GlobalTheory.Dec.KC
    refine ⟨huU.mul (hEu z), ?_⟩
    rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hzero : ∀ t : ℝ, F (u * E' ((t : ℂ) * Complex.I)) = 0 := by
    intro t
    apply hK
    unfold Formalism.REAL.Kset
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hstar]
      have hsw : star ((t : ℂ) * Complex.I) + (t : ℂ) * Complex.I = 0 := by
        rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [mul_assoc, ← mul_assoc uᴴ, hu1, one_mul, hmul, hsw, hE0]
    · rw [mul_assoc, hEJ, ← mul_assoc, huJ, mul_assoc]
  have hγ : Differentiable ℂ (fun z : ℂ => (fun a b => (u * E' z) a b : Fin n → Fin n → ℂ)) := by
    refine differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    have hd : ∀ c, Differentiable ℂ (fun z : ℂ => E' z c b) := by
      intro c
      simp only [hE']
      exact differentiable_exp_entry L c b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun c _ => (differentiable_const (u a c)).mul (hd c)
  have hg : Differentiable ℂ (fun z : ℂ => F (u * E' z)) := fun z =>
    ((hF _ (hKC z)).comp z ((hγ z).differentiableWithinAt (s := Set.univ))
      (fun w _ => hKC w)).differentiableAt Filter.univ_mem
  have han : AnalyticOnNhd ℂ (fun z : ℂ => F (u * E' z)) Set.univ := fun z _ => hg.analyticAt z
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, F (u * E' z) = 0 := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhdsWithin (0 : ℂ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hcont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Complex.I_ne_zero] using ht
    exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero))
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq
  have h12 := hall (Set.mem_univ (1 / 2 : ℂ))
  have hy' : u * E' (1 / 2) = y := by
    have e3 : (-(1 / 2 : ℂ) + 1 / 2) = 0 := by ring
    rw [hu, mul_assoc, hmul, e3, hE0, mul_one]
  simp only [Pi.zero_apply] at h12
  rw [hy'] at h12
  exact h12

end GlobalTheory.Dec.KCIdent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplOfSaturated
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem exists_compl_of_saturated {R V : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublatticeComplement.main
  | exact _root_.GlobalTheory.SaturatedSublatticeComplement.main
  | (apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublatticeComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublatticeComplement.main ..)

theorem saturatedFlag_splits : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i, ∀ y ∈ S (Fin.last a), y ∈ Submodule.span E (S i : Set (Fin n → E)) → y ∈ S i) → ∃ A : Fin a → Submodule (𝓞 E) (Fin n → E), ∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ := by
  intro E _ _ n a S _ hmono hfg hsat
  have key : ∀ i : Fin a, ∃ A : Submodule (𝓞 E) (Fin n → E),
      A ⊓ S i.castSucc = ⊥ ∧ A ⊔ S i.castSucc = S i.succ := by
    intro i
    have hle : S i.succ ≤ S (Fin.last a) := hmono (Fin.le_last _)
    refine exists_compl_of_saturated _ _ (hmono (Fin.castSucc_lt_succ).le)
      (Submodule.FG.of_le hfg hle) ?_
    intro r y hr hy hry
    apply hsat _ y (hle hy)
    have hr' : (algebraMap (𝓞 E) E r) ≠ 0 := by
      simpa using hr
    have : y = (algebraMap (𝓞 E) E r)⁻¹ • (r • y) := by
      rw [← algebraMap_smul E r y, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hry)
  choose A hA using key
  exact ⟨A, hA⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKStableOfMemLowKSub
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem exists_kStable_of_mem_lowKSub (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (hw : w ∈ lowKSub ε lam σ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧ w ∈ S := by
  classical
  obtain ⟨s, hs, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  refine ⟨⨆ i ∈ s, i, ?_, ?_, hws⟩
  · have hfg : (⨆ i ∈ s, i).FG := by
      refine Submodule.fg_biSup s (fun i => i) (fun i hi => ?_)
      obtain ⟨hfin, -⟩ := hs hi
      exact (Submodule.fg_iff_finiteDimensional i).2 hfin
    exact (Submodule.fg_iff_finiteDimensional _).1 hfg
  · intro g hg v hv
    have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine iSup₂_le fun i hi => ?_
      obtain ⟨-, hstab, -⟩ := hs hi
      intro x hx
      exact (le_iSup₂ (f := fun j (_ : j ∈ s) => j) i hi) (hstab g hg x hx)
    exact hle hv

theorem isKFin_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), w ∈ lowKSub ε lam σ → IsKFin ε σ w := by
  intro n ε lam H _ _ σ w hw
  obtain ⟨S, hfin, hstab, hwS⟩ := exists_kStable_of_mem_lowKSub n ε lam H σ w hw
  exact ⟨S, hfin, hwS, hstab⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplitStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_components_basis_local_lattice_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.St.G.first_components_basis | exact GlobalTheory.St.G.first_components_basis | (intros; apply GlobalTheory.St.G.first_components_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIffStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r), Λ.FG → (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔ ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  first | exact @GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | exact GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | (intros; apply GlobalTheory.RowLatXS.Ia_fg_and_mem_iff <;> assumption)
end

