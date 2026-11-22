import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0033
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCV
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Finset

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ltSigma (r : ℕ) : LsNc5.LtPair r ≃ Σ a : Fin r, Fin a.val where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun q := ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
  left_inv p := by rcases p with ⟨⟨b, a⟩, h⟩; rfl
  right_inv q := by rcases q with ⟨a, b⟩; rfl

theorem sum_lt (r : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p : LsNc5.LtPair r, g p.1.1.val p.1.2.val = ∑ a ∈ range r, ∑ b ∈ range a, g b a := by
  rw [Fintype.sum_equiv (ltSigma r) (fun p => g p.1.1.val p.1.2.val) (fun q => g q.2.val q.1.val) (fun _ => rfl),
    Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range a, g b a) r]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => g b a.val) a.val

theorem sum_id_real (a : ℕ) : ∑ b ∈ range a, (b : ℝ) = a * (a - 1) / 2 := by
  induction a with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem card_lt (r : ℕ) : (Fintype.card (LsNc5.LtPair r) : ℝ) = r * (r - 1) / 2 := by
  have h := sum_lt r (fun _ _ => 1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h]
  exact sum_id_real r

theorem card_lt_nat (r : ℕ) : Fintype.card (LsNc5.LtPair r) = r * (r - 1) / 2 := by
  have h2 : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
  have : ((r * (r - 1) / 2 : ℕ) : ℝ) = r * (r - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · rw [h0]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hp]; push_cast; ring
  exact_mod_cast (card_lt r).trans this.symm

theorem sumX (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * ((a : ℝ) - b)) =
    -((n - 1) * n * (2 * n - 1) / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
    push_cast; ring

theorem sumK (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * (R - b) - 2 * (R - a)) =
    3 * ((n - 1) * n * (2 * n - 1) / 6) - 4 * R * (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ∑ b ∈ range n, ((1 : ℝ) - 2 * (R - b) - 2 * (R - n)) =
        ∑ b ∈ range n, ((1 - 4 * R + 2 * (n : ℝ)) + 2 * (b : ℝ)) :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, sum_id_real]
    push_cast; ring

theorem sumR (R K : ℝ) (n : ℕ) : ∑ b ∈ range n, ((K + 1) * (1 - 2 * (R - b))) = (K + 1) * (n - 2 * R * n + n * (n - 1)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem sumD (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ((1 / 2 : ℝ) - 2 * (R - a)) = n / 2 - 2 * R * n + n * (n - 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem prod_const_rpow {ι : Type*} (s : Finset ι) {c d : ℝ} (hd : 0 < d) (e : ι → ℝ) :
    ∏ x ∈ s, (c * d ^ e x) = c ^ s.card * d ^ (∑ x ∈ s, e x) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos hd]

theorem half_succ (R : ℕ) : R * (R - 1) / 2 + R = R * (R + 1) / 2 := by
  rcases Nat.eq_zero_or_pos R with h0 | hp
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) * (m + 1 + 1) = (m + 1) * m + (m + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

theorem final_alg (t d : ℝ) (hd : 0 < d) (F R K : ℕ) (A B C E : ℝ)
    (h : A + B + C + E = LsNc5.covolumeExponent R K) :
    ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E) =
      t ^ (R * F) * (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) * d ^ LsNc5.covolumeExponent R K /
        (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
  have hd' : d ^ A * d ^ B * d ^ C * d ^ E = d ^ LsNc5.covolumeExponent R K := by
    rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_add hd]
  have h2 : ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) =
      (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_eq_mul_inv, ← inv_pow, ← inv_pow, ← pow_add,
      ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← half_succ]
    congr 1
    ring
  calc ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E)
      = t ^ (R * F) * (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R *
          ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2)) * (d ^ A * d ^ B * d ^ C * d ^ E) := by ring
    _ = _ := by rw [h2, hd']; ring

theorem cVal_prod {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X := by
  have hd0 : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hT : 0 < Tw (D := D) u := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos u
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [cVal]
  rw [prod_const_rpow _ hd0, prod_const_rpow _ hd0, prod_const_rpow _ hd0, ← Real.rpow_sum_of_pos hd0]
  have eX := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((a : ℝ) - b))
  have eK := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((D.R.rS : ℝ) - b) - 2 * ((D.R.rS : ℝ) - a))
  have eR : ∑ b : Fin D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ)))) =
      ∑ b ∈ range D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) :=
    Fin.sum_univ_eq_sum_range (fun b => ((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) D.R.rS
  have eD : ∑ a : Fin D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ))) =
      ∑ a ∈ range D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) :=
    Fin.sum_univ_eq_sum_range (fun a => (1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) D.R.rS
  simp only [Finset.card_univ]
  rw [eX, eK, eR, eD, sumX, sumK, sumR, sumD, card_lt_nat, Fintype.card_fin]
  unfold LsNc5.covolN LsNc5.twoU
  exact final_alg _ _ hd0 _ _ _ _ _ _ _ (by unfold LsNc5.covolumeExponent; ring)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.UnitPairSolutions

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem inP_alg_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : 𝓞 F) :
    InP 𝔭 k (algebraMap F K (a : F)) ↔ a ∈ 𝔭 ^ k := by
  haveI := h𝔭.isPrime
  rw [← idealPowerSpanBounds.mem_pow_iff (K := K)]
  constructor
  · rintro ⟨t, ht, z, hz, hzeq⟩
    have hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) a := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hzeq, map_mul]
      rfl
    refine idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 0) (d := t) (by simpa using ht) ?_
    rw [zero_add, ← hz']
    exact hz
  · intro ha
    exact inP_jK ha

private theorem mem_pow_vF_of_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    a ∈ 𝔭 ^ vF 𝔭 a ∧ a ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
  have hex : ∃ j, a ∉ 𝔭 ^ j := by
    by_contra h
    push_neg at h
    have hi : a ∈ ⨅ i : ℕ, 𝔭 ^ i := (Submodule.mem_iInf _).mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top] at hi
    exact ha ((Submodule.mem_bot _).mp hi)
  obtain ⟨j, hj⟩ := hex
  have hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e} := by
    refine ⟨j, fun e he => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hj (Ideal.pow_le_pow_right hlt.le he)
  refine ⟨Nat.sSup_mem ⟨0, by simp⟩ hbdd, fun h => ?_⟩
  have hc := le_csSup hbdd (show vF 𝔭 a + 1 ∈ {e : ℕ | a ∈ 𝔭 ^ e} from h)
  change vF 𝔭 a + 1 ≤ vF 𝔭 a at hc
  omega

theorem unit_part (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {a : 𝓞 F} (ha : a ≠ 0) :
    (algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a ∈ SP K 𝔭 := by
  haveI := h𝔭.isPrime
  obtain ⟨hmem, hnot⟩ := mem_pow_vF_of_ne_zero h𝔭 ha
  have hle : Ideal.span {s₀ ^ vF 𝔭 a} * 𝔭 ^ vF 𝔭 a ≤ Ideal.span {π ^ vF 𝔭 a} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    exact Ideal.pow_right_mono hu.le _
  have hsa : s₀ ^ vF 𝔭 a * a ∈ Ideal.span {π ^ vF 𝔭 a} :=
    hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hsa
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  have hbnot : b ∉ 𝔭 := by
    intro hb𝔭
    have h1 : s₀ ^ vF 𝔭 a * a ∈ 𝔭 ^ (0 + vF 𝔭 a + 1) := by
      rw [← hb, zero_add, pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) hb𝔭
    refine idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne ?_ hnot h1
    rw [zero_add, pow_one]
    exact fun h => hu.s_notMem (h𝔭.isPrime.mem_of_pow_mem _ h)
  have hbK : algebraMap F K (b : F) * algebraMap F K (π : F) ^ vF 𝔭 a =
      algebraMap F K (s₀ : F) ^ vF 𝔭 a * algebraMap F K (a : F) := by
    have := congrArg (fun x : 𝓞 F => algebraMap F K (x : F)) hb
    simpa [map_mul, map_pow] using this
  have haK : algebraMap F K (a : F) ≠ 0 := by simpa using ha
  refine mem_SP.mpr ⟨b, hbnot, algebraMap (𝓞 F) (𝓞 K) (s₀ ^ vF 𝔭 a), ?_⟩
  show algebraMap F K ((s₀ ^ vF 𝔭 a : 𝓞 F) : F) =
    algebraMap F K (b : F) * ((algebraMap F K (a : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a)
  have hc : ((s₀ ^ vF 𝔭 a : 𝓞 F) : F) = (s₀ : F) ^ vF 𝔭 a := by simp
  rw [hc, map_pow, ← mul_assoc, mul_comm (algebraMap F K (b : F)), mul_assoc, hbK]
  field_simp

private theorem exists_unit_mul_pow_eq_pow_mul_of_isUnif0 {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π s₀ : 𝓞 F}
    (hu : IsUnif0 𝔭 π s₀) {n : ℕ} {C : 𝓞 F} (hC : C ∈ 𝔭 ^ n) (hC' : C ∉ 𝔭 ^ (n + 1)) :
    ∃ b ∉ 𝔭, b * π ^ n = s₀ ^ n * C := by
  have hle : Ideal.span {s₀ ^ n} * 𝔭 ^ n ≤ Ideal.span {π ^ n} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    exact Ideal.pow_right_mono hu.le _
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp
    (hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hC))
  refine ⟨b, fun hb𝔭 => ?_, hb⟩
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  have h1 : s₀ ^ n * C ∈ 𝔭 ^ (0 + n + 1) := by
    rw [← hb, zero_add, pow_succ, mul_comm b]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hu.mem _) hb𝔭
  refine idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne ?_ hC' h1
  rw [zero_add, pow_one]
  exact fun h => hu.s_notMem (h𝔭.isPrime.mem_of_pow_mem _ h)

theorem unit_part_c (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {a : 𝓞 F} (ha : a ≠ 0) (he : vF 𝔭 a ≠ 0) {c : F}
    (hac : InP 𝔭 (2 * vF 𝔭 a) (algebraMap F K ((a : F) + c))) :
    algebraMap F K c ≠ 0 ∧ (algebraMap F K c)⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a ∈ SP K 𝔭 := by
  haveI := h𝔭.isPrime
  obtain ⟨hmem, hnot⟩ := mem_pow_vF_of_ne_zero h𝔭 ha
  have hne : 𝔭 ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨π, hu.mem, hu.ne_zero⟩
  obtain ⟨t, ht, z, hz, hzeq⟩ := hac
  have hint : IsIntegral ℤ ((t : F) * ((a : F) + c)) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F K) (algebraMap F K).injective]
    have hzK : IsScalarTower.toAlgHom ℤ F K ((t : F) * ((a : F) + c)) = algebraMap (𝓞 K) K z := by
      rw [IsScalarTower.coe_toAlgHom', hzeq, map_mul]
      rfl
    rw [hzK]
    exact RingOfIntegers.isIntegral_coe z
  obtain ⟨y, hyF⟩ : ∃ y : 𝓞 F, (y : F) = (t : F) * ((a : F) + c) := ⟨⟨_, hint⟩, rfl⟩
  have hyz : algebraMap (𝓞 F) (𝓞 K) y = z := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hzeq]
    show algebraMap F K (y : F) = _
    rw [hyF, map_mul]
    rfl
  have hy2 : y ∈ 𝔭 ^ (2 * vF 𝔭 a) := (idealPowerSpanBounds.mem_pow_iff (K := K) _ _ _).mp (hyz ▸ hz)
  have hy1 : y ∈ 𝔭 ^ (vF 𝔭 a + 1) := Ideal.pow_le_pow_right (by omega) hy2
  obtain ⟨C, hCdef⟩ : ∃ C : 𝓞 F, C = y - t * a := ⟨_, rfl⟩
  have hCF : (C : F) = (t : F) * c := by
    rw [hCdef]
    push_cast
    linear_combination hyF
  have hC1 : C ∈ 𝔭 ^ vF 𝔭 a := by
    rw [hCdef]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) hy2) (Ideal.mul_mem_left _ _ hmem)
  have hta : t * a ∉ 𝔭 ^ (0 + vF 𝔭 a + 1) :=
    idealPowerSpanBounds.mul_notMem h𝔭.isPrime hne (by rw [zero_add, pow_one]; exact ht) hnot
  have hC2 : C ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
    intro h
    apply hta
    rw [zero_add]
    have hta' : t * a = y - C := by rw [hCdef]; ring
    rw [hta']
    exact Ideal.sub_mem _ hy1 h
  obtain ⟨b, hb, hbC⟩ := exists_unit_mul_pow_eq_pow_mul_of_isUnif0 h𝔭 hu hC1 hC2
  have hC0 : C ≠ 0 := fun h => hC2 (h ▸ Submodule.zero_mem _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : (C : F) = 0 := by rw [hCF, mul_zero]
    exact hC0 (by exact_mod_cast h0)
  have hcK : algebraMap F K c ≠ 0 := (map_ne_zero _).mpr hc0
  refine ⟨hcK, mem_SP.mpr ⟨b, hb, algebraMap (𝓞 F) (𝓞 K) (t * s₀ ^ vF 𝔭 a), ?_⟩⟩
  show algebraMap F K ((t * s₀ ^ vF 𝔭 a : 𝓞 F) : F) =
    algebraMap F K (b : F) * ((algebraMap F K c)⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 a)
  have h2 := congrArg (fun x : 𝓞 F => (x : F)) hbC
  push_cast at h2
  have h3 : (b : F) * (π : F) ^ vF 𝔭 a = (s₀ : F) ^ vF 𝔭 a * ((t : F) * c) := by
    rw [← hCF]
    exact_mod_cast h2
  have hbK : algebraMap F K (b : F) * algebraMap F K (π : F) ^ vF 𝔭 a =
      algebraMap F K (s₀ : F) ^ vF 𝔭 a * (algebraMap F K (t : F) * algebraMap F K c) := by
    have h4 := congrArg (algebraMap F K) h3
    simpa [map_mul, map_pow] using h4
  have hc : ((t * s₀ ^ vF 𝔭 a : 𝓞 F) : F) = (t : F) * (s₀ : F) ^ vF 𝔭 a := by simp
  rw [hc, map_mul, map_pow, ← mul_assoc, mul_comm (algebraMap F K (b : F)), mul_assoc, hbK]
  field_simp

theorem pair_solve {q a c r X Y : K} (hq : q ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hr : a + c = q ^ 2 * r) :
    (X * q * (a⁻¹ * q) - Y * (a⁻¹ * q)) * (q⁻¹ ^ 2 * (a + c)) +
        (Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q)) * (q⁻¹ * c) = X ∧
      (X * q * (a⁻¹ * q) - Y * (a⁻¹ * q)) * (q⁻¹ * c) +
        (Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q)) * c = Y := by
  obtain rfl : c = q ^ 2 * r - a := by rw [← hr]; ring
  constructor
  · field_simp
    ring
  · field_simp
    ring

theorem pair_coeffs_mem {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {q a c r X Y : K}
    (hp : q ∈ SP K 𝔭) (hua : a⁻¹ * q ∈ SP K 𝔭) (huc : c⁻¹ * q ∈ SP K 𝔭) (hr : r ∈ SP K 𝔭)
    (hX : X ∈ SP K 𝔭) (hY : Y ∈ SP K 𝔭) :
    X * q * (a⁻¹ * q) - Y * (a⁻¹ * q) ∈ SP K 𝔭 ∧
      Y * r * (a⁻¹ * q) * (c⁻¹ * q) - X * (a⁻¹ * q) ∈ SP K 𝔭 := by
  exact ⟨(SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hX hp) hua) ((SP K 𝔭).mul_mem hY hua),
    (SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hY hr) hua) huc)
      ((SP K 𝔭).mul_mem hX hua)⟩

section Vec

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_locF_of_SP {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {L : Submodule (𝓞 K) V} {r : K}
    (hr : r ∈ SP K 𝔭) {v : V} (hv : v ∈ L) : r • v ∈ locF 𝔭 L := by
  obtain ⟨t, ht, z, hz⟩ := mem_SP.mp hr
  refine ⟨algebraMap (𝓞 F) (𝓞 K) t, Submonoid.subset_closure ⟨t, ht, rfl⟩, ?_⟩
  have he : algebraMap (𝓞 F) (𝓞 K) t • r • v = z • v := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (r • v), smul_smul, ← hz, algebraMap_smul]
  rw [he]
  exact L.smul_mem z hv

theorem eq_zero_of_orth {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) {ι' : Type}
    (G : ι' → V) (hG : Submodule.span K (Set.range G) = ⊤) {z : V} (hz : ∀ s, h (G s) z = 0) :
    z = 0 := by
  apply hnd
  intro y
  have hy : y ∈ Submodule.span K (Set.range G) := hG ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [← hs.eq, hz s, map_zero]
  | zero => simp
  | add x w _ _ hx hw => rw [map_add, hx, hw, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

end Vec

end Formalism.L2.SG.Pf.UnitPairSolutions
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TotallyPositiveAll
section
noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem emb_surj (D : Formalism.BasicNotions.D7) : Function.Surjective D.host.emb := by
  intro φ
  unfold Formalism.BasicNotions.Host.emb Formalism.BasicNotions.Host.sigmaOf

  have key : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, D.host.φ₀.comp (σ : D.host.E →+* D.host.E) = φ := by
    classical
    let f : (D.host.E ≃ₐ[ℚ] D.host.E) → (D.host.E →ₐ[ℚ] ℂ) :=
      fun σ => (D.host.φ₀.toRatAlgHom).comp (σ : D.host.E →ₐ[ℚ] D.host.E)
    have hinj : Function.Injective f := by
      intro σ τ h
      ext x
      have h1 : D.host.φ₀ (σ x) = D.host.φ₀ (τ x) := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) h
      exact D.host.φ₀.injective h1
    have hcard : Fintype.card (D.host.E ≃ₐ[ℚ] D.host.E) = Fintype.card (D.host.E →ₐ[ℚ] ℂ) := by
      haveI : IsGalois ℚ D.host.E := inferInstance
      rw [AlgHom.card ℚ D.host.E ℂ, ← IsGalois.card_aut_eq_finrank ℚ D.host.E, Fintype.card_eq_nat_card]
    obtain ⟨σ, hσ⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 φ.toRatAlgHom
    refine ⟨σ, ?_⟩
    ext x
    have h2 : D.host.φ₀ (σ x) = φ x := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) hσ
    exact h2
  obtain ⟨σ, hσ⟩ := key
  refine ⟨D.host.gal σ, ?_⟩
  simp only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hσ

theorem totally_positive_all : TotPosAll := by
  intro D x hx hpos φ
  obtain ⟨g, rfl⟩ := emb_surj D φ
  by_cases hg : g ∈ D.R.Psi
  · have h1 := hpos (D.eTau.symm ⟨g, hg⟩)
    simpa using h1
  · have hmem : g * D.R.cc ∈ D.R.Psi := by
      rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
      have h2 : g.1.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
      rw [Prod.fst_mul, Prod.snd_mul, h2]
      first
        | rfl
        | decide
        | (simp [Formalism.HC.Frame.cc]; done)
        | (simp [Formalism.HC.Frame.cc, Formalism.HC.c0])
    have h1 := hpos (D.eTau.symm ⟨g * D.R.cc, hmem⟩)
    simp only [Equiv.apply_symm_apply] at h1
    have hc : D.host.conj x = x := (Formalism.MainNotions.S.Inh.tie_star D x).symm.trans hx
    have he : D.host.emb (g * D.R.cc) x = D.host.emb g x := by
      change D.host.φ₀ ((D.host.gal.symm (g * D.R.cc)) x) = D.host.φ₀ ((D.host.gal.symm g) x)
      rw [map_mul, AlgEquiv.mul_apply]
      congr 2
    rw [he] at h1
    exact h1

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem rational_pair_holds : RatPair := ratPair_of R1.totally_positive_all

end Formalism.L2.SG.Pf.Cnt
end
end

