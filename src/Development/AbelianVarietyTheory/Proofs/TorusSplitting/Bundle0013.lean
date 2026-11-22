import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsPerfectTraceIdeal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn.PerfectTrace

open FractionalIdeal

theorem cc_eq_conj (D : D7) (z : D.host.E) : FD.cc z = D.host.conj z := by
  unfold FD.cc
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isIntegral_of_trace (D : D7) (x : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∀ b ∈ D.host.AA,
      ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * D.host.conj b) = z) :
    IsIntegral ℤ x := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    @one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _
  have key : ∀ e ∈ D.host.AA * D.host.AAbar, D.host.xi0 * x * e ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro e he
    refine FractionalIdeal.mul_induction_on (C := fun e => D.host.xi0 * x * e ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) he
      (fun a ha b hb => ?_) (fun u w hu hw => ?_)
    · show D.host.xi0 * x * (a * b) ∈ _
      rw [mem_dual h1ne]
      intro c hc
      rw [mem_one_iff] at hc
      obtain ⟨c, rfl⟩ := hc
      have hca : c • a ∈ D.host.AA := (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      obtain ⟨n, hn⟩ := h _ hca _ (conj_mem_AA D hb)
      rw [conj_conj, Algebra.smul_def] at hn
      rw [Algebra.traceForm_apply, show D.host.xi0 * x * (a * b) * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * x * (algebraMap (𝓞 D.host.E) D.host.E c * a) * b by ring, hn]
      exact ⟨n, eq_intCast (algebraMap ℤ ℚ) _⟩
    · show D.host.xi0 * x * (u + w) ∈ _
      rw [mul_add]
      exact (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).add_mem hu hw
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    conv_lhs => rw [← dual_eq hP D, mul_assoc, ← mul_assoc, spanSingleton_mul_spanSingleton, mul_comm x]
    rw [spanSingleton_mul_le_iff]
    exact key
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  generalize FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = J at hle hJ
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ 1 := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = J⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * J) := by
          rw [mul_comm _ J, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]
      _ ≤ J⁻¹ * J := CovariantClass.elim J⁻¹ hle
      _ = 1 := inv_mul_cancel₀ hJ
  have hx := hle2 (mem_spanSingleton_self _ _)
  obtain ⟨c, rfl⟩ := (mem_one_iff _).1 hx
  exact c.isIntegral_coe

theorem exists_perfect_trace_ideal :
    ∀ (D : D7), ∃ (ξ : D.host.E) (AA : Submodule (𝓞 D.host.E) D.host.E), FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧ AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ D.host.E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  refine ⟨D.host.xi0, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), conj_xi0_alt D, cmHost_imaginaryGenerator_ne_zero hP D,
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (AA_ne_zero hP D)), ?_, fun x => ⟨fun h => ?_, fun hx a ha b hb => ?_⟩⟩
  · intro h
    exact AA_ne_zero hP D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  · refine isIntegral_of_trace D x (fun a ha b hb => ?_)
    rw [← cc_eq_conj]
    exact h a ha b hb
  · have hxa : (⟨x, hx⟩ : 𝓞 D.host.E) • a ∈ D.host.AA :=
      (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha
    have hm : x * a * D.host.conj b ∈ NAA D := mul_mem_mul hxa (conj_mem_AAbar D hb)
    obtain ⟨n, hn⟩ := trace_int_of_mem hP D hm
    refine ⟨n, ?_⟩
    rw [cc_eq_conj, ← hn]
    congr 1; ring

end GlobalTheory.EtaAn.PerfectTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem page_rows : ∀ (D : D7) (large₂ : SizeData₂ D) (CA : ℝ), WeightAlgebra.ParA large₂ CA → SizesAt large₂ → 2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f := by
  intro D large₂ CA hA hS
  have hm4 := host_m_pow_four_le_f hS
  rw [hostSize_f] at hm4
  have hm2 := D.R.two_le_m
  have h16 : 16 ≤ D.R.f := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    omega
  have hC : SizeCond large₂ := hS.2.2.2.2.2.1
  have hQ : SizeQD large₂ := hS.2.2.2.2.2.2.1
  have hrd1 : 1 ≤ D.host.rdE := hQ.2.2.2.2.2.2.1
  have hrd2 : D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := hQ.2.2.2.2.2.2.2
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by
    have h0 : D.host.q * D.host.d ≠ 0 := by
      intro h
      have h' : (D.host.q : ℝ) * D.host.d = 0 := by exact_mod_cast h
      rw [h', Real.sqrt_zero, mul_zero] at hrd2
      linarith
    have : 1 ≤ D.host.q * D.host.d := Nat.one_le_iff_ne_zero.mpr h0
    exact_mod_cast this
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : szCond large₂ = (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by
    unfold szCond; ring
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hfc : (D.R.f : ℝ) ≤ szCond large₂ := by
    have h4 : ((4 * D.R.n : ℕ) : ℝ) ≤ ((D.host.QS * D.host.q * D.host.d : ℕ) : ℝ) := Nat.cast_le.2 D.host.four_ord_le_condN
    push_cast at h4
    rw [hc, hfn]; nlinarith
  have hrc : D.host.rdE ≤ szCond large₂ := by
    rw [hc]
    have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h0 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
    nlinarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by linarith
  have hc1 : 1 ≤ szCond large₂ := le_trans hf1 hfc
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have ht3 : (3 : ℝ) ≤ D.R.t := by
    have : 3 ≤ D.R.t := by omega
    exact_mod_cast this
  have hrt' : (D.R.r : ℝ) ≤ D.R.t := by
    have : D.R.r ≤ D.R.t := by omega
    exact_mod_cast this
  have hr1' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hlt : 1 ≤ Real.log D.R.t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlc : 0 ≤ Real.log (szCond large₂) := Real.log_nonneg hc1
  have hmain : 36 * Real.log (szCond large₂) + 150 * Real.log D.R.t ≤ large₂.sc.L / 2 := by
    have h1 : Real.sqrt large₂.sc.b = Real.exp (large₂.sc.L / 2) := by
      unfold Scale.b
      rw [Real.exp_half]
    have h2 : szCond large₂ ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.exp (large₂.sc.L / 2) := h1 ▸ hC
    have hp : 0 < szCond large₂ ^ 36 := by positivity
    have hp' : 0 < (D.R.t : ℝ) ^ 150 := by positivity
    have h3 := Real.log_le_log (mul_pos hp hp') h2
    rw [Real.log_exp, Real.log_mul hp.ne' hp'.ne', Real.log_pow, Real.log_pow] at h3
    exact_mod_cast h3
  have a1 : Real.log D.R.r ≤ Real.log D.R.t := Real.log_le_log (by linarith) hrt'
  have a2 : Real.log D.host.rdE ≤ Real.log (szCond large₂) := Real.log_le_log (by linarith) hrc
  have a3 : Real.log D.R.f ≤ Real.log (szCond large₂) := Real.log_le_log (by linarith) hfc
  refine ⟨by linarith, by linarith, by linarith, by linarith, hA.2.2.2.2.1, h16⟩

end GlobalTheory.EtaAn
end

