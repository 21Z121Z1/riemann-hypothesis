import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def HeckeRatioExpansion.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (k : ℕ),
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) ∧
      HasIntegralLaurentQExpansion (fun τ : ℍ ↦ (heckeRatios ⟨p, hp.pos⟩ τ).esymm k)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

open UpperHalfPlane
open scoped Manifold

def HeckeRatioHolo.Statement : Prop :=
  ∀ (n : ℕ+) (k : ℕ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ (heckeRatios n τ).esymm k)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def HeckeRatioInvariant.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (γ : SL(2, ℤ)) (τ : ℍ),
    heckeRatios ⟨p, hp.pos⟩ (γ • τ) = heckeRatios ⟨p, hp.pos⟩ τ

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.JQExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic

noncomputable section

def JQExpansion.Statement : Prop :=
  ∃ c : ℕ → ℤ, c 0 = 1 ∧ ∀ τ : ℍ,
    HasSum (fun n ↦ (c n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ * modularJ τ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LevelOneQExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def LevelOneQExpansion.Statement : Prop :=
  ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) →
    HasIntegralLaurentQExpansion f → ∃ Q : ℤ[X], ∀ τ : ℍ, f τ = aeval (modularJ τ) Q

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassMeanOverEmbeddings
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem ClassMeanOverEmbeddings.proof (S : PrimeDiscriminant K) (F : CMFamily K)
    (hMean : MeanOverEmbeddings.Statement S F) (hScale : PhScale.Statement)
    (hConj : PhConj.Statement) : ClassMeanOverEmbeddings.Statement S F := by
  intro σ
  have := S.isTotallyComplex
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

  have hhom : ∀ (τ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : Submodule ℤ ℂ) (c : ℂ),
      c ≠ 0 → (Λ : Set ℂ) = (c * ·) '' idealLattice τ J →
        logPeriod Λ = logPeriod (idealLattice τ J) := by
    intro τ J Λ c hc h
    have e : Λ = scaleLattice c (idealPeriodPair τ hK J).lattice := by
      apply SetLike.coe_injective
      rw [h, scaleLattice, Submodule.map_coe, lattice_idealPeriodPair]
      rfl
    rw [e, hScale _ c hc, lattice_idealPeriodPair]

  have hcls : ∀ (τ : K →+* ℂ) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
      logPeriod (idealLattice τ 𝔟) = classLogPeriod τ (ClassGroup.mk K 𝔟) := by
    intro τ 𝔟
    have hJ : ClassGroup.mk K 𝔟 =
        ClassGroup.mk K (FractionalIdeal.mk0 K (classRep (ClassGroup.mk K 𝔟))) := by
      rw [ClassGroup.mk_mk0, mk0_classGroupRep]
    obtain ⟨c, hc, h⟩ := (classGroup_mk_eq_iff τ hK _ _).1 hJ
    rw [classLogPeriod, classLattice, ← FractionalIdeal.coe_mk0, hhom τ 𝔟 _ c hc h]

  have hconj : ∀ τ : K →+* ℂ, classMean τ = classMean σ := by
    intro τ
    rcases S.eq_or_eq_conjugate σ τ with rfl | rfl
    · rfl
    · unfold classMean
      congr 1
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      rw [classLogPeriod, classLogPeriod, classLattice, classLattice, idealLattice_conjugate,
        ← FractionalIdeal.coe_mk0, ← lattice_idealPeriodPair σ hK, hConj]

  have hs : ∀ s : F.k →+* ℂ, (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K),
      logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
        F.periodLattice s) = classMean σ := by
    intro s
    obtain ⟨I, c, hc, h⟩ := F.exists_periodLattice_eq S s
    have e : ∀ C : ClassGroup (𝓞 K),
        logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
          F.periodLattice s) = classLogPeriod (F.restrict s) (C * ClassGroup.mk K I) := by
      intro C
      have h' := idealLattice_mul_homothetic (F.restrict s) (I : FractionalIdeal (𝓞 K)⁰ K)
        (↑(FractionalIdeal.mk0 K (classRep C))) h
      rw [← Units.val_mul] at h'
      rw [hhom _ _ _ c hc h', hcls, map_mul, ClassGroup.mk_mk0, mk0_classGroupRep]
    rw [Finset.sum_congr rfl fun C _ ↦ e C,
      Fintype.sum_equiv (Equiv.mulRight (ClassGroup.mk K I))
        (fun C ↦ classLogPeriod (F.restrict s) (C * ClassGroup.mk K I)) (classLogPeriod (F.restrict s))
        (fun C ↦ rfl)]
    exact hconj _
  have hN : (Fintype.card (F.k →+* ℂ) : ℝ) ≠ 0 := by
    have : Nonempty (F.k →+* ℂ) := ⟨(IsAlgClosed.lift : F.k →ₐ[ℚ] ℂ).toRingHom⟩
    exact_mod_cast Fintype.card_ne_zero
  have hh : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast classNumber_ne_zero K

  calc embMean F.k (fun s ↦ logPeriod (F.periodLattice s))
      = (classNumber K : ℝ)⁻¹ * ∑ _C : ClassGroup (𝓞 K),
          embMean F.k (fun s ↦ logPeriod (F.periodLattice s)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact (inv_mul_cancel_left₀ hh _).symm
    _ = (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K), embMean F.k (fun s ↦
          logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
            F.periodLattice s)) := by
        congr 1
        exact Finset.sum_congr rfl fun C _ ↦ (hMean _).symm
    _ = embMean F.k (fun s ↦ (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K),
          logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
            F.periodLattice s)) := by
        simp only [embMean, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = classMean σ := by
        simp only [hs, embMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PCotangentSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Complex ComplexConjugate
open scoped Real

theorem CotangentSum.pair_identity (w w' N : ℂ) (h1 : w + N ≠ 0) (h2 : w - N ≠ 0)
    (h3 : w' + N ≠ 0) (h4 : w' - N ≠ 0) (h5 : w - w' ≠ 0) :
    ((w + N) * (w' + N))⁻¹ + ((w - N) * (w' - N))⁻¹ =
      (w - w')⁻¹ * ((1 / (w' - N) + 1 / (w' + N)) - (1 / (w - N) + 1 / (w + N))) := by
  field_simp
  ring

theorem CotangentSum.proof : CotangentSum.Statement := by
  intro a u ha
  have hne : ∀ x : ℂ, x.im ≠ 0 → x ≠ 0 := fun x hx h => hx (by simp [h])
  have hmem : ∀ x : ℂ, x.im ≠ 0 → x ∈ Complex.integerComplement := by
    rintro x hx ⟨n, hn⟩
    apply hx
    rw [← hn]
    simp
  have ha0 : (a : ℝ) ≠ 0 := ha.ne'
  set w : ℂ := (u : ℂ) + (a : ℂ) * I with hw
  set w' : ℂ := (u : ℂ) - (a : ℂ) * I with hw'
  have hwim : w.im = a := by simp [hw]
  have hw'im : w'.im = -a := by simp [hw']
  have hconj : conj w = w' := by
    rw [hw, hw', map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
    ring
  have hdiff : w - w' = 2 * (a : ℂ) * I := by rw [hw, hw']; ring
  have hdiff0 : w - w' ≠ 0 := by
    rw [hdiff]; exact mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr ha0)) I_ne_zero

  let F : ℤ → ℂ := fun n => ((w + n) * (w' + n))⁻¹
  have hF : ∀ n : ℤ, ((((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) : ℝ) = F n := by
    intro n
    have e : (w + n) * (w' + n) = ((n : ℂ) + u) ^ 2 + (a : ℂ) ^ 2 := by
      rw [hw, hw']
      linear_combination (-(a : ℂ) ^ 2) * I_sq
    simp only [F, e, Real.rpow_neg_one]
    push_cast
    rfl
  have hsum : Summable F := by
    have h := (EisensteinSeries.linear_inv_isBigO_right 1 w').mul
      (EisensteinSeries.linear_inv_isBigO_right 1 w)
    refine EisensteinSeries.summable_inv_of_isBigO_rpow_inv (f := fun n : ℤ => (w + n) * (w' + n))
      (a := 2) (by norm_num) ?_
    simpa [pow_two, mul_inv] using! h

  have h1 := tsum_nat_add_neg hsum
  have h2 := (hsum.nat_add_neg).tsum_eq_zero_add
  have hterm : ∀ n : ℕ, F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ)) =
      (w - w')⁻¹ * (cotTerm w' n - cotTerm w n) := by
    intro n
    have hN : ∀ x : ℂ, x.im ≠ 0 → x + ((n : ℂ) + 1) ≠ 0 ∧ x - ((n : ℂ) + 1) ≠ 0 := by
      intro x hx
      refine ⟨hne _ ?_, hne _ ?_⟩ <;> simpa using hx
    have := CotangentSum.pair_identity w w' ((n : ℂ) + 1)
      (hN w (by rw [hwim]; exact ha0)).1 (hN w (by rw [hwim]; exact ha0)).2
      (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).1
      (hN w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)).2 hdiff0
    simp only [F, cotTerm]
    push_cast
    simp only [← sub_eq_add_neg]
    rw [← this]
  have hw_mem : w ∈ Complex.integerComplement := hmem w (by rw [hwim]; exact ha0)
  have hw'_mem : w' ∈ Complex.integerComplement :=
    hmem w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)
  have h3 : ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) =
      (w - w')⁻¹ * ((π * cot (π * w') - 1 / w') - (π * cot (π * w) - 1 / w)) := by
    rw [tsum_congr hterm, tsum_mul_left,
      Summable.tsum_sub (summable_cotTerm hw'_mem) (summable_cotTerm hw_mem),
      cot_series_rep' hw'_mem, cot_series_rep' hw_mem]
  have hF0 : F 0 = (w - w')⁻¹ * (1 / w' - 1 / w) := by
    simp only [F, Int.cast_zero, add_zero]
    have := hne w (by rw [hwim]; exact ha0)
    have := hne w' (by rw [hw'im]; exact neg_ne_zero.mpr ha0)
    field_simp
  have hS : ∑' n : ℤ, F n = (w - w')⁻¹ * (π * cot (π * w') - π * cot (π * w)) := by
    have h2' : ∑' n : ℕ, (F n + F (-n)) =
        (F 0 + F 0) + ∑' n : ℕ, (F ((n + 1 : ℕ) : ℤ) + F (-((n + 1 : ℕ) : ℤ))) := by
      rw [h2]; simp
    rw [h2', h3] at h1
    rw [hF0] at h1
    linear_combination -h1

  have hwH : 0 < w.im := by rw [hwim]; exact ha
  have hq := pi_mul_cot_pi_q_exp ⟨w, hwH⟩
  simp only at hq
  set q : ℂ := Complex.exp (2 * π * I * w) with hqdef
  have hqn : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hwH⟩
  have hgeo : ∑' n : ℕ, q ^ n = 1 + ∑' k : ℕ, q ^ (k + 1) := by
    rw [(summable_geometric_of_norm_lt_one hqn).tsum_eq_zero_add]; simp
  set T : ℂ := ∑' k : ℕ, q ^ (k + 1) with hT
  have hcot' : π * cot (π * w') = conj (π * cot (π * w)) := by
    rw [map_mul, conj_ofReal, ← cot_conj, map_mul, conj_ofReal, hconj]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, tsum_congr hF, hS, hcot', hq, hgeo]
  have hTc : T + conj T = 2 * (T.re : ℂ) := by rw [Complex.add_conj]; push_cast; ring
  simp only [map_sub, map_mul, map_add, conj_ofReal, conj_I, map_one, map_ofNat]
  rw [hdiff]
  have hI : I ≠ 0 := I_ne_zero
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha0
  push_cast
  field_simp
  linear_combination 2 * hTc
end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PGammaZetaLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real

noncomputable section

theorem tendsto_tsum_one_div_rpow_sub_one_div :
    Tendsto (fun w : ℝ ↦ (∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ w)) - 1 / (w - 1)) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have h := (Complex.continuous_re.tendsto _).comp
    ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  simp only [Complex.ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : (1 : ℝ) < w := hw
  simp only [Function.comp_apply]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hw')]
  have : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (w : ℂ)) = ((∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ w) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1 with n
    rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring
  rw [this]
  have h1 : ((1 : ℂ) / ((w : ℂ) - 1)) = (((1 : ℝ) / (w - 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_sub, Complex.ofReal_re]

theorem GammaZetaLimit.proof : GammaZetaLimit.Statement := by
  intro y hy
  set F : ℝ → ℝ := fun s ↦ √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * y ^ (1 - s) with hF
  have hs2 : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have h12 : Real.Gamma (1 - 1 / 2) = √π := by norm_num [Real.Gamma_one_half_eq]

  have hG12 : HasDerivAt (fun s : ℝ ↦ Real.Gamma (s - 1 / 2))
      (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2)) 1 := by
    have h : HasDerivAt Real.Gamma (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2))
        ((1 : ℝ) - 1 / 2) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      exact Real.hasDerivAt_Gamma_one_half
    exact h.comp_sub_const 1 (1 / 2)
  have hY : HasDerivAt (fun s : ℝ ↦ y ^ (1 - s)) (-Real.log y) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 1).const_rpow hy
  have hΓ1 : Real.Gamma 1 ≠ 0 := by simp
  have hFd : HasDerivAt F (-2 * π * Real.log 2 - π * Real.log y) 1 := by
    have h := ((hG12.div Real.hasDerivAt_Gamma_one hΓ1).const_mul √π).mul hY
    have e1 : ((fun t : ℝ ↦ √π * ((fun s : ℝ ↦ Real.Gamma (s - 1 / 2)) / Real.Gamma) t) *
        fun s : ℝ ↦ y ^ (1 - s)) = F := by
      funext s
      simp only [hF, Pi.mul_apply, Pi.div_apply]
      ring
    rw [e1] at h
    refine h.congr_deriv ?_
    simp only [h12, Real.Gamma_one, Pi.div_apply, one_pow, div_one, mul_one, sub_self,
      Real.rpow_zero]
    linear_combination (-(2 * Real.log 2 + Real.log y)) * hs2
  have hF1 : F 1 = π := by
    simp only [hF, h12, Real.Gamma_one, sub_self, Real.rpow_zero, div_one, mul_one]
    exact hs2

  have hslope : Tendsto (fun s ↦ (F s - π) / (s - 1)) (𝓝[>] 1)
      (𝓝 (-2 * π * Real.log 2 - π * Real.log y)) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hFd).mono_left
      (nhdsWithin_mono _ (fun x (hx : (1 : ℝ) < x) ↦ hx.ne'))
    refine this.congr' (Eventually.of_forall fun s ↦ ?_)
    rw [slope_def_field, hF1]
  have hFc : Tendsto F (𝓝[>] 1) (𝓝 π) :=
    hF1 ▸ hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝 1) (𝓝 (2 * 1 - 1)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) < s)
      show (1 : ℝ) < 2 * s - 1
      linarith
  have hZ := tendsto_tsum_one_div_rpow_sub_one_div.comp hmap
  have hlim := hslope.add ((hFc.const_mul 2).mul hZ)
  have hval : -2 * π * Real.log 2 - π * Real.log y + 2 * π * Real.eulerMascheroniConstant =
      2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) < s)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  have key : ∀ A Z : ℝ, (A - π) / (s - 1) + 2 * A * (Z - 1 / (2 * s - 1 - 1)) =
      2 * A * Z - π / (s - 1) := by
    intro A Z
    rw [show 2 * s - 1 - 1 = 2 * (s - 1) by ring]
    field_simp
    ring
  simp only [Function.comp_apply]
  rw [key]
  simp only [hF]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLogEta
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology Complex
open scoped Real UpperHalfPlane ModularForm

noncomputable section

theorem LogEta.proof : LogEta.Statement := by
  intro τ
  set q : ℂ := Complex.exp (2 * π * Complex.I * (τ : ℂ)) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hpow : ∀ k : ℕ, ‖q ^ (k + 1)‖ < 1 := fun k ↦ by
    rw [norm_pow]; exact pow_lt_one₀ hr0 hq1 (Nat.succ_ne_zero k)

  let F : ℕ × ℕ → ℂ := fun p ↦ ((1 / (p.1 + 1 : ℝ) : ℝ) : ℂ) * q ^ ((p.1 + 1) * (p.2 + 1))
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ ↦ ‖q‖ ^ p.1 * ‖q‖ ^ p.2)
      (Summable.mul_of_nonneg (summable_geometric_of_lt_one hr0 hq1)
        (summable_geometric_of_lt_one hr0 hq1) (fun _ ↦ pow_nonneg hr0 _)
        (fun _ ↦ pow_nonneg hr0 _)) ?_
    rintro ⟨m, k⟩
    simp only [F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [← pow_add]
    have h1 : |1 / ((m : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      exact div_le_one_of_le₀ (by linarith [m.cast_nonneg (α := ℝ)]) (by positivity)
    have h2 : ‖q‖ ^ ((m + 1) * (k + 1)) ≤ ‖q‖ ^ (m + k) :=
      pow_le_pow_of_le_one hr0 hq1.le (by nlinarith)
    calc _ ≤ 1 * ‖q‖ ^ (m + k) := mul_le_mul h1 h2 (pow_nonneg hr0 _) zero_le_one
      _ = _ := one_mul _
  set T := ∑' p, F p

  have hA : HasSum (fun m : ℕ ↦ ∑' k : ℕ, F (m, k)) T :=
    hFs.hasSum.prod_fiberwise fun m ↦ (hFs.prod_factor m).hasSum

  have hcol : ∀ k : ℕ, HasSum (fun m : ℕ ↦ F (m, k)) (-Complex.log (1 - q ^ (k + 1))) := by
    intro k
    convert hasSum_taylorSeries_neg_log' (hpow k) using 1
    ext m
    simp only [F]
    rw [← pow_mul, mul_comm (k + 1)]
    push_cast
    ring
  have hB : HasSum (fun k : ℕ ↦ -Complex.log (1 - q ^ (k + 1))) T := by
    have hsw : HasSum (F ∘ Prod.swap) T :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hFs.hasSum
    exact hsw.prod_fiberwise fun k ↦ hcol k

  have hne : ∀ k : ℕ, 1 - q ^ (k + 1) ≠ 0 := fun k ↦
    sub_ne_zero.mpr (ne_of_apply_ne norm (by rw [norm_one]; exact (hpow k).ne)).symm
  have hlog : HasSum (fun k : ℕ ↦ Real.log ‖1 - q ^ (k + 1)‖) (-T.re) := by
    have := (Complex.hasSum_re hB).neg
    simpa only [neg_re, Complex.log_re, neg_neg] using this
  have hprod : HasProd (fun k : ℕ ↦ ‖1 - q ^ (k + 1)‖) (Real.exp (-T.re)) := by
    convert hlog.rexp using 1
    ext k
    simp only [Function.comp_apply]
    rw [Real.exp_log (norm_pos_iff.mpr (hne k))]
  have hnorm : ‖∏' k : ℕ, (1 - q ^ (k + 1))‖ = Real.exp (-T.re) :=
    (ModularForm.multipliable_one_sub_pow hq1).hasProd.norm.unique hprod
  have heta : ‖η (τ : ℂ)‖ = Real.exp (-2 * π * (τ : ℂ).im / 24) * Real.exp (-T.re) := by
    rw [ModularForm.eta, norm_mul, Function.Periodic.norm_qParam, ← hnorm]
    congr 2
    refine tprod_congr fun n ↦ ?_
    rw [ModularForm.eta_q_eq_pow]
  have hlogeta : Real.log ‖η (τ : ℂ)‖ = -2 * π * τ.im / 24 - T.re := by
    rw [heta, ← Real.exp_add, Real.log_exp, UpperHalfPlane.coe_im]
    ring
  rw [hlogeta]
  convert Complex.hasSum_re hA using 1
  · ext m
    simp only [F]
    rw [tsum_mul_left, re_ofReal_mul]
  · ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

