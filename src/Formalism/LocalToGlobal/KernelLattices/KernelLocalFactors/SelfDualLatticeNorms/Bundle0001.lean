import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IntCurveOfScale
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.E (IntCurve curveL)

theorem intCurve_of_scale (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (h : IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)) (hΔ : ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1) :
    IntCurve (curveL p L ι) := by
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have h2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have h3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, h4, h6, hD⟩ := h
  have hS := fun g2 g3 : ℂ_[p] => (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have hιc : ι c ≠ 0 := by simpa using hc
  have hcn : ‖ι c‖ = 1 := by
    unfold curveL at hD
    rw [hS, h2, h3] at hD
    have e : ι ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ι ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (ι c ^ 12)⁻¹ * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      simp only [map_mul, map_inv₀, map_pow, map_sub, map_ofNat]
      field_simp
    rw [e, norm_mul, hΔ, mul_one, norm_inv, norm_pow, inv_eq_one] at hD
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hD
  refine ⟨by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩
  · have e : (curveL p L ι).a₄ = ι c ^ 4 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₄ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h2, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h4
  · have e : (curveL p L ι).a₆ = ι c ^ 6 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₆ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h3, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h6
  · unfold curveL
    rw [hS]
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using hΔ

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem disc_one (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by
    rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) B.L hL
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem intCurve_base (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (ι : ℂ ≃+* ℂ_[p]) :
    IntCurve (curveL p B.L ι) := by
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
    intro ω hω
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω
    rwa [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.theta_val] at this
  have hd8 : D.host.d % 8 = 7 := dMod8 D
  obtain ⟨c, hc, hI⟩ := Formalism.L2.Th1.Top.good_model_exists_all_primes D.host.d B.L D.host.hyp.2.1.squarefree (by omega) hcm p hp ι
  refine intCurve_of_scale p ι B.L c hc hI ?_
  rw [disc_one B hcc hδ, map_one, norm_one]

theorem chiFac_unit (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') (h1 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L) (h2 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L') :
    ‖ι (Base.chiFac χ N N' L L')‖ = 1 := by
  obtain ⟨hq, hn⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.chiFacUnit χ hχ p ((ι : ℂ →+* ℂ_[p]).comp (algebraMap TaylorLogMetric.Qbar ℂ)) N N' L L' hA h1 h2
  unfold TaylorLogMetric.lamC at hn
  rw [dif_pos hq] at hn
  exact hn

end Formalism.L2.Ker.KS
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK kernel4 F0 stdLat alphaQ)

section Gen

variable {L L' : PeriodPair} {ω₀ ω₀' : ℂ}

theorem thetaNull_congr_lattice (h : L.lattice = L'.lattice) (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) :
    Formalism.L2.Th1.F.th0 L (ω₀ / 2) = Formalism.L2.Th1.F.th0 L' (ω₀' / 2) := by
  obtain ⟨-, -, -, hA, -, hs, -⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  have e1 : Formalism.L2.Th1.F.th0 L (ω₀ / 2) = Formalism.L2.Th1.F.th0 L' (ω₀ / 2) := by
    funext z
    simp only [Formalism.L2.Th1.F.th0, Formalism.L2.Th1.F.opU, Formalism.L2.Th1.F.herm, hA, hs]
  rw [e1]
  funext z
  have := Formalism.L2.Th1.F.th0Class L' (ω₀' / 2) ((ω₀ - ω₀') / 2) z hω hn
  rw [← this]
  congr 1
  ring

theorem stdH_congr (h : L.lattice = L'.lattice) (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.L2.Th1.H.stdH L n = Formalism.L2.Th1.H.stdH L' n := by
  unfold Formalism.L2.Th1.H.stdH
  rw [(Formalism.L2.Th1.F.latticeOnly L L' h).2.2.2.1]

theorem hOne_congr (h : L.lattice = L'.lattice) (n : Type) [Fintype n] [DecidableEq n] : hOne L n = hOne L' n := by
  unfold hOne
  rw [(Formalism.L2.Th1.F.latticeOnly L L' h).2.2.2.1]

theorem thM_congr (h : L.lattice = L'.lattice) (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) (c : ℝ)
    {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (κ : ℂ) :
    thM L ω₀ c ΛM g κ = thM L' ω₀' c ΛM g κ := by
  have e : IsThM L ω₀ c ΛM g κ = IsThM L' ω₀' c ΛM g κ := by
    funext θ
    unfold IsThM kernel4 F0 Formalism.L2.Th1.H.stdLat
    rw [hOne_congr h, stdH_congr h, thetaNull_congr_lattice h hω hn, h]
  unfold thM
  rw [e]

end Gen

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def reBase (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) : Base D cc δ :=
  { B with L := L', lat := hl, ω₀ := ω₀', t0 := ht }

theorem lattice_eq (B B' : Base D cc δ) : B.L.lattice = B'.L.lattice := by
  have h : B.L.lattice.toAddSubgroup = B'.L.lattice.toAddSubgroup := B.lat.trans B'.lat.symm
  exact Submodule.toAddSubgroup_injective h

theorem thMM_reBase (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) (hω : (B.ω₀ - ω₀') / 2 ∈ L'.lattice) :
    B.thMM = (reBase B L' hl ω₀' ht).thMM :=
  thM_congr (lattice_eq B (reBase B L' hl ω₀' ht)) hω (Base.half_not_mem (reBase B L' hl ω₀' ht)) _ _ _ _

theorem eNat_reBase (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) (hω : (B.ω₀ - ω₀') / 2 ∈ L'.lattice) (χ : TaylorLogMetric.IdE D → ℂ) :
    B.eNat χ = (reBase B L' hl ω₀' ht).eNat χ := by
  funext N N' L L₁ z
  simp only [Base.eNat, Base.thMoved, Base.thHalf, Base.thZero, thMM_reBase B L' hl ω₀' ht hω]

theorem ambOf_reBase {X : Fields} (s : Seam D X) (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) (hω : (B.ω₀ - ω₀') / 2 ∈ L'.lattice) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    (ambOf s B χ cD : Amb X) = ambOf s (reBase B L' hl ω₀' ht) χ cD := by
  unfold ambOf
  rw [eNat_reBase B L' hl ω₀' ht hω χ]

section Re

open Formalism.L2.Th1.F (cmTheta)

variable (B : Base D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0)

theorem theta_val' (d : ℕ) : cmTheta 1 d = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
  simp [cmTheta]

theorem mem_lam_iff (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (x : ℂ) :
    x ∈ TaylorLogMetric.lamOf D cc δ ↔ x ∈ (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice := by
  rw [← hl]; rfl

theorem isTorsionPoint_standard_CM (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) :
    GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (lam * a₀ / 2) := by
  obtain ⟨h1, h2, h3⟩ := half_period_standard_CM a₀ b₀ c₀ D.host.d ha hd lam hlam hcm
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - cmTheta 1 D.host.d := by rw [theta_val']; ring
  refine ⟨(mem_lam_iff a₀ b₀ ha hd lam hlam hl _).2 h1, ?_, ?_⟩
  · rw [mem_lam_iff a₀ b₀ ha hd lam hlam hl, ← theta_val']; exact h2
  · rw [mem_lam_iff a₀ b₀ ha hd lam hlam hl, e]; exact h3

def cmBase (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) : Base D cc δ :=
  reBase B (cmL a₀ b₀ D.host.d ha hd lam hlam) hl (lam * a₀) (isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd lam hlam hcm hl)

theorem cmBase_isCm (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) :
    (cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl).IsCm a₀ b₀ ha hd lam hlam := ⟨rfl, rfl⟩

theorem ambOf_cmBase {X : Fields} (s : Seam D X) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    (ambOf s B χ cD : Amb X) = ambOf s (cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl) χ cD := by
  refine ambOf_reBase s B _ hl _ _ ?_ χ cD
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - cmTheta 1 D.host.d := by rw [theta_val']; ring
  have h := half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (B.ω₀ / 2)
    ((mem_lam_iff a₀ b₀ ha hd lam hlam hl _).1 B.t0.1)
    (by rw [← mem_lam_iff a₀ b₀ ha hd lam hlam hl, theta_val']; exact B.t0.2.1)
    (by rw [← mem_lam_iff a₀ b₀ ha hd lam hlam hl, ← e]; exact B.t0.2.2)
  have e2 : (B.ω₀ - lam * a₀) / 2 = B.ω₀ / 2 - lam * a₀ / 2 := by ring
  rw [e2]
  exact h

end Re

end Formalism.L2.Ker.KS
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapVal
section
noncomputable section
open NumberField IsDedekindDomain

namespace Formalism.L2.Ker.KS

section Val

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p])

theorem normO_le (a : 𝓞 K) : ‖f (a : K)‖ ≤ 1 := by
  obtain ⟨P, hm, hP⟩ := RingOfIntegers.isIntegral_coe a
  let v : Valuation ℂ_[p] NNReal := NormedField.valuation
  have hv := Valuation.integer.integers v
  have h2 : IsIntegral v.integer (f (a : K)) := by
    refine ⟨P.map (Int.castRingHom v.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e1 : (algebraMap v.integer ℂ_[p]).comp (Int.castRingHom v.integer) = f.comp (algebraMap ℤ K) :=
      RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (algebraMap ℤ K) (a : K) P = 0 := hP
    rw [this, map_zero]
  have := (hv.isIntegral_iff_v_le_one).mp h2
  exact_mod_cast this

variable (𝔭 : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (h : ℕ) (hgen : 𝔭.asIdeal ^ h = Ideal.span {ϖ}) (hlt : ‖f (ϖ : K)‖ < 1)

include hgen hlt in

theorem norm_lt_of_mem {t : 𝓞 K} (ht : t ∈ 𝔭.asIdeal) : ‖f (t : K)‖ < 1 := by
  have hmem : t ^ h ∈ Ideal.span {ϖ} := hgen ▸ Ideal.pow_mem_pow ht h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have key : ‖f (t : K)‖ ^ h < 1 := by
    have e : ‖f (t : K)‖ ^ h = ‖f (c : K)‖ * ‖f (ϖ : K)‖ := by
      rw [← norm_pow, ← map_pow, ← norm_mul, ← map_mul]
      congr 2
      exact_mod_cast hc.symm
    rw [e]
    calc ‖f (c : K)‖ * ‖f (ϖ : K)‖ ≤ 1 * ‖f (ϖ : K)‖ :=
          mul_le_mul_of_nonneg_right (normO_le f c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hlt
  have hh : h ≠ 0 := by
    rintro rfl
    simp at key
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hh).mp key

include hgen hlt in

theorem norm_eq_one_of_not_mem {a : 𝓞 K} (ha : a ∉ 𝔭.asIdeal) : ‖f (a : K)‖ = 1 := by
  obtain ⟨b, i, hi, hbi⟩ := 𝔭.isMaximal.exists_inv ha
  have hsmall : ‖f (i : K)‖ < 1 := norm_lt_of_mem f 𝔭 ϖ h hgen hlt hi
  have hba : ‖f (b : K)‖ * ‖f (a : K)‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    have e : ((b : K) * (a : K)) = 1 + -(i : K) := by
      have : ((b * a + i : 𝓞 K) : K) = 1 := by rw [hbi]; rfl
      push_cast at this
      linear_combination this
    rw [e, map_add, map_neg, map_one]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_neg] <;> linarith [hsmall]
  refine le_antisymm (normO_le f a) ?_
  calc (1 : ℝ) = ‖f (b : K)‖ * ‖f (a : K)‖ := hba.symm
    _ ≤ 1 * ‖f (a : K)‖ := mul_le_mul_of_nonneg_right (normO_le f b) (norm_nonneg _)
    _ = ‖f (a : K)‖ := one_mul _

include hgen hlt in

theorem norm_pow_int {a : 𝓞 K} (ha : a ≠ 0) :
    ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) ∧ ‖f (a : K)‖ ^ h = ‖f (ϖ : K)‖ ^ n := by
  classical
  obtain ⟨n, hva⟩ : ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) := ⟨_, 𝔭.intValuation_if_neg ha⟩
  refine ⟨n, hva, ?_⟩
  have hvah : 𝔭.intValuation (a ^ h) = WithZero.exp (-((n * h : ℕ) : ℤ)) := by
    rw [map_pow, hva, ← WithZero.exp_nsmul]
    congr 1
    push_cast
    ring
  have hmem : a ^ h ∈ Ideal.span {ϖ ^ n} := by
    have := (𝔭.intValuation_le_pow_iff_mem (a ^ h) (n * h)).mp hvah.le
    rwa [mul_comm, pow_mul, hgen, Ideal.span_singleton_pow] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcn : c ∉ 𝔭.asIdeal := by
    intro hcm
    have h1 : a ^ h ∈ 𝔭.asIdeal ^ (n * h + 1) := by
      rw [← hc, pow_succ', mul_comm n h, pow_mul, hgen, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_mul hcm (Ideal.mem_span_singleton_self _)
    have h2 := (𝔭.intValuation_le_pow_iff_mem _ _).mpr h1
    rw [hvah, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hc1 := norm_eq_one_of_not_mem f 𝔭 ϖ h hgen hlt hcn
  have e : (a : K) ^ h = (c : K) * (ϖ : K) ^ n := by exact_mod_cast hc.symm
  rw [← norm_pow, ← map_pow f, e, map_mul, norm_mul, hc1, one_mul, map_pow, norm_pow]

include hgen hlt in

theorem norm_pow_eq {x : K} (hx : x ≠ 0) :
    ‖f x‖ ^ h = ‖f (ϖ : K)‖ ^ (-WithZero.log (𝔭.valuation K x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨n, hva, hna⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt ha0
  obtain ⟨m, hvb, hnb⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt hb0
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hgen
    exact (pow_ne_zero h 𝔭.ne_bot) hgen
  have hfϖ : ‖f (ϖ : K)‖ ≠ 0 := by simpa using hϖ
  have hva' : 𝔭.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-(n : ℤ)) := by
    rw [← hva]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 a
  have hvb' : 𝔭.valuation K (algebraMap (𝓞 K) K b) = WithZero.exp (-(m : ℤ)) := by
    rw [← hvb]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 b
  rw [(𝔭.valuation K).map_div, hva', hvb', ← WithZero.exp_sub, WithZero.log_exp, map_div₀, norm_div,
    div_pow]
  change ‖f (a : K)‖ ^ h / ‖f (b : K)‖ ^ h = _
  rw [hna, hnb, show -(-(n : ℤ) - -(m : ℤ)) = (n : ℤ) - m by ring, zpow_sub₀ hfϖ, zpow_natCast,
    zpow_natCast]

end Val

end Formalism.L2.Ker.KS
end
end

