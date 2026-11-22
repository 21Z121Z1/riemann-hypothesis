import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfDisc
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.ModelThree

theorem norm_add_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_sub_le_max' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K} (hlt : ‖α‖ < ‖β‖)
    (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  have hb : 0 < ‖β‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : ‖α ^ 2 - α * β‖ < ‖β ^ 2‖ := by
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
    · rw [norm_pow, norm_pow]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    · rw [norm_mul, norm_pow, sq]; exact mul_lt_mul_of_pos_right hlt hb
  have h2 : ‖β ^ 2 + (α ^ 2 - α * β)‖ = ‖β ^ 2‖ := norm_add_of_lt h1
  have h3 : α ^ 2 - α * β + β ^ 2 = β ^ 2 + (α ^ 2 - α * β) := by ring
  rw [h3, h2, norm_pow] at hN
  have h4 : ‖β‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact ⟨(hlt.trans_le h4).le, h4⟩

theorem norm_le_one_of_disc {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K}
    (h : ‖α * β * (α - β)‖ = 1) (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  rcases lt_trichotomy ‖α‖ ‖β‖ with hlt | heq | hgt
  · exact norm_le_one_of_lt hlt hN
  · have hc : ‖α - β‖ ≤ ‖α‖ := by
      refine (norm_sub_le_max' _ _).trans ?_
      rw [heq, max_self]
    rcases hc.lt_or_eq with hc | hc
    · have h1 : ‖(α - β) ^ 2‖ < ‖α * β‖ := by
        rw [norm_pow, norm_mul, ← heq, ← sq]
        exact pow_lt_pow_left₀ hc (norm_nonneg _) (by norm_num)
      have h2 : ‖α * β + (α - β) ^ 2‖ = ‖α * β‖ := norm_add_of_lt h1
      have h3 : α ^ 2 - α * β + β ^ 2 = α * β + (α - β) ^ 2 := by ring
      rw [h3, h2, norm_mul, ← heq] at hN
      have h4 : ‖α‖ ≤ 1 := by
        by_contra hc'
        push Not at hc'
        nlinarith
      exact ⟨h4, heq ▸ h4⟩
    · rw [norm_mul, norm_mul, hc, ← heq] at h
      have h4 : ‖α‖ ^ 3 = 1 := by rw [← h]; ring
      have h5 : ‖α‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4
      exact ⟨h5.le, (heq ▸ h5).le⟩
  · have hN' : ‖β ^ 2 - β * α + α ^ 2‖ ≤ 1 := by
      have : β ^ 2 - β * α + α ^ 2 = α ^ 2 - α * β + β ^ 2 := by ring
      rw [this]; exact hN
    exact (norm_le_one_of_lt hgt hN').symm

theorem exists_roots {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (g2 g3 : K) :
    ∃ α β : K, 16 * (α ^ 2 - α * β + β ^ 2) = 12 * g2 ∧
      64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) = 216 * g3 := by
  let f : Polynomial K := Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C g2 * Polynomial.X - Polynomial.C g3
  have hdeg : f.degree ≠ 0 := by
    have h3 : f.natDegree = 3 := by
      simp only [f]
      compute_degree!
    intro h
    have h0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h.le
    omega
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root f hdeg
  have he' : 4 * e ^ 3 - g2 * e - g3 = 0 := by simpa [f, Polynomial.IsRoot] using he
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (g2 - 3 * e ^ 2) (n := 2) (by norm_num)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨(-3 * e + s) / 2, (-3 * e - s) / 2, ?_, ?_⟩
  · field_simp
    linear_combination (48 : K) * hs
  · have e1 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he'
    rw [e1]
    field_simp
    linear_combination (-1728 * e : K) * hs

def twoTorsionModel {K : Type} [Field K] (α β : K) : WeierstrassCurve K := ⟨0, -(α + β), 0, α * β, 0⟩

theorem c₄_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₄ = 16 * (α ^ 2 - α * β + β ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, twoTorsionModel]
  ring

theorem c₆_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₆ = 64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, twoTorsionModel]
  ring

theorem Δ_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).Δ = 16 * (α * β * (α - β)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, twoTorsionModel]
  ring

theorem norm_two : ‖(2 : ℂ_[3])‖ = 1 := by
  have e : (2 : ℂ_[3]) = algebraMap ℚ_[3] ℂ_[3] ((2 : ℕ) : ℚ_[3]) := by rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  norm_num

theorem exists_model (g2 g3 : ℂ_[3]) (hΔ : g2 ^ 3 - 27 * g3 ^ 2 = 1) (hj : ‖1728 * g2 ^ 3‖ ≤ 1) :
    ∃ W : WeierstrassCurve ℂ_[3], Formalism.L2.Th1.A.g₂ W = g2 ∧ Formalism.L2.Th1.A.g₃ W = g3 ∧ IntCurve W := by
  obtain ⟨α, β, h4, h6⟩ := exists_roots g2 g3
  have c4 : (twoTorsionModel α β).c₄ = 12 * g2 := by rw [c₄_model, h4]
  have c6 : (twoTorsionModel α β).c₆ = 216 * g3 := by rw [c₆_model, h6]
  have hD : (twoTorsionModel α β).Δ = 1 := by
    have hc := (twoTorsionModel α β).c_relation
    rw [c4, c6] at hc
    have : (1728 : ℂ_[3]) * (twoTorsionModel α β).Δ = 1728 * (g2 ^ 3 - 27 * g3 ^ 2) := by
      linear_combination hc
    exact (mul_left_cancel₀ (by norm_num) this).trans hΔ
  have n16 : ‖(16 : ℂ_[3])‖ = 1 := by
    have : (16 : ℂ_[3]) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, norm_two, one_pow]
  have hprod : ‖α * β * (α - β)‖ = 1 := by
    have h1 := congrArg norm hD
    rw [Δ_model, norm_mul, n16, one_mul, norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1 := by
    have e : (16 * (α ^ 2 - α * β + β ^ 2)) ^ 3 = 1728 * g2 ^ 3 := by rw [h4]; ring
    have h1 : ‖(16 * (α ^ 2 - α * β + β ^ 2)) ^ 3‖ ≤ 1 := by rw [e]; exact hj
    rw [norm_pow, norm_mul, n16, one_mul] at h1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨ha, hb⟩ := norm_le_one_of_disc hprod hN
  refine ⟨twoTorsionModel α β, ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂
    rw [c4]; field_simp
  · unfold Formalism.L2.Th1.A.g₃
    rw [c6]; field_simp
  · refine ⟨by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_⟩
    · simp only [twoTorsionModel, norm_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · simp only [twoTorsionModel, norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) hb
    · rw [hD, norm_one]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_iota_le_one (ι : ℂ ≃+* ℂ_[3]) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨f, hf, hr⟩ := hx
  refine norm_le_one_of_isIntegral ⟨f, hf, ?_⟩
  have h := congrArg (ι : ℂ →+* ℂ_[3]) hr
  rw [map_zero, Polynomial.hom_eval₂] at h
  have e : (@algebraMap ℤ ℂ_[3] _ _ (Ring.toIntAlgebra ℂ_[3])) = (ι : ℂ →+* ℂ_[3]).comp (algebraMap ℤ ℂ) :=
    Subsingleton.elim _ _
  rw [e]
  exact h

theorem goodModelThree : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[3], ∃ W : WeierstrassCurve ℂ_[3], Unif 3 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hL ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) L hL'
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd hok.1
      (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ D.host.d hok.1 hok.2.2.1))
  have hd8 := hok.2.2.1
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) :=
    hIn.jInt D.host.d L hok.2.2.2.prime.squarefree (by omega) hcm
  have hj' : Formalism.L2.Th1.CM.jInv L = 1728 * L.g₂ ^ 3 := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [hdisc, div_one]
  rw [hj'] at hj
  have hn := norm_iota_le_one ι hj
  have hΔ : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
    have := congrArg ι hdisc
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one] using this
  have hn' : ‖1728 * ι L.g₂ ^ 3‖ ≤ 1 := by
    simpa only [map_mul, map_pow, map_ofNat] using hn
  obtain ⟨W, h2, h3, hW⟩ := exists_model _ _ hΔ hn'
  exact ⟨W, ⟨h2, h3⟩, hW⟩

end GlobalTheory.ThLoc.ModelThree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormNatCastOfCoprime
section
open NumberField

namespace GlobalTheory.CoprimeUnitMultipliers

theorem exists_common_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : R → Prop) (h1 : U 1) (hm : ∀ a b, U a → U b → U (a * b))
    (M N : Submodule R V) (hM : M.FG) (h : ∀ x ∈ M, ∃ s, U s ∧ s • x ∈ N) :
    ∃ s, U s ∧ ∀ x ∈ M, s • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hM
  have key : ∀ T : Finset V, (∀ x ∈ T, ∃ s, U s ∧ s • x ∈ N) → ∃ s, U s ∧ ∀ x ∈ T, s • x ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1, by simp⟩
    | insert a T _ ih =>
      intro hT
      obtain ⟨s, hs, hsT⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨t, ht, hta⟩ := hT a (Finset.mem_insert_self a T)
      refine ⟨s * t, hm _ _ hs ht, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [mul_smul]; exact N.smul_mem _ hta
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (hsT x hx)
  obtain ⟨s, hs, hS⟩ := key S fun x hx => h x (Submodule.subset_span hx)
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

theorem norm_natCast_of_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) :
    ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

theorem general {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p]) {N N' : ℕ}
    (L L₁ : Submodule (𝓞 E) (Fin N → E)) (L' L₁' : Submodule (𝓞 E) (Fin N' → E))
    (P : Matrix (Fin N) (Fin N) E) (P' : Matrix (Fin N') (Fin N') E) (hfg : L₁.FG)
    (s : ℕ) (hs : Nat.Coprime s p) (hL : ∀ x ∈ L₁, (s : E) • x ∈ L)
    (s' : ℕ) (hs' : Nat.Coprime s' p) (hL' : ∀ x ∈ L', (s' : E) • x ∈ L₁')
    (hdet : P.det ≠ 0)
    (hP : ∀ x ∈ L, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, t • x = ∑ a, c a • P.transpose a)
    (hP' : ∀ a, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ t • P'.transpose a ∈ L') :
    ∃ σ σ' : 𝓞 E, ‖ρ (σ : E)‖ = 1 ∧ ‖ρ (σ' : E)‖ = 1 ∧
      (∀ a : Fin N, ∀ x ∈ L₁, ∃ o : 𝓞 E, (o : E) = (σ : E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧
      ∀ b : Fin N', (fun i : Fin N' => (σ' : E) * P' i b) ∈ L₁' := by
  have h1 : ‖ρ ((1 : 𝓞 E) : E)‖ = 1 := by simp
  have hm : ∀ a b : 𝓞 E, ‖ρ (a : E)‖ = 1 → ‖ρ (b : E)‖ = 1 → ‖ρ ((a * b : 𝓞 E) : E)‖ = 1 := by
    intro a b ha hb
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb ⊢
    rw [map_mul, map_mul, norm_mul, ha, hb, one_mul]
  have hn : ∀ n : ℕ, Nat.Coprime n p → ‖ρ (((n : 𝓞 E)) : E)‖ = 1 := by
    intro n hn
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
    exact norm_natCast_of_coprime hn
  have hsm : ∀ {k : ℕ} (n : ℕ) (x : Fin k → E), (n : 𝓞 E) • x = (n : E) • x := by
    intro k n x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨σ, hσ, hσL⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm L₁
    (Submodule.span (𝓞 E) (Set.range P.transpose)) hfg (by
      intro x hx
      obtain ⟨t, ht, c, hc⟩ := hP _ (hL x hx)
      refine ⟨t * s, hm _ _ ht (hn s hs), ?_⟩
      rw [mul_smul, hsm, hc]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨σ', hσ', hσL'⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm
    (Submodule.span (𝓞 E) (Set.range P'.transpose)) L₁'
    (Submodule.fg_span (Set.finite_range _)) (by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨t, ht, hta⟩ := hP' a
        refine ⟨s' * t, hm _ _ (hn s' hs') ht, ?_⟩
        rw [mul_smul, hsm]
        exact hL' _ hta
      | zero => exact ⟨1, h1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨t, ht, htx⟩ := hx
        obtain ⟨u, hu, huy⟩ := hy
        refine ⟨t * u, hm _ _ ht hu, ?_⟩
        rw [smul_add]
        refine L₁'.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L₁'.smul_mem _ htx
        · rw [mul_smul]; exact L₁'.smul_mem _ huy
      | smul a x _ hx =>
        obtain ⟨t, ht, htx⟩ := hx
        exact ⟨t, ht, by rw [smul_comm]; exact L₁'.smul_mem _ htx⟩)
  refine ⟨σ, σ', hσ, hσ', fun a x hx => ?_, fun b => ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hσL x hx)
    refine ⟨c a, ?_⟩
    have e1 : P.mulVec (fun i => (c i : E)) = (σ : E) • x := by
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def] at this
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [RingOfIntegers.coe_eq_algebraMap σ, ← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : (fun i => (c i : E)) = (σ : E) • P⁻¹.mulVec x := by
      rw [← Matrix.mulVec_smul, ← e1, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
    have := congrFun e2 a
    simpa [Matrix.mulVec, dotProduct] using this
  · have := hσL' _ (Submodule.subset_span ⟨b, rfl⟩)
    convert this using 1
    funext i
    simp only [Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def]

theorem exists_unit_multipliers : ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [inst : Fact (Nat.Prime p)] (ρ : (Formalism.BasicNotions.D7.host D).E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E)) (L' L₁' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)) (P : Matrix (Fin N) (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (P' : Matrix (Fin N') (Fin N') ((Formalism.BasicNotions.D7.host D).E)), Submodule.FG L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L' L₁' → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L P → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L' P' → ∃ (σ : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (σ' : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ' : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ (∀ (a : Fin N), ∀ x ∈ L₁, ∃ (o : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), (↑o : (Formalism.BasicNotions.D7.host D).E) = (↑σ : (Formalism.BasicNotions.D7.host D).E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧ ∀ (b : Fin N'), (fun (i : Fin N') ↦ (↑σ' : (Formalism.BasicNotions.D7.host D).E) * P' i b) ∈ L₁' := by
  intro D p inst ρ N N' L L₁ L' L₁' P P' hfg h h' hP hP'
  obtain ⟨s, hs, -, hL⟩ := h
  obtain ⟨s', hs', hL', -⟩ := h'
  exact general ρ L L₁ L' L₁' P P' hfg s hs hL s' hs' hL' hP.1 hP.2.2 hP'.2.1

end GlobalTheory.CoprimeUnitMultipliers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTwelveCubedEqOneOfFiveLePrime
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.GoodModelFive

theorem norm_nat_twelve (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) {N k : ℕ} (hN : N ∣ 12 ^ k) : ‖(N : ℂ_[p])‖ = 1 := by
  refine Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p fun h => ?_
  have hp : p.Prime := Fact.out
  have h12 : p ∣ 12 := hp.dvd_of_dvd_pow (h.trans hN)
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem norm_twelve_cubed_eq_one_of_five_le_prime (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) : ‖(1728 : ℂ_[p])‖ = 1 := by
  simpa using norm_nat_twelve p h5 (N := 1728) (k := 3) (by norm_num)

theorem norm_27 (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) : ‖(27 : ℂ_[p])‖ = 1 := by
  simpa using norm_nat_twelve p h5 (N := 27) (k := 3) (by norm_num)

theorem lamOf_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.lamOf D cc δ = (TaylorLogMetric.lamOf D cc 1).map (AddMonoidHom.mulLeft δ) := by
  unfold TaylorLogMetric.lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, AddMonoidHom.coe_mulLeft, one_mul]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem omega1_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

theorem intCurve_of_disc_one (hIn : GlobalTheory.ThLoc.Inputs) (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy d L) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p)
    (ι : ℂ ≃+* ℂ_[p]) : IntCurve (curveL p L ι) := by
  set a : ℂ := L.g₂ with ha
  set b : ℂ := L.g₃ with hb
  have hj : 1728 * a ^ 3 = Formalism.L2.Th1.CM.jInv L := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [← ha, ← hb, hΔ, div_one]
  have hJ : ‖ι (Formalism.L2.Th1.CM.jInv L)‖ ≤ 1 :=
    GlobalTheory.NormSum.KernelAt.norm_le_one_of_isIntegral (by convert map_isIntegral_int ι (hIn.jInt d L hsq hd4 hcm); exact Subsingleton.elim _ _)
  have ha3 : ‖ι a‖ ^ 3 ≤ 1 := by
    have h := congrArg ι hj
    rw [map_mul, map_pow, map_ofNat] at h
    rw [← h, norm_mul, norm_twelve_cubed_eq_one_of_five_le_prime p h5, one_mul, norm_pow] at hJ
    exact hJ
  have ha1 : ‖ι a‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 ha3
  have hb2 : ‖ι b‖ ^ 2 ≤ 1 := by
    have h : 27 * ι b ^ 2 = ι a ^ 3 - 1 := by
      have h := congrArg ι hΔ
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
      linear_combination -h
    have h' := congrArg norm h
    rw [norm_mul, norm_27 p h5, one_mul, norm_pow] at h'
    rw [h', sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by simp))
    rw [norm_pow]; exact ha3
  have hb1 : ‖ι b‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb2
  unfold curveL
  refine Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short p h5 _ _ ha1 hb1 ?_
  have h := congrArg ι hΔ
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
  rw [h, norm_one]

end GlobalTheory.GoodModelFive

namespace GlobalTheory.GoodModelFive

theorem goodModel_five : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι) := by
  intro hIn D cc δ _hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat p _ h5 ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hL
  obtain ⟨h4, _hodd, h8, hprime⟩ := hok
  have hmem : ∀ z, z ∈ TaylorLogMetric.lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [← hlat]; rfl

  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h1 : L.ω₁ ∈ TaylorLogMetric.lamOf D cc 0 := (hmem _).2 (L.mem_lattice.2 ⟨1, 0, by simp⟩)
    have hle : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
      unfold TaylorLogMetric.lamOf
      rw [AddSubgroup.closure_le]
      rintro w ⟨c, -, rfl⟩
      simp
    exact omega1_ne_zero L (by simpa using hle h1)

  set L' := Formalism.L2.Th1.F.scalePair L δ⁻¹ (inv_ne_zero hδ0) with hL'
  have hH := Formalism.L2.Th1.F.homogeneity L δ⁻¹ (inv_ne_zero hδ0)
  have hmem' : ∀ z, z ∈ TaylorLogMetric.lamOf D cc 1 ↔ z ∈ L'.lattice := fun z => by
    rw [hH.1, inv_inv, ← hmem, lamOf_eq_map D cc δ]
    exact (AddSubgroup.mem_map_iff_mem (f := AddMonoidHom.mulLeft δ) (mul_right_injective₀ hδ0)).symm
  have hdict := GlobalTheory.LatticeInvariants.invariants_dictionary L' (TaylorLogMetric.lamOf D cc 1) hmem'
  have e2 : TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc 1) = δ ^ 4 * L.g₂ := by
    rw [hdict.1, hH.2.2.2.2.2.2.2.2.2.1, inv_pow, inv_inv]
  have e3 : TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc 1) = δ ^ 6 * L.g₃ := by
    rw [hdict.2.1, hH.2.2.2.2.2.2.2.2.2.2, inv_pow, inv_inv]

  have hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h : δ ^ 12 = δ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      conv_lhs => rw [hδ]
      unfold TaylorLogMetric.discr
      rw [e2, e3]
      ring
    have h12 : δ ^ 12 ≠ 0 := pow_ne_zero _ hδ0
    exact (mul_left_cancel₀ h12 (h.symm.trans (mul_one _).symm))

  have hbodd : Odd b₀ := by
    rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | h
    · exfalso
      have e : (D.host.d : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by rw [hk] at h4; linear_combination -h4
      generalize (a₀ : ℤ) * c₀ - k * k = m at e
      omega
    · exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam
      (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd h4 hbodd)
  exact intCurve_of_disc_one hIn D.host.d L hprime.prime.squarefree (by omega) hcm hΔ p h5 ι

end GlobalTheory.GoodModelFive
end
end

