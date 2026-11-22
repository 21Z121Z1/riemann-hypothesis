import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIntegralTraceAlmostAll
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem eventually_valued_eq_one {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  refine Filter.eventually_cofinite.2 (((HeightOneSpectrum.Support.finite (𝓞 F) x).union
    (HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹)).subset fun v hv => ?_)
  by_contra hc
  simp only [HeightOneSpectrum.Support, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, map_inv₀] at hc
  have h0 : 0 < v.valuation F x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have h1 : v.valuation F x = 1 := le_antisymm hc.1 ((inv_le_one₀ h0).1 hc.2)
  exact hv ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans h1)

theorem norm_one_coords {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {d β x y : K} (hd : d ≠ 0) (hβ : β ≠ 0)
    (hxy : β = x ^ 2 - d * y ^ 2) (t : K) :
    let m := ((t * 2⁻¹) ^ 2 - 1) * d⁻¹
    let r := (1 + m) * 2⁻¹
    let c := (m - 1) * 2⁻¹
    (t * 2⁻¹) ^ 2 - d * r ^ 2 - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2 = 1 := by
  intro m r c
  have hm : d * m = (t * 2⁻¹) ^ 2 - 1 := by simp only [m]; field_simp
  have e : - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2 = c ^ 2 * d := by
    have : - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2
        = c ^ 2 * d * (x ^ 2 - d * y ^ 2) * β⁻¹ := by field_simp; ring
    rw [this, ← hxy]; field_simp
  have e2 : d * r ^ 2 - c ^ 2 * d = d * m := by
    simp only [r, c]; field_simp; ring
  linear_combination e - e2 - hm

theorem exists_integral_coords {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {D B t : v.adicCompletion F} (h2 : Valued.v (2 : v.adicCompletion F) = 1) (hD : Valued.v D = 1)
    (hB : Valued.v B = 1) (ht : t ∈ v.adicCompletionIntegers F) :
    ∃ a₀ ∈ v.adicCompletionIntegers F, ∃ a₁ ∈ v.adicCompletionIntegers F,
      ∃ a₂ ∈ v.adicCompletionIntegers F, ∃ a₃ ∈ v.adicCompletionIntegers F,
        2 * a₀ = t ∧ a₀ ^ 2 - D * a₁ ^ 2 - B * a₂ ^ 2 + D * B * a₃ ^ 2 = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v D B h2 hD hB
  have ne0 : ∀ {z : v.adicCompletion F}, Valued.v z = 1 → z ≠ 0 := fun hz h0 => by
    rw [h0, map_zero] at hz; exact zero_ne_one hz
  have inv_mem : ∀ {z : v.adicCompletion F}, Valued.v z = 1 → z⁻¹ ∈ v.adicCompletionIntegers F :=
    fun hz => by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hz, inv_one]
  have hDm : D ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hD]
  have hi2 := inv_mem h2
  have hk := norm_one_coords (ne0 h2) (ne0 hD) (ne0 hB) hxy t
  have h0 : t * 2⁻¹ ∈ v.adicCompletionIntegers F := mul_mem ht hi2
  have hm : ((t * 2⁻¹) ^ 2 - 1) * D⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem (sub_mem (pow_mem h0 2) (one_mem _)) (inv_mem hD)
  have hc := mul_mem (sub_mem hm (one_mem _)) hi2
  exact ⟨_, h0, _, mul_mem (add_mem (one_mem _) hm) hi2, _,
    neg_mem (mul_mem (mul_mem (mul_mem hc hy) hDm) (inv_mem hB)), _,
    mul_mem (mul_mem hc hx) (inv_mem hB), by rw [mul_comm t, ← mul_assoc,
      mul_inv_cancel₀ (ne0 h2), one_mul], hk⟩

theorem exists_integral_norm_one_trace :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 →
      ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)), ∀ t ∈ Ov v,
        ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
  intro F _ _ d β hd hβ
  filter_upwards [eventually_valued_eq_one hd, eventually_valued_eq_one hβ,
    eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hdv hβv h2v t ht
  rw [map_ofNat] at h2v
  obtain ⟨a₀, h₀, a₁, h₁, a₂, h₂, a₃, h₃, htr, hn⟩ := exists_integral_coords v h2v hdv hβv ht
  exact ⟨⟨a₀, a₁, a₂, a₃⟩, hn, htr, h₀, h₁, h₂, h₃⟩

end GlobalTheory.CompanionTheory.PlaneSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjugate
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.ConjQ

section Coord

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d β : F}

theorem isUnit_of_qn_ne_zero {y : Q d β K} (h : qn y ≠ 0) : IsUnit y := by
  refine isUnit_iff_exists.2 ⟨(qn y)⁻¹ • star y, ?_, ?_⟩
  · rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]
  · rw [smul_mul_assoc, star_mul_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]

def pureAdd (x b : Q d β K) : Q d β K := ⟨0, x.imI + b.imI, x.imJ + b.imJ, x.imK + b.imK⟩

def pureSub (x b : Q d β K) : Q d β K := ⟨0, x.imI - b.imI, x.imJ - b.imJ, x.imK - b.imK⟩

theorem pureAdd_mul (x b : Q d β K) (hre : x.re = b.re) (hq : qn x = qn b) :
    pureAdd x b * x = b * pureAdd x b := by
  unfold qn at hq
  rw [hre] at hq
  ext <;> simp only [pureAdd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, hre]
  · linear_combination -hq
  · ring
  · ring
  · ring

theorem pureSub_mul (x b : Q d β K) (hre : x.re = b.re) (hq : qn x = qn b) :
    pureSub x b * x = star b * pureSub x b := by
  unfold qn at hq
  rw [hre] at hq
  ext <;> simp only [pureSub, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, hre]
  · linear_combination -hq
  · ring
  · ring
  · ring

theorem qn_add_sub (x b : Q d β K) :
    qn (pureAdd x b) + qn (pureSub x b) = 2 * (qn x - x.re ^ 2) + 2 * (qn b - b.re ^ 2) := by
  simp only [qn, pureAdd, pureSub]
  ring

theorem mul_star_of_orth (z b : Q d β K) (hz : z.re = 0)
    (ho : algebraMap F K d * z.imI * b.imI + algebraMap F K β * z.imJ * b.imJ -
      algebraMap F K d * algebraMap F K β * z.imK * b.imK = 0) :
    z * star b = b * z := by
  ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, hz]
  · linear_combination -2 * ho
  · ring
  · ring
  · ring

theorem exists_orth (h2 : (2 : K) ≠ 0) (hd : algebraMap F K d ≠ 0) (hβ : algebraMap F K β ≠ 0)
    (b : Q d β K) (hb : qn b - b.re ^ 2 ≠ 0) :
    ∃ z : Q d β K, z.re = 0 ∧ qn z ≠ 0 ∧
      algebraMap F K d * z.imI * b.imI + algebraMap F K β * z.imJ * b.imJ -
        algebraMap F K d * algebraMap F K β * z.imK * b.imK = 0 := by
  set a := algebraMap F K d with ha
  set c := algebraMap F K β with hc
  by_cases hA : a * b.imI ^ 2 + c * b.imJ ^ 2 = 0
  · by_cases hB : b.imI ^ 2 - c * b.imK ^ 2 = 0
    · by_cases hC : b.imJ ^ 2 - a * b.imK ^ 2 = 0
      · exfalso
        have hk : 2 * (a * c * b.imK ^ 2) = 0 := by
          linear_combination hA - a * hB - c * hC
        have hk2 : a * c * b.imK ^ 2 = 0 := (mul_eq_zero.1 hk).resolve_left h2
        apply hb
        simp only [qn, ← ha, ← hc]
        linear_combination hk2 - hA
      · refine ⟨⟨0, 0, a * b.imK, b.imJ⟩, rfl, ?_, ?_⟩
        · simp only [qn, ← ha, ← hc]
          intro h
          have : a * c * (b.imJ ^ 2 - a * b.imK ^ 2) = 0 := by linear_combination h
          exact hC ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
        · simp only [← ha, ← hc]; ring
    · refine ⟨⟨0, c * b.imK, 0, b.imI⟩, rfl, ?_, ?_⟩
      · simp only [qn, ← ha, ← hc]
        intro h
        have : a * c * (b.imI ^ 2 - c * b.imK ^ 2) = 0 := by linear_combination h
        exact hB ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
      · simp only [← ha, ← hc]; ring
  · refine ⟨⟨0, c * b.imJ, -(a * b.imI), 0⟩, rfl, ?_, ?_⟩
    · simp only [qn, ← ha, ← hc]
      intro h
      have : a * c * (a * b.imI ^ 2 + c * b.imJ ^ 2) = 0 := by linear_combination -h
      exact hA ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
    · simp only [← ha, ← hc]; ring

end Coord

theorem conj_of_same_re : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 →
    ∀ x b : Q d β K, qn x = 1 → qn b = 1 → x.re = b.re → x.re ^ 2 ≠ 1 →
      ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
  intro F K _ _ _ d β h2 hd hβ x b hx hb hre hp
  have hd' : algebraMap F K d ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).2 hd
  have hβ' : algebraMap F K β ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).2 hβ
  have hn : (1 : K) - b.re ^ 2 ≠ 0 := by
    rw [← hre]
    exact fun h => hp (by linear_combination -h)

  have key : ∀ y : (Q d β K)ˣ, (y : Q d β K) * x = b * y →
      ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
    intro y hy
    exact ⟨y, by rw [hy, mul_assoc, Units.mul_inv, mul_one]⟩
  have hq : qn x = qn b := hx.trans hb.symm
  by_cases h₁ : qn (pureAdd x b) = 0
  · have h₂ : qn (pureSub x b) ≠ 0 := by
      intro h₂
      have hs := qn_add_sub x b
      rw [h₁, h₂, hx, hb, hre] at hs
      have : (2 * 2 : K) * (1 - b.re ^ 2) = 0 := by linear_combination -hs
      exact hn ((mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 h2))
    obtain ⟨z, hz, hzn, ho⟩ := exists_orth h2 hd' hβ' b (by rwa [hb])
    obtain ⟨e, he⟩ := isUnit_of_qn_ne_zero h₂
    obtain ⟨w, hw⟩ := isUnit_of_qn_ne_zero hzn
    refine key (w * e) ?_
    rw [Units.val_mul, hw, he, mul_assoc, pureSub_mul x b hre hq, ← mul_assoc,
      mul_star_of_orth z b hz ho, mul_assoc]
  · obtain ⟨y, hy⟩ := isUnit_of_qn_ne_zero h₁
    refine key y ?_
    rw [hy, pureAdd_mul x b hre hq]

end GlobalTheory.CompanionTheory.PlaneSA.ConjQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDense
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.RegDense

open scoped Polynomial

noncomputable def cay {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F) (p q r n e : K) : Q d β K :=
  ⟨(1 + e ^ 2 * n) / (1 - e ^ 2 * n), 2 * e * p / (1 - e ^ 2 * n), 2 * e * q / (1 - e ^ 2 * n),
    2 * e * r / (1 - e ^ 2 * n)⟩

theorem qn_cay {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F) (p q r n e : K)
    (hn : n = algebraMap F K d * p ^ 2 + algebraMap F K β * q ^ 2
      - algebraMap F K d * algebraMap F K β * r ^ 2)
    (h : 1 - e ^ 2 * n ≠ 0) : qn (cay d β p q r n e) = 1 := by
  simp only [qn, cay]
  field_simp
  rw [hn]
  ring

theorem exists_regular {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F)
    (h2 : (2 : K) ≠ 0) (hd : d ≠ 0) (hb : β ≠ 0) :
    ∃ b : Q d β K, qn b = 1 ∧ b.re ^ 2 ≠ 1 := by
  have hD : algebraMap F K d ≠ 0 := by simpa using hd
  have hB : algebraMap F K β ≠ 0 := by simpa using hb
  have hex : ∃ p q r n : K, n = algebraMap F K d * p ^ 2 + algebraMap F K β * q ^ 2
      - algebraMap F K d * algebraMap F K β * r ^ 2 ∧ n ≠ 0 ∧ n ≠ 1 := by
    by_cases h1 : algebraMap F K d = 1
    · by_cases h3 : algebraMap F K β = 1
      · refine ⟨0, 0, 1, -1, by rw [h1, h3]; ring, by simp, ?_⟩
        intro h
        apply h2
        linear_combination -h
      · exact ⟨0, 1, 0, _, rfl, by simpa using hB, by simpa using h3⟩
    · exact ⟨1, 0, 0, _, rfl, by simpa using hD, by simpa using h1⟩
  obtain ⟨p, q, r, n, hn, hn0, hn1⟩ := hex
  have hW : 1 - (1 : K) ^ 2 * n ≠ 0 := by
    intro h
    apply hn1
    linear_combination -h
  refine ⟨cay d β p q r n 1, qn_cay d β p q r n 1 hn hW, ?_⟩
  intro h
  have hW' : 1 - n ≠ 0 := by simpa using hW
  simp only [cay, one_pow, one_mul] at h
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hW')] at h
  have h4 : (2 : K) * 2 * n = 0 := by linear_combination h
  exact (mul_ne_zero (mul_ne_zero h2 h2) hn0) h4

theorem eventually_eval_ne {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    (hV : ∃ V ∈ 𝓝 (0 : K), (1 : K) ∉ V) (P : K[X]) (hP : P ≠ 0) :
    ∀ᶠ e in 𝓝[≠] (0 : K), P.eval e ≠ 0 := by
  obtain ⟨V, hV, h1⟩ := hV
  have key : ∀ r : K, ∀ᶠ e in 𝓝[≠] (0 : K), e ≠ r := by
    intro r
    by_cases hr : r = 0
    · subst hr
      exact eventually_mem_nhdsWithin
    · have hc : ContinuousAt (fun x : K => x * r⁻¹) 0 := by fun_prop
      have hm : (fun x : K => x * r⁻¹) ⁻¹' V ∈ 𝓝 (0 : K) := hc (by simpa using hV)
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hm] with e he hne
      subst hne
      apply h1
      simpa [hr] using he
  classical
  have hall := (Filter.eventually_all_finset P.roots.toFinset).2 (fun r _ => key r)
  filter_upwards [hall] with e he h0
  exact he e (by simp [hP, Polynomial.IsRoot, h0]) rfl

theorem continuousAt_cay {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (d β : F) (p q r n : K) :
    ContinuousAt (fun e : K => cay d β p q r n e) 0 := by
  have hW : (1 : K) - 0 ^ 2 * n ≠ 0 := by simp
  have hden : ContinuousAt (fun e : K => 1 - e ^ 2 * n) 0 := by fun_prop
  have h1 : ContinuousAt (fun e : K => (1 + e ^ 2 * n) / (1 - e ^ 2 * n)) 0 :=
    ContinuousAt.div (by fun_prop) hden hW
  have h2 : ∀ t : K, ContinuousAt (fun e : K => 2 * e * t / (1 - e ^ 2 * n)) 0 := fun t =>
    ContinuousAt.div (by fun_prop) hden hW
  refine (qHomeo (d := d) (β := β) (R := K)).isInducing.continuousAt_iff.2 ?_
  exact h1.prodMk ((h2 p).prodMk ((h2 q).prodMk (h2 r)))

theorem cay_zero {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F) (p q r n : K) :
    cay d β p q r n 0 = 1 := by
  ext <;> simp [cay]

noncomputable def quartic {K : Type} [Field K] (A B D : K) : K[X] :=
  Polynomial.C (A ^ 2 - 1) + Polynomial.C (4 * A * B) * Polynomial.X
    + Polynomial.C (4 * B ^ 2 + 2 * A ^ 2 * D + 2 * D) * Polynomial.X ^ 2
    + Polynomial.C (4 * A * B * D) * Polynomial.X ^ 3
    + Polynomial.C (D ^ 2 * (A ^ 2 - 1)) * Polynomial.X ^ 4

theorem quartic_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (A B D : K) (hD : D ≠ 0) :
    quartic A B D ≠ 0 := by
  intro h
  have gen : ∀ c0 c1 c2 c3 c4 : K,
      (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2
        + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 0 = c0 ∧
      (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2
        + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 1 = c1 ∧
      (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2
        + Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 : K[X]).coeff 2 = c2 := by
    intro c0 c1 c2 c3 c4
    simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  obtain ⟨g0, g1, g2⟩ := gen (A ^ 2 - 1) (4 * A * B) (4 * B ^ 2 + 2 * A ^ 2 * D + 2 * D)
    (4 * A * B * D) (D ^ 2 * (A ^ 2 - 1))
  unfold quartic at h
  rw [h, Polynomial.coeff_zero] at g0 g1 g2
  have c0 := g0.symm
  have c1 := g1.symm
  have c2 := g2.symm
  have hB : (2 : K) * 2 * B = 0 := by
    linear_combination A * c1 - 4 * B * c0
  have hB0 : B = 0 := by
    rcases mul_eq_zero.1 hB with h | h
    · exact absurd h (mul_ne_zero h2 h2)
    · exact h
  have h4 : (2 : K) * 2 * D = 0 := by
    rw [hB0] at c2
    linear_combination c2 - 2 * D * c0
  exact (mul_ne_zero (mul_ne_zero h2 h2) hD) h4

theorem eval_quartic {K : Type} [Field K] (A B D e : K) :
    (quartic A B D).eval e = (A * (1 + e ^ 2 * D) + 2 * e * B) ^ 2 - (1 - e ^ 2 * D) ^ 2 := by
  simp only [quartic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

theorem regular_dense : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F),
  (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 → (𝓝[≠] (0 : K)).NeBot →
  ∀ a : Q d β K, qn a = 1 → ∀ U ∈ 𝓝 a, ∃ b ∈ U, qn b = 1 ∧ b.re ^ 2 ≠ 1 := by
  intro F K _ _ _ _ _ d β h2 hd hb hne a ha U hU
  by_cases hV : ∃ V ∈ 𝓝 (0 : K), (1 : K) ∉ V
  · have hD : algebraMap F K d ≠ 0 := by simpa using hd
    have e1 := eventually_eval_ne hV _
      (quartic_ne_zero h2 a.re (algebraMap F K d * a.imI) (algebraMap F K d) hD)
    have hP2 : (1 - Polynomial.X ^ 2 * Polynomial.C (algebraMap F K d) : K[X]) ≠ 0 := by
      intro h
      have := congrArg (fun P : K[X] => P.eval 0) h
      simp at this
    have e2 := eventually_eval_ne hV _ hP2
    have e3 : ∀ᶠ e in 𝓝[≠] (0 : K),
        a * cay d β (1 : K) 0 0 (algebraMap F K d) e ∈ U := by
      have hc : ContinuousAt (fun e : K => a * cay d β (1 : K) 0 0 (algebraMap F K d) e) 0 :=
        continuousAt_const.mul (continuousAt_cay d β _ _ _ _)
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds (hc ?_)
      simpa [cay_zero] using hU
    obtain ⟨e, h1, hW, h3⟩ := (e1.and (e2.and e3)).exists
    have hW' : 1 - e ^ 2 * algebraMap F K d ≠ 0 := by
      simpa only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] using hW
    refine ⟨_, h3, ?_, ?_⟩
    · rw [qn_mul, ha, one_mul]
      exact qn_cay d β _ _ _ _ _ (by ring) hW'
    · intro hre
      apply h1
      rw [eval_quartic]
      have hr : (a * cay d β (1 : K) 0 0 (algebraMap F K d) e).re =
          (a.re * (1 + e ^ 2 * algebraMap F K d) + 2 * e * (algebraMap F K d * a.imI)) /
            (1 - e ^ 2 * algebraMap F K d) := by
        simp only [QuaternionAlgebra.re_mul, cay]
        field_simp
        ring
      rw [hr, div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hW')] at hre
      rw [hre, sub_self]
  · push_neg at hV
    obtain ⟨b, hb1, hb2⟩ := exists_regular (K := K) d β h2 hd hb
    refine ⟨b, ?_, hb1, hb2⟩
    let g : K → Q d β K := fun t =>
      ⟨a.re + t * (b.re - a.re), a.imI + t * (b.imI - a.imI), a.imJ + t * (b.imJ - a.imJ),
        a.imK + t * (b.imK - a.imK)⟩
    have hg : Continuous g :=
      continuous_q_iff.2 ⟨by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop,
        by dsimp only [g]; fun_prop, by dsimp only [g]; fun_prop⟩
    have hg0 : g 0 = a := by ext <;> simp [g]
    have hg1 : g 1 = b := by ext <;> simp [g]
    have hm : g ⁻¹' U ∈ 𝓝 (0 : K) := hg.continuousAt (by rw [hg0]; exact hU)
    have := hV _ hm
    rwa [Set.mem_preimage, hg1] at this

end GlobalTheory.CompanionTheory.PlaneSA.RegDense
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionTraceOpen
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem re_normOne_open_of_sq_ne_one {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (d β : F)
    (a : Q d β K) (ha : qn a = 1) (hp : a.re ^ 2 ≠ 1)
    (hsq : ∀ V ∈ 𝓝 (1 : K), ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x) :
    ∀ U ∈ 𝓝 a, ∀ᶠ r in 𝓝 a.re, ∃ b ∈ U, qn b = 1 ∧ b.re = r := by
  intro U hU
  have hc : 1 - a.re ^ 2 ≠ 0 := fun h => hp (sub_eq_zero.1 h).symm
  let g : K × K → Q d β K := fun z => ⟨z.1, z.2 * a.imI, z.2 * a.imJ, z.2 * a.imK⟩
  have hg : Continuous g := by
    rw [continuous_q_iff]
    refine ⟨continuous_fst, ?_, ?_, ?_⟩ <;> exact continuous_snd.mul continuous_const
  have hg1 : g (a.re, 1) = a := by
    ext <;> simp [g]
  have hpre : g ⁻¹' U ∈ 𝓝 ((a.re, 1) : K × K) :=
    hg.continuousAt.preimage_mem_nhds (by rwa [hg1])
  obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.1 hpre
  have hx : Filter.Tendsto (fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2)) (𝓝 a.re) (𝓝 1) := by
    have hcont : Continuous fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2) := by
      simp only [div_eq_mul_inv]
      exact (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
    have := hcont.tendsto a.re
    simpa [div_self hc] using this
  filter_upwards [hA, hx.eventually (hsq V hV)] with r hrA hr
  obtain ⟨μ, hμV, hμ⟩ := hr
  refine ⟨g (r, μ), hAV (Set.mk_mem_prod hrA hμV), ?_, rfl⟩
  have hy : algebraMap F K d * a.imI ^ 2 + algebraMap F K β * a.imJ ^ 2
      - algebraMap F K d * algebraMap F K β * a.imK ^ 2 = a.re ^ 2 - 1 := by
    have : qn a = 1 := ha
    simp only [qn] at this
    linear_combination -this
  have hμ' : μ ^ 2 * (1 - a.re ^ 2) = 1 - r ^ 2 := by
    rw [hμ]; field_simp
  simp only [qn, g]
  linear_combination -(μ ^ 2) * hy + hμ'

end GlobalTheory.CompanionTheory.PlaneSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenPeriodFiniteExtensionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sen_period_finite_extension : ∀ {l : ℕ} [Fact l.Prime],
    (∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x) →
    ∀ (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
      ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite | exact GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite | (intros; apply GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriodStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sen_unramified_character_period : ∀ {l : ℕ} [Fact l.Prime], ∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | exact GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExistsStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_near_power_exists : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) → ∀ (ϖ : Formalism.Per6.BdRp l),
    thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 → ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.TopNil.main | exact GlobalTheory.CompanionTheory.LTPer.TopNil.main | (intros; apply GlobalTheory.CompanionTheory.LTPer.TopNil.main <;> assumption)
end
end

