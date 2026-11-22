import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowSlashTPow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.NrmT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

theorem eOm_add' (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply ε.injective
  rw [map_mul, KTExp.map_eOm, KTExp.map_eOm, KTExp.map_eOm, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem eOm_zero' : eOm ε 0 = 1 := (KTExp.eOm_eq_one_iff ε 0).2 rfl

theorem eOm_nat_mul (x : ℚ) (b : ℕ) : eOm ε (x * b) = eOm ε x ^ b := by
  induction b with
  | zero => simp only [Nat.cast_zero, mul_zero, pow_zero]; exact eOm_zero'
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add', ih, pow_succ]

theorem eOm_pow_den (x : ℚ) : eOm ε x ^ x.den = 1 := by
  rw [← eOm_nat_mul, (KTExp.eOm_eq_one_iff ε _).2]
  rw [Rat.mul_den_eq_num]; simp

theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {z : Ω} {d : ℕ} (hd : 0 < d) (h : z ^ d = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with hz | hz
  · exact hz
  · have h1 : z * z ^ (d - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hd, h]
    rw [eq_inv_of_mul_eq_one_left h1, ← inv_pow]
    exact pow_mem hz _

theorem eOm_mem (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A :=
  mem_of_pow_eq_one A x.den_pos (eOm_pow_den x)

theorem eOm_ne_zero (x : ℚ) : eOm ε x ≠ 0 := by
  intro h
  have := eOm_pow_den (ε := ε) x
  rw [h, zero_pow x.den_nz] at this
  exact zero_ne_one this

theorem eOm_inv_mem (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  have h : eOm ε (-x) * eOm ε x = 1 := by rw [← eOm_add', neg_add_cancel, eOm_zero']
  rw [← eq_inv_of_mul_eq_one_left h]
  exact eOm_mem A _

def trT (ε : Ω →+* ℂ) (b : ℕ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := eOm ε (r * b) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem trT_coeff (b : ℕ) (φ : HahnSeries ℚ Ω) (r : ℚ) : (trT ε b φ).coeff r = eOm ε (r * b) * φ.coeff r := rfl

theorem trT_support (b : ℕ) (φ : HahnSeries ℚ Ω) : (trT ε b φ).support ⊆ φ.support :=
  fun r hr h => hr (by rw [trT_coeff, h, mul_zero])

theorem coeff_mul_sup {x y : HahnSeries ℚ Ω} {s t : Set ℚ} (hs : s.IsPWO) (ht : t.IsPWO) (hxs : x.support ⊆ s)
    (hyt : y.support ⊆ t) (a : ℚ) :
    (x * y).coeff a = ∑ ij ∈ Finset.addAntidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_addAntidiagonal] at hij
    exact Finset.mem_addAntidiagonal.2 ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  · intro ij hij hn
    by_cases h1 : x.coeff ij.1 = 0
    · rw [h1, zero_mul]
    · by_cases h2 : y.coeff ij.2 = 0
      · rw [h2, mul_zero]
      · exact absurd (Finset.mem_addAntidiagonal.2 ⟨h1, h2, (Finset.mem_addAntidiagonal.1 hij).2.2⟩) hn

theorem trT_mul (b : ℕ) (x y : HahnSeries ℚ Ω) : trT ε b (x * y) = trT ε b x * trT ε b y := by
  ext a
  rw [coeff_mul_sup x.isPWO_support y.isPWO_support (trT_support b x) (trT_support b y)]
  simp only [trT_coeff]
  rw [HahnSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mem_addAntidiagonal] at hij
  rw [← hij.2.2, add_mul, eOm_add']
  ring

theorem trT_sub (b : ℕ) (x y : HahnSeries ℚ Ω) : trT ε b (x - y) = trT ε b x - trT ε b y := by
  ext r
  simp only [trT_coeff, HahnSeries.coeff_sub]
  ring

theorem theta_trT (s : ℚ) (b : ℕ) (φ : HahnSeries ℚ Ω) : theta s (trT ε b φ) = trT ε b (theta s φ) := by
  ext r
  show algebraMap ℚ Ω (s * r) * (eOm ε (r * b) * φ.coeff r) = eOm ε (r * b) * (algebraMap ℚ Ω (s * r) * φ.coeff r)
  ring

theorem modularTowerExp_slAction_T_pow (X : Tower Ω ε) (b : ℕ) (f : X.K) :
    X.exp (X.sl (ofSL (ModularGroup.T ^ b)) f) = trT ε b (X.exp f) := by
  obtain ⟨h00, h01, h10, h11⟩ := KTExp.ent_T_pow b
  ext r
  have := X.exp_upper (ofSL (ModularGroup.T ^ b)) h10 f r
  rw [h00, h01, h11, mul_one, div_one, div_one] at this
  rw [trT_coeff]; exact this

theorem cgA_mul (A : ValuationSubring Ω) (l n : ℕ) {c x y : Ω} (hc : c ∈ A) (h : CgA A l n x y) :
    CgA A l n (c * x) (c * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨c * z, mul_mem hc hz, by rw [← mul_sub, e]; ring⟩

theorem prim_trT (A : ValuationSubring Ω) (b : ℕ) {φ : HahnSeries ℚ Ω} (h : Prim A φ) : Prim A (trT ε b φ) := by
  obtain ⟨hi, r, hr0, hru⟩ := h
  refine ⟨fun r => mul_mem (eOm_mem A _) (hi r), r, ?_, ?_⟩
  · rw [trT_coeff]; exact mul_ne_zero (eOm_ne_zero _) hr0
  · rw [trT_coeff, mul_inv]; exact mul_mem (eOm_inv_mem A _) hru

theorem isLogDerivQExpansionModPrimePow_slash_T_pow (X : Tower Ω ε) (A : ValuationSubring Ω) (l m : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) (b : ℕ)
    (h : IsDl X A l m s f φ) : IsDl X A l m s (X.sl (ofSL (ModularGroup.T ^ b)) f) (trT ε b φ) := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨fun r => mul_mem (eOm_mem A _) (hφ r), X.sl (ofSL (ModularGroup.T ^ b)) a,
    X.sl (ofSL (ModularGroup.T ^ b)) c, κ, hκ, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul (X.sl (ofSL (ModularGroup.T ^ b))) f c, he, map_mul, AlgEquiv.commutes]
  · rw [modularTowerExp_slAction_T_pow]; exact prim_trT A b ha
  · rw [modularTowerExp_slAction_T_pow]; exact prim_trT A b hc
  · intro r
    rw [modularTowerExp_slAction_T_pow, modularTowerExp_slAction_T_pow]
    simp only [theta_trT, ← trT_mul, ← trT_sub]
    simp only [trT_coeff]
    exact cgA_mul A l m (eOm_mem A _) (hcg r)

theorem sum_trT (L : ℕ) (φ : HahnSeries ℚ Ω) (hφ : ∀ r, φ.coeff r ≠ 0 → (r * L).den = 1) (φ' : HahnSeries ℚ Ω)
    (h' : ∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) :
    ∑ b ∈ Finset.range L, trT ε b φ = HahnSeries.C (L : Ω) * φ' := by
  ext r
  rw [HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, h', smul_eq_mul]
  simp only [trT_coeff, eOm_nat_mul]
  rw [← Finset.sum_mul]
  by_cases h0 : φ.coeff r = 0
  · simp [h0]
  · split_ifs with hr
    · have : eOm ε r = 1 := (KTExp.eOm_eq_one_iff ε r).2 hr
      simp [this]
    · have hz1 : eOm ε r ≠ 1 := fun e => hr ((KTExp.eOm_eq_one_iff ε r).1 e)
      have hzL : eOm ε r ^ L = 1 := by rw [← eOm_nat_mul]; exact (KTExp.eOm_eq_one_iff ε _).2 (hφ r h0)
      have hs : ∑ i ∈ Finset.range L, eOm ε r ^ i = 0 := by
        have := geom_sum_mul (eOm ε r) L
        rw [hzL, sub_self] at this
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz1)
      rw [hs, zero_mul, mul_zero]

theorem theta_eq_C_mul (s : ℚ) (x : HahnSeries ℚ Ω) : theta s x = HahnSeries.C (algebraMap ℚ Ω s) * theta 1 x := by
  ext r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  show algebraMap ℚ Ω (s * r) * x.coeff r = algebraMap ℚ Ω s * (algebraMap ℚ Ω (1 * r) * x.coeff r)
  rw [one_mul, map_mul]; ring

theorem coeff_mul_mem (A : ValuationSubring Ω) (t : Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, ∃ z ∈ A, x.coeff r = t * z)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : ∃ z ∈ A, (x * y).coeff r = t * z := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_induction _ (fun u => ∃ z ∈ A, u = t * z)
  · rintro u v ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', add_mem hz hz', by ring⟩
  · exact ⟨0, zero_mem A, by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hx ij.1
    exact ⟨z * y.coeff ij.2, mul_mem hz (hy ij.2), by rw [e]; ring⟩

theorem int_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A)
    (r : ℚ) : (x * y).coeff r ∈ A := by
  obtain ⟨z, hz, e⟩ := coeff_mul_mem A 1 (fun r => ⟨x.coeff r, hx r, (one_mul _).symm⟩) hy r
  rw [e, one_mul]; exact hz

theorem isDl_congr (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (F : X.K) (φ ψ : HahnSeries ℚ Ω)
    (h : IsDl X A l n s F φ) (hψ : ∀ r, ψ.coeff r ∈ A) (hc : ∀ r, CgA A l n (ψ.coeff r) (φ.coeff r)) :
    IsDl X A l n s F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc', hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc', fun r => ?_⟩
  have hy : ∀ r, (X.exp a * X.exp c).coeff r ∈ A := int_mul A ha.1 hc'.1
  have hx : ∀ r, ∃ z ∈ A, (ψ - φ).coeff r = (l : Ω) ^ n * z := fun r => by
    obtain ⟨z, hz, e⟩ := hc r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub, e]⟩
  obtain ⟨z1, hz1, e1⟩ := coeff_mul_mem A _ hx hy r
  obtain ⟨z2, hz2, e2⟩ := hcg r
  refine ⟨z1 + z2, add_mem hz1 hz2, ?_⟩
  have : ψ * X.exp a * X.exp c = (ψ - φ) * (X.exp a * X.exp c) + φ * X.exp a * X.exp c := by ring
  rw [this, HahnSeries.coeff_add, e1, mul_add, ← e2]; ring

def resZ (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := if r.den = 1 then φ.coeff r else 0
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem resZ_coeff (φ : HahnSeries ℚ Ω) (r : ℚ) : (resZ φ).coeff r = if r.den = 1 then φ.coeff r else 0 := rfl

end GlobalTheory.Glue.NrmT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReImMapSurjective
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.CompactDualOmega

theorem Jpq_mul_self (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jpq_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem mem_lieU {P Q : ℕ} (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ lieU P Q ↔ Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 := Iff.rfl

def reImMap (P Q : ℕ) :
    (lieU P Q × lieU P Q) →ₗ[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) where
  toFun ab := entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' x y := by
    funext ij
    simp [entries]
    ring
  map_smul' c x := by
    funext ij
    simp [entries]
    ring

theorem reImMap_injective (P Q : ℕ) : Function.Injective (reImMap P Q) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
  have h1 : a + Complex.I • b = 0 := by
    ext i j
    exact congrFun h (i, j)
  have h2 : a = -(Complex.I • b) := eq_neg_of_add_eq_zero_left h1
  have ha' := (mem_lieU a).1 ha
  have hb' := (mem_lieU b).1 hb
  have h3 : bᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * b) := eq_neg_of_add_eq_zero_left hb'
  have h4 : (-(2 * Complex.I)) • (Formalism.UG.Jpq P Q * b) = 0 := by
    rw [← ha', h2]
    simp only [conjTranspose_neg, conjTranspose_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.smul_mul, Matrix.mul_smul, h3, Complex.star_def, Complex.conj_I]
    module
  have h5 : Formalism.UG.Jpq P Q * b = 0 :=
    (smul_eq_zero.1 h4).resolve_left (by simp)
  have h6 : b = 0 := by
    have := congrArg (Formalism.UG.Jpq P Q * ·) h5
    simpa [← Matrix.mul_assoc, Jpq_mul_self] using this
  have h7 : a = 0 := by rw [h2, h6]; simp
  subst h6
  subst h7
  rfl

theorem reImMap_surjective (P Q : ℕ) : Function.Surjective (reImMap P Q) := by
  intro f
  let Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun i j => f (i, j)
  have hJ := Jpq_mul_self P Q
  have hH := Jpq_conjTranspose P Q
  have hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ,
      Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨(⟨(1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩,
    ⟨(-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q), ?_⟩), ?_⟩
  · rw [mem_lieU]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]
    module
  · rw [mem_lieU]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [neg_div]
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, this, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hJ, hl, Matrix.mul_one]
    module
  · have h1 : Complex.I * (-(Complex.I / 2)) = 1 / 2 := by
      have := Complex.I_mul_I
      linear_combination (-1 / 2 : ℂ) * this
    have h2 : (1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) +
        Complex.I • (-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) = Z := by
      rw [smul_smul, h1]
      module
    exact (congrArg entries h2).trans rfl

theorem exists_isOmegaLeb : ∀ P Q : ℕ, ∃ lam : Measure (lieU P Q), IsOmegaLeb lam := by
  intro P Q
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : FiniteDimensional ℝ (lieU P Q × lieU P Q) :=
    FiniteDimensional.of_injective (reImMap P Q) (reImMap_injective P Q)
  let e : (lieU P Q × lieU P Q) ≃L[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) :=
    (LinearEquiv.ofBijective (reImMap P Q)
      ⟨reImMap_injective P Q, reImMap_surjective P Q⟩).toContinuousLinearEquiv
  let l : Measure (lieU P Q) := Measure.addHaar
  have : ((l.prod l).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  let t : ℝ≥0 := Measure.addHaarScalarFactor volume ((l.prod l).map e)
  have ht : volume = t • (l.prod l).map e := Measure.isAddLeftInvariant_eq_smul _ _
  have ht0 : 0 < t := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hs : NNReal.sqrt t ≠ 0 := by simpa using ht0.ne'
  refine ⟨NNReal.sqrt t • l, Measure.IsAddHaarMeasure.nnreal_smul l hs, ?_⟩
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, NNReal.mul_self_sqrt,
    Measure.map_smul]
  exact ht.symm

end GlobalTheory.CompactDualOmega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.VacInt

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ}

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h, h1, -⟩ := exists_lattice_of_adelic_point D N
  exact h1 ▸ (h 1).2

theorem vac_mem_TT (hg : admG1 D) (crv : Crv D cc δ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) :
    e0 ∈ TT D (tor0 D cc δ) a d := by
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, (GlobalTheory.ThetaLine.theta_line D hg cc δ crv a d _ (Or.inr ⟨_, _, sd_std D a, sd_std D d, rfl⟩)).2.1 x hx]
  exact funext (he.2 x hx)

theorem om_vac_norm (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : k ∈ intG D a) (hk' : k' ∈ intG D d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0 := by
  obtain ⟨x, x', -, -, h⟩ := om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk')
  refine ⟨_, ?_, h⟩
  simp [W.chV.unitary, W.chV'.unitary]

theorem om_vac_fix (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) (hu : ∀ u, IntU D u → W.chV'.f u = 1) {k : GA D a} (hk : k ∈ intG D a) :
    W.Om k 1 e0 = e0 := by
  obtain ⟨x, hx, h⟩ := om_vac_left he hT W (AdLattice.intG_of_mem D a k hk)
  rw [h, hu x hx]
  simp

def sphericalPair (hg : admG1 D) (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (had : a ≤ d) (hd : Even d)
    (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0) (n : D.what₂.Tau → ℕ)
    (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) (hu : ∀ u, IntU D u → W.chV'.f u = 1) :
    Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 had hd vac W n wt (fun _ hk => om_vac_fix vac.1 (vac_mem_TT hg crv vac.1) W hu hk)
    (fun _ hj => om_vac_norm vac.1 (vac_mem_TT hg crv vac.1) W (one_mem _) hj)

theorem vacuum_eigen : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (a d : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), ∀ W : WeilO D cc δ a d e0,
      e0 ∈ TT D (tor0 D cc δ) a d ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ x x' : (AE D)ˣ, IntU D x ∧ IntU D x' ∧
        W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0) ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → ∀ k ∈ intG D a, W.Om k 1 e0 = e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → a ≤ d → Even d → ∀ t0 : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
        oddE0 D cc δ t0 a d e0 → ∀ n : D.what₂.Tau → ℕ, (∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) →
        ∃ P : Pair D cc δ t0 1, P.a = a ∧ P.d = d ∧ HEq P.e0 e0 ∧ HEq P.W W ∧ P.n = n ∧ P.F = P.e0 ∧ P.F ≠ 0 ∧
          P.J = intG D P.d) := by
  intro D hg cc δ crv a d e0 he W
  have hT := vac_mem_TT hg crv he
  exact ⟨hT, fun k hk k' hk' => om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk'),
    fun _ hk _ hk' => om_vac_norm he hT W hk hk', fun hu _ hk => om_vac_fix he hT W hu hk,
    fun hu had hd t0 pt0 vac n wt => ⟨sphericalPair hg crv pt0 had hd vac W n wt hu, rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl,
      W.nz, rfl⟩⟩

end GlobalTheory.NormSum.VacInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeAgreeOfTrivialAtPrime
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.LocAgree

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  have h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) *
      (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
    intro i j
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
  choose m hm hmS using h0
  set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs
  have hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) *
        (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
          (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
      rw [hs, hc]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩
  rw [AdLattice.inv_entry (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ k.2]
  have := Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)
  rwa [map_mul, map_natCast] at this

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((m : D.host.E) • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  show δ * embT D τ ((m : D.host.E) * z i j) = m • (δ * embT D τ (z i j))
  rw [map_mul, map_natCast, nsmul_eq_mul]
  ring

theorem matrix_move {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {N N' : ℕ} (g₁ g₂ : GL (Fin N) A)
    (g₁' g₂' : GL (Fin N') A) (s s' : ℕ) (z : Matrix (Fin N') (Fin N) R) :
    ((g₂'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * (((s * s' : ℕ) : R) • z).map f *
      (g₂ : Matrix (Fin N) (Fin N) A) =
      ((s' : A) • ((g₂'⁻¹ * g₁' : GL (Fin N') A) : Matrix (Fin N') (Fin N') A)) *
      (((g₁'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * z.map f * (g₁ : Matrix (Fin N) (Fin N) A)) *
      ((s : A) • ((g₁⁻¹ * g₂ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) := by
  have e1 : (((s * s' : ℕ) : R) • z).map f = ((s : A) * (s' : A)) • z.map f := by
    ext i j
    simp
  rw [e1]
  simp only [Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (g₁ : Matrix (Fin N) (Fin N) A), Units.mul_inv, Matrix.one_mul,
    ← Matrix.mul_assoc (g₁' : Matrix (Fin N') (Fin N') A), Units.mul_inv, Matrix.one_mul]

theorem smul_mem_La (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : cc ≠ ⊥) {N N' : ℕ}
    (g₁ g₂ : GA D N) (g₁' g₂' : GA D N')
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h₁ : Moves D (g₁ : GL (Fin N) (AE D)) L₁) (h₁' : Moves D (g₁' : GL (Fin N') (AE D)) L₁')
    (h₂ : Moves D (g₂ : GL (Fin N) (AE D)) L₂) (h₂' : Moves D (g₂' : GL (Fin N') (AE D)) L₂')
    (s s' : ℕ)
    (hs : ∀ i j, (s : AE D) * (((g₁ : GL (Fin N) (AE D))⁻¹ * (g₂ : GL (Fin N) (AE D)) : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (hs' : ∀ i j, (s' : AE D) * (((g₂' : GL (Fin N') (AE D))⁻¹ * (g₁' : GL (Fin N') (AE D)) : GL (Fin N') (AE D)) :
      Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D)
    (x : VC D N N') (hx : x ∈ La D (tor0 D cc δ) L₁ L₁') : (s * s') • x ∈ La D (tor0 D cc δ) L₂ L₂' := by
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hG cc δ hc N N' g₁ g₁' L₁ L₁' h₁ h₁' x hx
  rw [← pt_nsmul]
  refine GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hG cc δ hc N N' g₂ g₂' L₂ L₂' h₂ h₂' _ ?_
  have hI := (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hc).2.2
  intro i j
  rw [matrix_move (inc D) (g₁ : GL (Fin N) (AE D)) _ (g₁' : GL (Fin N') (AE D)), Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine hI _ (hs l j) _ ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun r _ => hI _ (hs' i r) _ (hz r l)

end GlobalTheory.NormSum.LocAgree

open GlobalTheory.NormSum.LocAgree in

theorem GlobalTheory.NormSum.La_agree_of_trivAt : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  intro D hG cc δ hc N N' q h k h' k' L₁ L₂ L₁' L₂' hk hk' h₁ h₁' h₂ h₂'
  obtain ⟨s, hsq, hs, hsi⟩ := exists_int_mul D q k hk
  obtain ⟨s', hsq', hs', hsi'⟩ := exists_int_mul D q k' hk'
  refine ⟨fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩,
    fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩⟩
  · refine smul_mem_La D hG cc δ hc h (h * k) h' (h' * k') h₁ h₁' h₂ h₂' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi'
  · refine smul_mem_La D hG cc δ hc (h * k) h (h' * k') h' h₂ h₂' h₁ h₁' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs'
end
end

