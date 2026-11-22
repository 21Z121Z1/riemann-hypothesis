import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrResCard

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def redCoord {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (x : S) (k : Fin d) :
    v.adicCompletionIntegers F ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.mk _ ⟨(Algebra.TensorProduct.basis (Fv F v) bs).repr x k,
    (show (x : Fv F v ⊗[F] E) ∈ Rv bs v from hS ▸ x.2) k⟩

theorem redCoord_eq_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) (x y : S) :
    redCoord bs v S hS ϖ x = redCoord bs v S hS ϖ y ↔ x - y ∈ lev (⟨_, hϖ⟩ : S) 1 := by
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  have hsm : ∀ z : Fv F v ⊗[F] E, z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (ϖ : Fv F v) • z := by
    intro z
    rw [Algebra.smul_def, mul_comm]
  rw [show lev (⟨_, hϖ⟩ : S) 1 = Ideal.span {(⟨_, hϖ⟩ : S) ^ 1} from rfl, pow_one,
    Ideal.mem_span_singleton']
  constructor
  · intro h
    have hk : ∀ k, ∃ t : v.adicCompletionIntegers F, (t : Fv F v) * ϖ = B.repr x k - B.repr y k := by
      intro k
      have h1 := congrFun h k
      simp only [redCoord] at h1
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      refine ⟨t, ?_⟩
      have h2 := congrArg Subtype.val ht
      push_cast at h2
      exact h2
    choose t ht using hk
    let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
    have hz : ∀ k, B.repr z k = t k := by
      intro k
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hzS : z ∈ S := by
      have hzR : z ∈ Rv bs v := by
        intro k
        rw [hz k]
        exact (t k).2
      rw [← hS] at hzR
      exact hzR
    refine ⟨⟨z, hzS⟩, ?_⟩
    apply Subtype.ext
    show z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (x : Fv F v ⊗[F] E) - y
    rw [hsm, B.ext_elem_iff]
    intro k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hz k, map_sub, Finsupp.sub_apply, mul_comm]
    exact ht k
  · rintro ⟨a, ha⟩
    have hxy : (x : Fv F v ⊗[F] E) - y = (ϖ : Fv F v) • (a : Fv F v ⊗[F] E) := by
      rw [← hsm]
      exact (congrArg Subtype.val ha).symm
    have haR : (a : Fv F v ⊗[F] E) ∈ Rv bs v := hS ▸ a.2
    funext k
    simp only [redCoord]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨B.repr a k, haR k⟩, ?_⟩
    apply Subtype.ext
    push_cast
    have h3 := congrArg (fun w => B.repr w k) hxy
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
    rw [mul_comm, ← h3]

theorem redCoord_surjective {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) : Function.Surjective (redCoord bs v S hS ϖ) := by
  intro g
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  choose t ht using fun k => Ideal.Quotient.mk_surjective (g k)
  let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
  have hz : ∀ k, B.repr z k = t k := by
    intro k
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hzS : z ∈ S := by
    have hzR : z ∈ Rv bs v := by
      intro k
      rw [hz k]
      exact (t k).2
    rw [← hS] at hzR
    exact hzR
  refine ⟨⟨z, hzS⟩, ?_⟩
  funext k
  simp only [redCoord]
  rw [← ht k]
  congr 1
  exact Subtype.ext (hz k)

theorem card_quot {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) :
    Nat.card (S ⧸ lev (⟨_, hϖ⟩ : S) 1) = Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) ^ d := by
  have hsurj := Ideal.Quotient.mk_surjective (I := lev (⟨_, hϖ⟩ : S) 1)
  let sec := Function.surjInv hsurj
  have hsec : ∀ q, Ideal.Quotient.mk _ (sec q) = q := Function.surjInv_eq hsurj
  let g : S ⧸ lev (⟨_, hϖ⟩ : S) 1 → (Fin d → v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) :=
    fun q => redCoord bs v S hS ϖ (sec q)
  have hg : Function.Bijective g := by
    constructor
    · intro q₁ q₂ h
      rw [← hsec q₁, ← hsec q₂, Ideal.Quotient.eq]
      exact (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mp h
    · intro w
      obtain ⟨x, hx⟩ := redCoord_surjective bs v S hS ϖ w
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [← hx]
      apply (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mpr
      rw [← Ideal.Quotient.eq, hsec]
  rw [Nat.card_congr (Equiv.ofBijective g hg), Nat.card_fun, Nat.card_fin]

theorem q3 : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨hCM, -, hS, -, -, -, -, hcard⟩ := hQ
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis bs, Fintype.card_fin]
  subst hd
  rw [card_quot bs v S hS ϖ hϖ, hcard]

end GlobalTheory.CompanionTheory.GunrResCard
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwo
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ValuationCompleteness

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr Filter Topology
open scoped TensorProduct

section Abstract

variable {K A : Type} [NormedField K] [CommRing A] [Algebra K A] {d : ℕ}
  (b : Module.Basis (Fin d) K A) (S : Subring A)

theorem mem_lev_iff (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (k : ℕ) :
    a ∈ lev (⟨_, hϖ⟩ : S) k ↔ ∀ i, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k := by
  have hpow : ∀ c : A, c * (algebraMap K A ϖ) ^ k = ϖ ^ k • c := by
    intro c
    rw [← map_pow, Algebra.smul_def, mul_comm]
  have hcoe : ∀ c : S, ((c * (⟨_, hϖ⟩ : S) ^ k : S) : A) = ϖ ^ k • (c : A) := by
    intro c
    rw [← hpow]
    rfl
  constructor
  · intro ha i
    rw [lev, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    have hc' : (a : A) = ϖ ^ k • (c : A) := by
      rw [← hc, hcoe]
    rw [hc', map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have hci := (hS c).1 c.2 i
    calc ‖ϖ‖ ^ k * ‖b.repr (c : A) i‖ ≤ ‖ϖ‖ ^ k * 1 := by gcongr
      _ = ‖ϖ‖ ^ k := mul_one _
  · intro ha
    rw [lev, Ideal.mem_span_singleton']
    have hpos : 0 < ‖ϖ‖ ^ k := pow_pos (norm_pos_iff.mpr h0) k
    have hcS : (ϖ ^ k)⁻¹ • (a : A) ∈ S := by
      rw [hS]
      intro i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow,
        inv_mul_le_iff₀ hpos, mul_one]
      exact ha i
    refine ⟨⟨_, hcS⟩, ?_⟩
    apply Subtype.ext
    rw [hcoe]
    change ϖ ^ k • ((ϖ ^ k)⁻¹ • (a : A)) = (a : A)
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero k h0), one_smul]

theorem separated (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (h : ∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) : a = 0 := by
  have hi : ∀ i, b.repr (a : A) i = 0 := by
    intro i
    have hle : ∀ k : ℕ, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k :=
      fun k => (mem_lev_iff b S hS h0 hϖ a k).1 (h k) i
    have ht : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hle)
  have hr : b.repr (a : A) = 0 := by
    ext i
    exact hi i
  have ha : (a : A) = 0 := (LinearEquiv.map_eq_zero_iff b.repr).mp hr
  exact_mod_cast ha

variable [CompleteSpace K] [IsUltrametricDist K]

theorem complete (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (f : ℕ → S) (hf : ∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) :
    ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k := by
  set x : ℕ → Fin d → K := fun k i => b.repr (f k : A) i with hx
  have hstep : ∀ k i, ‖x (k + 1) i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro k i
    have := (mem_lev_iff b S hS h0 hϖ _ k).1 (hf k) i
    simpa [hx, map_sub] using this
  have hn0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have hle1 : ‖ϖ‖ ≤ 1 := le_of_lt h1
  have hfar : ∀ i k m, k ≤ m → ‖x m i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : x (m + 1) i - x k i = (x (m + 1) i - x m i) + (x m i - x k i) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep m i).trans (pow_le_pow_of_le_one hn0 hle1 hkm)
  have hcau : ∀ i, CauchySeq (fun k => x k i) := by
    intro i
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 h1 (fun n => ?_)
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    exact hstep n i
  choose c hc using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hbd : ∀ i k, ‖c i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k
    have ht : Tendsto (fun m => ‖x m i - x k i‖) atTop (𝓝 ‖c i - x k i‖) :=
      ((hc i).sub_const _).norm
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    exact hfar i k m hm
  set aA : A := b.equivFun.symm c with haA
  have hrep : ∀ i, b.repr aA i = c i := by
    intro i
    rw [← b.equivFun_apply, haA, LinearEquiv.apply_symm_apply]
  have hmem : aA ∈ S := by
    rw [hS]
    intro i
    rw [hrep]
    have e : c i = (c i - x 0 i) + x 0 i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using hbd i 0
    · exact (hS _).1 (f 0).2 i
  refine ⟨⟨aA, hmem⟩, fun k => ?_⟩
  rw [mem_lev_iff b S hS h0 hϖ]
  intro i
  have e : ((⟨aA, hmem⟩ - f k : S) : A) = aA - (f k : A) := rfl
  rw [e, map_sub, Finsupp.sub_apply, hrep]
  exact hbd i k

end Abstract

theorem q2 : Q2 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨-, -, hSR, -, h0, h1, -, -⟩ := hQ
  have hS : ∀ x, x ∈ S ↔ ∀ i, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x i‖ ≤ 1 := by
    intro x
    rw [← SetLike.mem_coe, hSR]
    exact forall_congr' fun i =>
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).trans
        Valued.toNormedField.norm_le_one_iff.symm
  exact ⟨fun a ha => separated _ S hS h0 h1 hϖ a ha, fun f hf => complete _ S hS h0 h1 hϖ f hf⟩

end GlobalTheory.CompanionTheory.ValuationCompleteness

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedDoubleIntegralBoundStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_double_integral_bound : ∀ (g φ : ℝ → ℝ), Measurable g → Measurable φ → Integrable g → Integrable φ →
    (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ φ x) → (∀ x, φ x ≤ 1) → ∀ α β : ℝ, α ≠ 0 → β ≠ 0 →
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2) ≤ (∫ x, g x) * (∫ x, φ x) / max |α| |β| := by
  first | exact @GlobalTheory.CompanionTheory.Shear.integral_shear_le | exact GlobalTheory.CompanionTheory.Shear.integral_shear_le | (intros; apply GlobalTheory.CompanionTheory.Shear.integral_shear_le <;> assumption)
end

