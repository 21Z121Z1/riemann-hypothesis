import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Formalism.LatticeTheta.Statement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR.LhsSum

variable {F : Type} [Field F] [NumberField F]

theorem prod_realEmb_eq_norm [IsTotallyReal F] (x : F) :
    (∏ τ : F →+* ℝ, τ x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [show ((Algebra.norm ℚ x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) from rfl, h]
  have hb : Function.Bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) := by
    refine ⟨fun τ τ' h => ?_, fun φ => ?_⟩
    · ext x
      exact Complex.ofReal_injective (RingHom.congr_fun h x)
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
        (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩
  refine Fintype.prod_bijective (fun τ : F →+* ℝ => RingHom.equivRatAlgHom F ℂ (Complex.ofRealHom.comp τ))
    ((RingHom.equivRatAlgHom F ℂ).bijective.comp hb) _ _ (fun τ => ?_)
  rfl

theorem one_le_abs_prod_int [IsTotallyReal F] (y : 𝓞 F) (hy : y ≠ 0) :
    1 ≤ |∏ τ : F →+* ℝ, τ (y : F)| := by
  rw [prod_realEmb_eq_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs h
  have h2 : (((Algebra.norm ℤ y : ℤ) : ℚ) : ℝ) = ((Algebra.norm ℤ y : ℤ) : ℝ) := by push_cast; rfl
  rw [h2]
  exact_mod_cast h1

theorem exists_lower_norm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a ∈ M, a ≠ 0 → ν ≤ |∏ τ : F →+* ℝ, τ a| := by
  obtain ⟨d, hd, hint⟩ := M.isFractional
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hP : 0 < |∏ τ : F →+* ℝ, τ (d : F)| :=
    abs_pos.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero τ).2 hd0)
  refine ⟨1 / |∏ τ : F →+* ℝ, τ (d : F)|, by positivity, fun a ha ha0 => ?_⟩
  obtain ⟨y, hy⟩ := hint a ha
  have hy' : (y : F) = (d : F) * a := by
    rw [← Algebra.smul_def]; exact hy
  have hy0 : y ≠ 0 := by
    intro h; apply mul_ne_zero hd0 ha0; rw [← hy', h]; simp
  have h1 := one_le_abs_prod_int y hy0
  rw [hy'] at h1
  simp only [map_mul, Finset.prod_mul_distrib, abs_mul] at h1
  rw [div_le_iff₀ hP]
  linarith [mul_comm (|∏ τ : F →+* ℝ, τ (d : F)|) (|∏ τ : F →+* ℝ, τ a|)]

theorem exists_lower_one_add (w : ℂ) (hw : w.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖w + (t : ℂ)‖ := by
  have him : 0 < |w.im| := abs_pos.2 hw
  refine ⟨|w.im| / (|w.im| + 1 + ‖w‖), by positivity, fun t => ?_⟩
  have h1 : |w.im| ≤ ‖w + (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w + (t : ℂ))
    simpa using this
  have h2 : |t| ≤ ‖w + (t : ℂ)‖ + ‖w‖ := by
    have := norm_sub_le (w + (t : ℂ)) w
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem floor_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (x : ℝ) :
    s / 2 * (1 + |((⌊x / s⌋ : ℤ) : ℝ)|) ≤ 1 + |x| := by
  set n : ℤ := ⌊x / s⌋ with hn
  have h1 : (n : ℝ) ≤ x / s := Int.floor_le _
  have h2 : x / s < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (n : ℝ) * s ≤ x := by rwa [le_div_iff₀ hs0] at h1
  have h2' : x < ((n : ℝ) + 1) * s := by rwa [div_lt_iff₀ hs0] at h2
  rcases le_or_gt 0 (n : ℝ) with hn0 | hn0
  · rw [abs_of_nonneg hn0, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hn1 : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by
        have : n < 0 := by exact_mod_cast hn0
        omega
      exact_mod_cast this
    rw [abs_of_neg hn0]
    have : |x| ≥ -x := neg_le_abs x
    nlinarith

def wt (m : ℤ) : ℝ := ((1 + |(m : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (m : ℤ) : 0 ≤ wt m := by unfold wt; positivity

theorem summable_wt : Summable wt := by
  have hA : Summable (fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ))) := Real.summable_abs_int_rpow (by norm_num)
  have hB : Summable (fun m : ℤ => if m = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le wt_nonneg (fun m => ?_) (hA.add hB)
  by_cases hm : m = 0
  · subst hm
    simp [wt, Real.zero_rpow]
  · simp only [hm, if_false, add_zero]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    rw [Real.rpow_neg (abs_nonneg _), wt]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    nlinarith [abs_nonneg (m : ℝ)]

theorem summable_prod_wt (ι : Type) [Fintype ι] [DecidableEq ι] :
    Summable (fun n : ι → ℤ => ∏ i, wt (n i)) := by
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' m, wt m)
    (fun n => Finset.prod_nonneg fun i _ => wt_nonneg _) (fun u => ?_)
  calc ∑ n ∈ u, ∏ i, wt (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : ι → ℤ => n i)), ∏ i, wt (n i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_image_of_mem _ hn
        · intro n _ _
          exact Finset.prod_nonneg fun i _ => wt_nonneg _
    _ = ∏ i, ∑ m ∈ u.image (fun n : ι → ℤ => n i), wt m := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' m, wt m := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg fun m _ => wt_nonneg m
        · intro i _; exact summable_wt.sum_le_tsum _ (fun m _ => wt_nonneg m)

end GlobalTheory.LipschitzTR.LhsSum

open GlobalTheory.LipschitzTR.LhsSum in

theorem GlobalTheory.LipschitzTR.summable_lhsTerm_ideal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
      ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
        Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  intro F _ _ _ M _ k hk z hz
  classical
  obtain ⟨ν, hν0, hν⟩ := exists_lower_norm M
  have hcard : 0 < Fintype.card (F →+* ℝ) := by
    rw [card_realEmb]; exact Module.finrank_pos
  set s : ℝ := min 1 (ν / 2) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsν : s ^ Fintype.card (F →+* ℝ) < ν :=
    lt_of_le_of_lt (pow_le_of_le_one hs0.le hs1 hcard.ne') (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let N : ↥(M : Set F) → ((F →+* ℝ) → ℤ) := fun a τ => ⌊τ (a : F) / s⌋
  have hN : Function.Injective N := by
    intro a b hab
    by_contra hne
    have hne' : (a : F) - b ≠ 0 := sub_ne_zero.2 (fun h => hne (Subtype.ext h))
    have hmem : (a : F) - b ∈ M := (M : Submodule (𝓞 F) F).sub_mem a.2 b.2
    have h1 := hν _ hmem hne'
    have h2 : |∏ τ : F →+* ℝ, τ ((a : F) - b)| ≤ s ^ Fintype.card (F →+* ℝ) := by
      rw [Finset.abs_prod, ← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun τ _ => ?_)
      have hf := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hab τ)
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at hf
      rw [map_sub]; exact hf.le
    linarith
  have hc : ∀ τ : F →+* ℝ, ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖z τ + (t : ℂ)‖ :=
    fun τ => exists_lower_one_add (z τ) (hz τ)
  choose c hc0 hc using hc
  set C : ℝ := ∏ τ : F →+* ℝ, ((c τ * (s / 2)) ^ k)⁻¹ with hC
  refine Summable.of_norm_bounded (g := fun a => C * ∏ τ, wt (N a τ))
    (((summable_prod_wt (F →+* ℝ)).comp_injective hN).mul_left C) (fun a => ?_)
  simp only [lhsTerm, zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib, norm_prod, norm_inv, norm_pow]
  rw [hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => by positivity) (fun τ _ => ?_)
  have hD : 0 < c τ * (s / 2) := by have := hc0 τ; positivity
  have hfl := floor_bound hs0 hs1 (τ (a : F))
  have he : c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) ≤ ‖z τ + ((τ (a : F) : ℝ) : ℂ)‖ := by
    calc c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) = c τ * (s / 2 * (1 + |((N a τ : ℤ) : ℝ)|)) := by ring
      _ ≤ c τ * (1 + |τ (a : F)|) := mul_le_mul_of_nonneg_left hfl (hc0 τ).le
      _ ≤ _ := hc τ _
  have hone : (1 : ℝ) ≤ 1 + |((N a τ : ℤ) : ℝ)| := by linarith [abs_nonneg ((N a τ : ℤ) : ℝ)]
  rw [wt, ← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ 2
      ≤ (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone hk) (by positivity)
    _ = (c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|)) ^ k := by rw [mul_pow (c τ * (s / 2))]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) he k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorComp
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace TensorProduct

namespace GlobalTheory.AnPer

theorem Step.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta h)) (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (s : Step J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Step J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  obtain ⟨n, h1, h2, h3⟩ := s
  refine ⟨fun a ↦ (1 : D) ⊗ₜ[ℂ] n a, fun a ↦ hJ _ (h1 a), fun a b ↦ by simp [h2], fun f ↦ ?_⟩
  have key : ∀ x : D ⊗[ℂ] Hol W₀, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂ x =
      Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ x +
        ∑ a, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ (LinearMap.lTensor D (dw a).toLinearMap x) *
          (1 : D) ⊗ₜ[ℂ] n a := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d h =>
      have := h3 h
      simp only [RingHom.coe_coe] at this
      simp [this, tmul_add, tmul_sum]
    | add x y hx hy =>
      simp only [map_add, hx, hy, add_mul, Finset.sum_add_distrib]
      abel
  simpa [hT] using key (Ta f)

theorem Close.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta h)) (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (h : Close J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  have key : ∀ ρ : Hol W₀ →+* C, Close J (ρ₁ : Hol W₀ →+* C) ρ → ∃ σ : Hol W₀ →ₐ[ℂ] C, (σ : Hol W₀ →+* C) = ρ ∧
      Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
        ((Algebra.TensorProduct.map (AlgHom.id ℂ D) σ).comp Ta).toRingHom := by
    intro ρ hρ
    induction hρ with
    | refl => exact ⟨ρ₁, rfl, Relation.ReflTransGen.refl⟩
    | @tail b c _ s ih =>
      obtain ⟨σ, rfl, ih⟩ := ih
      have hc : ∀ z : ℂ, c (algebraMap ℂ (Hol W₀) z) = algebraMap ℂ C z := by
        intro z
        obtain ⟨n, -, -, h3⟩ := s
        rw [h3]
        simp [Derivation.map_algebraMap]
      exact ⟨{ c with commutes' := hc }, rfl,
        Relation.ReflTransGen.tail ih (Step.tensor_comp Ta hT J J' hJ σ { c with commutes' := hc } s)⟩
  obtain ⟨σ, hσ, h'⟩ := key _ h
  obtain rfl : σ = ρ₂ := AlgHom.coe_ringHom_injective hσ
  exact h'

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.TorsMem

private theorem div_N_mem_tauPair_lattice_iff_dvd (N : ℕ) [NeZero N] (τ : ℍ) (a b : ℤ) :
    ((a : ℂ) * τ + (b : ℂ)) / N ∈ (tauPair τ).lattice ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    rw [h1, h2, eq_div_iff hN] at h
    obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.mp (tauPair τ).indep
      (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by
        rw [h1, h2, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination h)
    norm_cast at k1 k2
    exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    rw [h1, h2, eq_div_iff hN]
    push_cast
    ring

theorem div_mem_iff (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  rw [div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  intro N _ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : ∀ x : Fin 2 → ZMod N,
      tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N := by
    intro x
    simp only [tors, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ
        + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht]; push_cast; ring
    rw [e, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp [sub_eq_zero]
  · intro x y
    have e : tors N τ (x + y) - (tors N τ x + tors N τ y) =
        (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ)
        + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht, ht]; push_cast; ring
    rw [e, div_mem_iff]
    simp
  · intro x
    rw [ht, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp
  · intro x
    rw [PeriodPair.mem_lattice]
    refine ⟨(x 0).val, (x 1).val, ?_⟩
    change (((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _
    rw [ht]
    field_simp
  · intro z hz
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
    change (m : ℂ) * τ + n * 1 = N * z at h
    refine ⟨![(m : ZMod N), (n : ZMod N)], ?_⟩
    have hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N := by
      rw [eq_div_iff hN]
      linear_combination -h
    have e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] =
        (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N := by
      rw [hz', ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    rw [e, div_mem_iff]
    simp

end GlobalTheory.WpFam.TorsMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
section
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc.Translate

theorem exists_X_sub_C_mem_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k]
    (Q : Ideal k[X]) [hQ : Q.IsPrime] :
    ∀ (n : ℕ) (g : k[X]), g ≠ 0 → g.natDegree = n → g ∈ Q → ∃ r : k, X - C r ∈ Q := by
  intro n
  induction n with
  | zero =>
    intro g hg hdeg hgQ
    exfalso
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hgQ hg
    have h0 : g.coeff 0 ≠ 0 := fun h => hg (by rw [h, map_zero])
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hgQ (isUnit_C.2 (IsUnit.mk0 _ h0)))
  | succ n ih =>
    intro g hg hdeg hgQ
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g (by
      rw [Polynomial.degree_eq_natDegree hg, hdeg]; exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := g) (a := r)).2 hr
    rw [← hdiv] at hgQ hg
    rcases hQ.mem_or_mem hgQ with h | h
    · exact ⟨r, h⟩
    · refine ih _ (right_ne_zero_of_mul hg) ?_ h
      have := natDegree_divByMonic g (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [this, hdeg]; omega

theorem exists_X_sub_C_mem (T : Type) [CommRing T] [IsLocalRing T] [IsAlgClosed (ResidueField T)]
    (P : Ideal T[X]) [hPp : P.IsPrime] (hP : P.comap (C : T →+* T[X]) = maximalIdeal T)
    (hne : P ≠ (maximalIdeal T).map (C : T →+* T[X])) : ∃ c : T, X - C c ∈ P := by
  set π : T[X] →+* (ResidueField T)[X] := mapRingHom (residue T) with hπ
  have hsurj : Function.Surjective π := map_surjective _ residue_surjective
  have hker : RingHom.ker π = (maximalIdeal T).map (C : T →+* T[X]) := by
    rw [hπ, ker_mapRingHom, ker_residue]
  have hle : RingHom.ker π ≤ P := by
    rw [hker, Ideal.map_le_iff_le_comap, hP]
  haveI hQ : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hle
  have hPQ : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hle
  have hQbot : P.map π ≠ ⊥ := by
    intro h
    apply hne
    rw [← hker, ← hPQ, h, RingHom.ker_eq_comap_bot]
  obtain ⟨g, hgQ, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQbot
  obtain ⟨r, hr⟩ := exists_X_sub_C_mem_of_isAlgClosed _ _ _ g hg rfl hgQ
  obtain ⟨c, rfl⟩ := residue_surjective r
  refine ⟨c, ?_⟩
  rw [← hPQ, Ideal.mem_comap]
  simpa [hπ] using hr

end GlobalTheory.LocAcyc.Translate

namespace GlobalTheory.LocAcyc.Translate

theorem keyClosedPts_of_keyOrigin : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  intro hKO
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith at hKO
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne q hq hqu
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP' q hq hqu

end GlobalTheory.LocAcyc.Translate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionLatticeEqStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_lattice_eq : ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] [Algebra (𝓞 F) O] (La : Type) [AddCommGroup La] [Module O La] [Module.Free ℤ La] [Module.Finite ℤ La] (k : ℕ), Module.finrank ℤ La = k * Module.finrank ℚ F → ∀ c : 𝓞 F, ((LinearMap.trace ℤ La (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap : ℤ) : ℂ) = (k : ℂ) * ∑ τ : F →+* ℂ, τ (c : F) := by
  first | exact @GlobalTheory.LatticeTrace.trace_lattice_eq | exact GlobalTheory.LatticeTrace.trace_lattice_eq | (intros; apply GlobalTheory.LatticeTrace.trace_lattice_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryConjMapsKerAevalBasisAndGramStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 → ∀ (Q : K[X]) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q)) → LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧ Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) = LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧ (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first | exact @GlobalTheory.unitary_conj_ker_basis_gram | exact GlobalTheory.unitary_conj_ker_basis_gram | (intros; apply GlobalTheory.unitary_conj_ker_basis_gram <;> assumption)
end

