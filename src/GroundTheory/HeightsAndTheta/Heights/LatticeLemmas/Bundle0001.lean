import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PGaussNormBasic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GaussNormBasic

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [IsUltrametricDist L] in
theorem normAbv_apply (x : L) : normAbv L x = ‖x‖ := rfl

theorem isNonarchimedean_normAbv : IsNonarchimedean (normAbv L) :=
  fun x y ↦ IsUltrametricDist.isNonarchimedean_norm x y

theorem gaussNorm_add_le {ι : Type*} (g g' : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (g + g') ≤
      max (gaussNormOf (normAbv L) g) (gaussNormOf (normAbv L) g') := by
  refine gaussNormOf_le _ ((gaussNormOf_nonneg _ g).trans (le_max_left _ _)) fun m ↦ ?_
  rw [coeff_add]
  exact (isNonarchimedean_normAbv _ _).trans
    (max_le_max (le_gaussNormOf _ g m) (le_gaussNormOf _ g' m))

theorem gaussNorm_sum_le {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ r) :
    gaussNormOf (normAbv L) (∑ b ∈ s, f b) ≤ r :=
  Finset.sum_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ r)
    (fun _ _ ha hb ↦ (gaussNorm_add_le _ _).trans (max_le ha hb))
    (by rw [gaussNormOf_zero]; exact hr) h

omit [IsUltrametricDist L] in

theorem gaussNorm_monomial_le {ι : Type*} (d : ι →₀ ℕ) (b : L) :
    gaussNormOf (normAbv L) (monomial d b) ≤ ‖b‖ := by
  classical
  refine gaussNormOf_le _ (norm_nonneg b) fun m ↦ ?_
  rw [coeff_monomial, normAbv_apply]
  split_ifs <;> simp

omit [IsUltrametricDist L] in

theorem gaussNorm_one {ι : Type*} : gaussNormOf (normAbv L) (1 : MvPolynomial ι L) = 1 := by
  rw [← C_1, gaussNormOf_C, normAbv_apply, norm_one]

theorem mul_le_one_of_gaussNorm {ι : Type*} {a b : MvPolynomial ι L}
    (ha : gaussNormOf (normAbv L) a ≤ 1) (hb : gaussNormOf (normAbv L) b ≤ 1) :
    gaussNormOf (normAbv L) (a * b) ≤ 1 :=
  (gaussNormOf_mul_le isNonarchimedean_normAbv a b).trans
    (mul_le_one₀ ha (gaussNormOf_nonneg _ b) hb)

theorem gaussNorm_prod_le_one {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L)
    (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ 1) :
    gaussNormOf (normAbv L) (∏ b ∈ s, f b) ≤ 1 :=
  Finset.prod_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ 1)
    (fun _ _ ha hb ↦ mul_le_one_of_gaussNorm ha hb) gaussNorm_one.le h

theorem gaussNorm_pow_le_one {ι : Type*} (f : MvPolynomial ι L)
    (h : gaussNormOf (normAbv L) f ≤ 1) (n : ℕ) : gaussNormOf (normAbv L) (f ^ n) ≤ 1 := by
  induction n with
  | zero => rw [pow_zero]; exact gaussNorm_one.le
  | succ n ih => rw [pow_succ]; exact mul_le_one_of_gaussNorm ih h

theorem gaussNorm_bind₁_le {ι κ : Type*} (f : ι → MvPolynomial κ L)
    (hf : ∀ i, gaussNormOf (normAbv L) (f i) ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (bind₁ f g) ≤ gaussNormOf (normAbv L) g := by
  conv_lhs => rw [g.as_sum, map_sum]
  refine gaussNorm_sum_le _ _ (gaussNormOf_nonneg _ g) fun m _ ↦ ?_
  rw [bind₁_monomial]
  refine (gaussNormOf_mul_le isNonarchimedean_normAbv _ _).trans ?_
  rw [gaussNormOf_C]
  have h1 := gaussNorm_prod_le_one m.support (fun i ↦ f i ^ m i)
    fun i _ ↦ gaussNorm_pow_le_one _ (hf i) _
  calc normAbv L (g.coeff m) * gaussNormOf (normAbv L) (∏ i ∈ m.support, f i ^ m i)
      ≤ normAbv L (g.coeff m) * 1 :=
        mul_le_mul_of_nonneg_left h1 ((normAbv L).nonneg _)
    _ ≤ gaussNormOf (normAbv L) g := by rw [mul_one]; exact le_gaussNormOf _ g m

theorem gaussNorm_linearForm_le {κ : Type*} [Fintype κ] (b : κ → L) (c : L)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    gaussNormOf (normAbv L) (∑ j, C (b j) * X j + C c : MvPolynomial κ L) ≤ 1 := by
  refine (gaussNorm_add_le _ _).trans (max_le ?_ ?_)
  · refine gaussNorm_sum_le _ _ zero_le_one fun j _ ↦ ?_
    rw [C_mul_X_eq_monomial]
    exact (gaussNorm_monomial_le _ _).trans (hb j)
  · rw [gaussNormOf_C, normAbv_apply]; exact hc

theorem gaussNorm_affineSubst_le {ι κ : Type*} [Fintype κ] (B : Matrix ι κ L) (a : ι → L)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (affineSubst B a g) ≤ gaussNormOf (normAbv L) g :=
  gaussNorm_bind₁_le _ (fun i ↦ gaussNorm_linearForm_le _ _ (hB i) (ha i)) g

omit [IsUltrametricDist L] in

theorem affineSubst_affineSubst {ι κ μ : Type*} [Fintype κ] [Fintype μ] (B : Matrix ι κ L)
    (a : ι → L) (B' : Matrix κ μ L) (a' : κ → L) (g : MvPolynomial ι L) :
    affineSubst B' a' (affineSubst B a g) = affineSubst (B * B') (B.mulVec a' + a) g := by
  have h : ∀ i, bind₁ (fun k ↦ ∑ l, C (B' k l) * X l + C (a' k))
      (∑ j, C (B i j) * X j + C (a i) : MvPolynomial κ L) =
      ∑ l, C ((B * B') i l) * X l + C ((B.mulVec a' + a) i) := by
    intro i
    simp only [map_add, map_sum, map_mul, bind₁_C_right, bind₁_X_right, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Pi.add_apply, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := μ))]
    ring
  unfold affineSubst
  rw [bind₁_bind₁]
  simp only [h]

omit [IsUltrametricDist L] in

theorem affineSubst_one_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι L) :
    affineSubst (1 : Matrix ι ι L) 0 g = g := by
  unfold affineSubst
  have : (fun i ↦ ∑ j, C ((1 : Matrix ι ι L) i j) * X j + C ((0 : ι → L) i)) =
      (X : ι → MvPolynomial ι L) := by
    funext i
    simp [Matrix.one_apply]
  rw [this, bind₁_X_left]
  rfl

theorem norm_sum_le_one {β : Type*} (s : Finset β) (f : β → L) (h : ∀ b ∈ s, ‖f b‖ ≤ 1) :
    ‖∑ b ∈ s, f b‖ ≤ 1 :=
  Finset.sum_induction f (fun x ↦ ‖x‖ ≤ 1)
    (fun _ _ ha hb ↦ (IsUltrametricDist.isNonarchimedean_norm _ _).trans (max_le ha hb))
    (by simp) h

end GaussNormBasic

open GaussNormBasic in

theorem GaussNormBasic.proof : GaussNormBasic.Statement := by
  intro L _ _ _
  refine ⟨fun ι g g' ↦ ⟨gaussNorm_add_le g g', gaussNormOf_mul_le isNonarchimedean_normAbv g g'⟩,
    fun ι κ _ B a hB ha g ↦ gaussNorm_affineSubst_le B a hB ha g, ?_, ?_⟩
  · intro ι _ _ B a hB ha hdet hinv g
    refine le_antisymm (gaussNorm_affineSubst_le B a hB ha g) ?_
    set a' : ι → L := -(B⁻¹.mulVec a)
    have ha' : ∀ i, ‖a' i‖ ≤ 1 := fun i ↦ by
      simp only [a', Pi.neg_apply, norm_neg, Matrix.mulVec, dotProduct]
      exact norm_sum_le_one _ _ fun j _ ↦ by
        rw [norm_mul]; exact mul_le_one₀ (hinv i j) (norm_nonneg _) (ha j)
    have hcomp : affineSubst B⁻¹ a' (affineSubst B a g) = g := by
      rw [affineSubst_affineSubst, Matrix.mul_nonsing_inv _ hdet]
      have : B.mulVec a' + a = 0 := by
        simp only [a', Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
          Matrix.one_mulVec, neg_add_cancel]
      rw [this, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst B⁻¹ a' (affineSubst B a g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ hinv ha' _
  · intro ι κ _ _ P hP hsurj g
    classical
    refine le_antisymm (gaussNorm_affineSubst_le P 0 hP (fun _ ↦ by simp) g) ?_
    choose x hx hPx using fun i : ι ↦ hsurj (Pi.single i 1) fun j ↦ by
      rw [Pi.single_apply]; split_ifs <;> simp
    let S : Matrix κ ι L := fun k i ↦ x i k
    have hPS : P * S = 1 := by
      ext j i
      have := congrFun (hPx i) j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [S, this, Pi.single_apply]
    have hcomp : affineSubst S 0 (affineSubst P 0 g) = g := by
      rw [affineSubst_affineSubst, hPS, Matrix.mulVec_zero, add_zero, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst S 0 (affineSubst P 0 g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ (fun k i ↦ hx i k) (fun _ ↦ by simp) _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHeightOfPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ComplexAt TensorProduct

noncomputable section

namespace HeightOfPointAlt

variable {K : Type*} [Field K] [NumberField K]

theorem adicAbv_sum_le (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i ∈ s, NumberField.HeightOneSpectrum.adicAbv K v (f i) ≤ r) :
    NumberField.HeightOneSpectrum.adicAbv K v (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem finite_adicAbv_ne_one {c : K} (hc : c ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      NumberField.HeightOneSpectrum.adicAbv K v c ≠ 1}.Finite := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  refine (hfin.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset ?_
  intro v hv
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  exact hv

variable {F : Type*} [Field F] [NumberField F] [Algebra F K]

omit [NumberField F] in

theorem adicAbv_intToField_le_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 F) :
    NumberField.HeightOneSpectrum.adicAbv K v (intToField F K a) ≤ 1 := by
  let b : 𝓞 K := ⟨algebraMap F K (a : F), (RingOfIntegers.isIntegral_coe a).algebraMap⟩
  have hb : intToField F K a = algebraMap (𝓞 K) K b := rfl
  rw [hb]
  exact v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) b

variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]

def archLinear (τ : K →+* ℂ) (yv : DualVec F W K) :
    Fibre (τ.comp (algebraMap F K)) W →ₗ[ℂ] ComplexAt (τ.comp (algebraMap F K)) where
  toFun := archFunctional τ yv
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z e =>
      rw [TensorProduct.smul_tmul', RingHom.id_apply]
      simp only [archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
      exact smul_mul_assoc c z _
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

theorem archDualNorm_pos (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (x : W)
    (hx : yv x ≠ 0) : 0 < archDualNorm h τ yv := by
  set σ := τ.comp (algebraMap F K)
  let φ : FibreSpace h σ →ₗ[ℂ] ℂ := (ofComplex σ).symm.toLinearMap ∘ₗ archLinear τ yv ∘ₗ
    (FibreSpace.equiv h σ).symm.toLinearMap
  have hφ : ∀ ξ, φ ξ = (ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ)) :=
    fun _ => rfl
  let φc := LinearMap.toContinuousLinearMap φ
  have hbdd : BddAbove (Set.range fun ξ : {ξ : FibreSpace h σ // ‖ξ‖ ≤ 1} =>
      ‖(ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))‖) := by
    refine ⟨‖φc‖, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    show ‖φ ξ‖ ≤ _
    calc ‖φ ξ‖ = ‖φc ξ‖ := rfl
      _ ≤ ‖φc‖ * ‖(ξ : FibreSpace h σ)‖ := φc.le_opNorm _
      _ ≤ ‖φc‖ * 1 := mul_le_mul_of_nonneg_left ξ.2 (norm_nonneg φc)
      _ = ‖φc‖ := mul_one _
  set ξ₀ : FibreSpace h σ := FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ x)
  have hξ₀ : φ ξ₀ = τ (yv x) := by
    rw [hφ]
    simp only [ξ₀, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, one_mul]
    rfl
  have hne : ξ₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ₀
    exact (map_ne_zero τ).mpr hx hξ₀.symm
  set ξ₁ : FibreSpace h σ := ((‖ξ₀‖ : ℂ)⁻¹) • ξ₀
  have hξ₁ : ‖ξ₁‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hne)
  have hφ₁ : φ ξ₁ ≠ 0 := by
    rw [map_smul, hξ₀, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero ?_) ((map_ne_zero τ).mpr hx)
    exact_mod_cast (norm_ne_zero_iff.mpr hne)
  calc (0 : ℝ) < ‖φ ξ₁‖ := norm_pos_iff.mpr hφ₁
    _ ≤ archDualNorm h τ yv := by
      rw [hφ]
      exact le_ciSup hbdd ⟨ξ₁, hξ₁⟩

end HeightOfPointAlt

open HeightOfPointAlt

theorem heightOfPoint : HeightOfPoint.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ yv hyv
  have hspan : ∀ x : W, ∃ c : Fin n → 𝓞 F, ∑ k, c k • w k = x := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hw ▸ Submodule.mem_top)
  have hyvx : ∀ c : Fin n → 𝓞 F, yv (∑ k, c k • w k) = ∑ k, intToField F K (c k) * yv (w k) := by
    intro c
    simp only [map_sum, map_smulₛₗ, smul_eq_mul]
  set M : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) with hMdef
  have hM0 : ∀ v, 0 ≤ M v := fun v => Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _
  have hleM : ∀ v k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ≤ M v := fun v k =>
    by
    show _ ≤ ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))
    exact le_ciSup (f := fun k => NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)))
      (Finite.bddAbove_range _) k
  have hle : ∀ v x, NumberField.HeightOneSpectrum.adicAbv K v (yv x) ≤ M v := by
    intro v x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) :=
          mul_le_mul_of_nonneg_right (adicAbv_intToField_le_one v (c k)) (AbsoluteValue.nonneg _ _)
      _ ≤ M v := by rw [one_mul]; exact hleM v k
  have hdual : ∀ v, dualNormAt v yv = M v := by
    intro v
    have hbdd : BddAbove (Set.range fun x : W =>
        NumberField.HeightOneSpectrum.adicAbv K v (yv x)) := by
      refine ⟨M v, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle v x
    unfold dualNormAt
    refine le_antisymm (Real.iSup_le (hle v) (hM0 v)) ?_
    exact Real.iSup_le (fun k => le_ciSup hbdd (w k))
      (Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _)
  have hgauss : ∀ v, gaussNorm v (∑ k, C (yv (w k)) * X k : MvPolynomial (Fin n) K) = M v := by
    intro v
    rw [gaussNorm_eq_gaussNormOf]
    refine le_antisymm (gaussNormOf_le _ (hM0 v) fun m => ?_) ?_
    · rw [coeff_sum]
      refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
      rw [coeff_C_mul, map_mul, coeff_X]
      split_ifs
      · rw [map_one, mul_one]; exact hleM v k
      · rw [map_zero, mul_zero]; exact hM0 v
    · refine Real.iSup_le (fun k => ?_) (gaussNormOf_nonneg _ _)
      have hc : coeff (Finsupp.single k 1) (∑ j, C (yv (w j)) * X j : MvPolynomial (Fin n) K) =
          yv (w k) := by
        rw [coeff_sum, Finset.sum_eq_single k]
        · rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one]
        · intro j _ hj
          rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
          intro hjk
          exact hj (Finsupp.single_left_injective one_ne_zero hjk)
        · intro hk; exact absurd (Finset.mem_univ k) hk
      rw [← hc]
      exact le_gaussNormOf _ _ _

  obtain ⟨k₀, hk₀⟩ : ∃ k, yv (w k) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hyv
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    simp [hcon]
  have hMpos : ∀ v, 0 < M v := fun v =>
    lt_of_lt_of_le ((NumberField.HeightOneSpectrum.adicAbv K v).pos hk₀) (hleM v k₀)
  have hMfin : (Function.support fun v => Real.log (M v)).Finite := by
    refine (Set.Finite.biUnion (Set.toFinite {k | yv (w k) ≠ 0})
      fun k hk => finite_adicAbv_ne_one hk).subset ?_
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
    apply hv
    have h1 : M v = 1 := by
      refine le_antisymm (Real.iSup_le (fun k => ?_) zero_le_one) ?_
      · by_cases hk : yv (w k) = 0
        · rw [hk, map_zero]; exact zero_le_one
        · exact (hnot k hk).le
      · rw [← hnot k₀ hk₀]; exact hleM v k₀
    simp only [h1, Real.log_one]
  refine ⟨fun v => ⟨hdual v, (hdual v).trans (hgauss v).symm⟩, fun x hx => ?_⟩
  have hAfin : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x))).Finite := by
    refine (finite_adicAbv_ne_one hx).subset ?_
    intro v hv h1
    apply hv
    simp only [h1, Real.log_one]
  have e1 : ∀ v, Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x) / dualNormAt v yv) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x)) - Real.log (M v) := by
    intro v
    rw [hdual, Real.log_div ((NumberField.HeightOneSpectrum.adicAbv K v).pos hx).ne' (hMpos v).ne']
  have e2 : ∀ τ : K →+* ℂ, Real.log (‖τ (yv x)‖ / archDualNorm h τ yv) =
      Real.log ‖τ (yv x)‖ - Real.log (archDualNorm h τ yv) := by
    intro τ
    exact Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero τ).mpr hx))
      (archDualNorm_pos h τ yv x hx).ne'
  have e3 : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv) =
      ∑ᶠ v, Real.log (M v) := finsum_congr fun v => by rw [hdual]
  unfold heightWith
  simp only [e1, e2]
  rw [finsum_sub_distrib hAfin hMfin, Finset.sum_sub_distrib, finsum_log_adicAbv hx,
    sum_log_norm_embeddings hx, e3]
  ring

theorem HeightOfPoint.proof (_h1 : GaussNormBasic.Statement) : HeightOfPoint.Statement :=
  heightOfPoint

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSchwartzZippelPerVariable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SchwartzZippelPerVariable.proof : SchwartzZippelPerVariable.Statement := by
  intro R _ _ _ q d S G hG hdeg
  have key := MvPolynomial.schwartz_zippel_sum_degreeOf hG (fun _ : Fin q ↦ S)
  have hsum : ∑ i : Fin q, ((G.degreeOf i : ℚ≥0) / (S.card : ℚ≥0)) ≤
      ∑ _i : Fin q, ((d : ℚ≥0) / (S.card : ℚ≥0)) :=
    Finset.sum_le_sum fun i _ ↦ by gcongr; exact_mod_cast hdeg i
  have key' := key.trans hsum
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    nsmul_eq_mul] at key'
  change ((((Fintype.piFinset fun _ : Fin q ↦ S).filter fun c ↦ eval c G = 0).card : ℕ) : ℚ≥0) /
    (S.card : ℚ≥0) ^ q ≤ (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) at key'
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero, div_one, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero,
      Nat.cast_eq_zero] at key'
    rw [key']
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos S.card with hs | hs
  · have : S = ∅ := Finset.card_eq_zero.mp hs
    subst this
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    simp [Fintype.piFinset_empty]
  have hs' : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hs
  have hpow : (S.card : ℚ≥0) ^ q = (S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [div_le_iff₀ (pow_pos hs' q), hpow] at key'
  have hcalc : (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) *
      ((S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1)) =
      (q : ℚ≥0) * d * (S.card : ℚ≥0) ^ (q - 1) := by
    field_simp
  rw [hcalc] at key'
  exact_mod_cast key'

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsFibreMahler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

def FibreMahlerForms.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (W : Type) [AddCommGroup W] [Module (𝓞 F) W]
    [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W] (h : HermitianMetric F W) (n : ℕ)
    (w : Fin n → W), Submodule.span (𝓞 F) (Set.range w) = ⊤ →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] (τ : K →+* ℂ) (m : ℕ)
      (yv : Fin m → DualVec F W K), (∀ q, yv q ≠ 0) → ∀ a : ℂ, a ≠ 0 →
        fibreMahler h (τ.comp (algebraMap F K)) w (C a * ∏ q, ∑ k, C (τ (yv q (w k))) * X k) =
          Real.log ‖a‖ + ∑ q, (Real.log (archDualNorm h τ (yv q)) -
            (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)

example : HermitianMetric ℚ (Fin 2 → 𝓞 ℚ) := HermitianMetric.standard ℚ (Fin 2)

end

end GroundTheory.Heights₂.Heights
end

