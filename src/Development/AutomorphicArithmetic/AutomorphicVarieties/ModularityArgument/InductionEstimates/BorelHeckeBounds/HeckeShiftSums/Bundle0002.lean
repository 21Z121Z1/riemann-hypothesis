import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem vl (i : Fin 2) : ((finSumFinEquiv (Sum.inl i) : Fin (2 + 2)) : ℕ) = i := rfl

private theorem vr (i : Fin 2) : ((finSumFinEquiv (Sum.inr i) : Fin (2 + 2)) : ℕ) = 2 + i := rfl

private theorem blk_val' (x y : GL (Fin 2) R) :
    (blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private theorem blk_low (x y : GL (Fin 2) R) (i j : Fin (2 + 2)) (hi : 2 ≤ (i : ℕ)) (hj : (j : ℕ) < 2) :
    (blk x y).val i j = 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk_val', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [vl] at hi; omega
  · rfl
  · rfl
  · rw [vr] at hj; omega

private theorem blk_tri (x y : GL (Fin 2) R) (hx : x.val.IsUpperTriangular) (hy : y.val.IsUpperTriangular) :
    (blk x y).val.IsUpperTriangular := by
  intro i j hij
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk_val', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · have h : ((finSumFinEquiv (Sum.inl j) : Fin (2 + 2)) : ℕ) < (finSumFinEquiv (Sum.inl i) : Fin (2 + 2)) := hij
    rw [vl, vl] at h
    exact hx h
  · rfl
  · rfl
  · have h : ((finSumFinEquiv (Sum.inr j) : Fin (2 + 2)) : ℕ) < (finSumFinEquiv (Sum.inr i) : Fin (2 + 2)) := hij
    rw [vr, vr] at h
    exact hy (show (j : ℕ) < i by omega)

private theorem unip_tri (X : UPos (2 + 2) 2 → R) : (unipGL X).val.IsUpperTriangular := by
  intro i j hij
  have h : (j : ℕ) < i := hij
  have hne : i ≠ j := fun e => by subst e; omega
  simp only [coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply_ne hne, zero_add]
  rw [dif_neg (by omega)]

private theorem sandwich {A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R}
    (hA : ∀ i a : Fin (2 + 2), 2 ≤ (i : ℕ) → (a : ℕ) < 2 → A i a = 0)
    (hB : ∀ i a : Fin (2 + 2), 2 ≤ (i : ℕ) → (a : ℕ) < 2 → B i a = 0) (Z : UPos (2 + 2) 2 → R) :
    ∃ Y : UPos (2 + 2) 2 → R, A * blockEntry Z * B = blockEntry Y := by
  refine ⟨fun p => (A * blockEntry Z * B) p.1.1 p.1.2, ?_⟩
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
    rw [blockEntry_apply]
    split_ifs with h'
    · by_cases hi : 2 ≤ (i : ℕ)
      · rw [hA i a hi h'.1, zero_mul, zero_mul]
      · rw [hB b j h'.2 (by omega), mul_zero]
    · rw [mul_zero, zero_mul]

private theorem blk_unip (x y : GL (Fin 2) R) (X : UPos (2 + 2) 2 → R) :
    ∃ Y : UPos (2 + 2) 2 → R, blk x y * unipGL X = unipGL Y * blk x y := by
  obtain ⟨Y, hY⟩ := sandwich (blk_low x y) (blk_low x⁻¹ y⁻¹) X
  refine ⟨Y, ?_⟩
  rw [← mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have e : (blk x y)⁻¹ = blk x⁻¹ y⁻¹ := Units.ext rfl
  simp only [Units.val_mul, coe_unipGL, unipMatrix]
  rw [← hY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, e]

private theorem blk_cont' [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun p : GL (Fin 2) R × GL (Fin 2) R => blk p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem blk_diag (d : Fin (2 + 2) → Rˣ) :
    diagUnits (2 + 2) d = blk (diagUnits 2 fun i => d (Fin.castAdd 2 i)) (diagUnits 2 fun i => d (Fin.natAdd 2 i)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk_val', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, coe_diagUnits,
    Matrix.fromBlocks_diagonal, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.redEx :
    ∀ {K : Type} [Field K] [NumberField K], ∃ (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Red ω t := by
  intro K _ _
  obtain ⟨ω₄, hc₄, hb₄, t₄, ht₄, h₄⟩ := exists_siegelSet (K := K) (2 + 2)
  obtain ⟨ω₂, hc₂, hb₂, t₂, ht₂, h₂⟩ := exists_siegelSet (K := K) 2
  obtain ⟨-, -, C, hC, -, hCX⟩ := volOne (K := K) (2 + 2) 2
  obtain ⟨hlv, -, -, -, -, hmul, -, -, -, -, hK, hmax⟩ := blkLaws (K := K)
  have hz : zt K 0 = 1 := by
    rw [zt, ← map_one (centralSection K 2)]
    exact congrArg _ (Subtype.ext Real.exp_zero)
  have hlv0 : ∀ a b : G1 K 2, ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := fun a b => by
    rw [hlv, neg_zero, hz, mul_one, mul_one]
  let F : (UPos (2 + 2) 2 → 𝔸[K]) × AdelicGLn.AdelicGL K 2 × AdelicGLn.AdelicGL K 2 → AdelicGLn.AdelicGL K (2 + 2) :=
    fun p => unipGL p.1 * blk p.2.1 p.2.2
  have hF : Continuous F := (continuous_unipGL.comp continuous_fst).mul (blk_cont'.comp continuous_snd)
  refine ⟨ω₄ ∪ F '' (C ×ˢ ω₂ ×ˢ ω₂), min t₄ t₂, ⟨hc₄.union ((hC.prod (hc₂.prod hc₂)).image hF), ?_⟩,
    lt_min ht₄ ht₂, fun x => ?_, fun z => ?_⟩
  · rintro _ (h | ⟨p, ⟨-, h1, h2⟩, rfl⟩)
    · exact hb₄ h
    · exact Subgroup.mul_mem _ (mem_adelicBorel.2 (unip_tri p.1))
        (mem_adelicBorel.2 (blk_tri _ _ (mem_adelicBorel.1 (hb₂ h1)) (mem_adelicBorel.1 (hb₂ h2))))
  · obtain ⟨γ, b, hb, _, ⟨r, hr, hrt, rfl⟩, k, hk, e⟩ := h₄ x
    refine ⟨⟨AdelicGLn.diagonal K _ γ, rationalGL_le_normOneGL ⟨γ, rfl⟩⟩, ⟨γ, rfl⟩, r,
      ⟨hr, b, Or.inl hb, k, hk, e⟩, fun i j hij => ?_⟩
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hr j).le).trans (hrt i j hij)
  · obtain ⟨X, m₁, m₂, s, k, hk, rfl⟩ := iwa z
    obtain ⟨γ₁, b₁, hb₁, _, ⟨r₁, hr₁, hrt₁, rfl⟩, k₁, hk₁, e₁⟩ := h₂ ((m₁ : AdelicGLn.AdelicGL K 2) * zt K s)
    obtain ⟨γ₂, b₂, hb₂', _, ⟨r₂, hr₂, hrt₂, rfl⟩, k₂, hk₂, e₂⟩ := h₂ ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-s))
    let g₁ : Gam K 2 := ⟨⟨AdelicGLn.diagonal K _ γ₁, rationalGL_le_normOneGL ⟨γ₁, rfl⟩⟩, ⟨γ₁, rfl⟩⟩
    let g₂ : Gam K 2 := ⟨⟨AdelicGLn.diagonal K _ γ₂, rationalGL_le_normOneGL ⟨γ₂, rfl⟩⟩, ⟨γ₂, rfl⟩⟩
    obtain ⟨Y, hY⟩ := blk_unip (AdelicGLn.diagonal K _ γ₁) (AdelicGLn.diagonal K _ γ₂) X
    obtain ⟨ξ, hξ⟩ := hCX Y
    have hρ : ∀ i : Fin (2 + 2), 0 < (Fin.append r₁ r₂ : Fin (2 + 2) → ℝ) i := fun i => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact hr₁ i
      · rw [Fin.append_right]; exact hr₂ i
    have hkk : blk k₁ k₂ ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := by
      have := hK ⟨k₁, (hmax 2).2 k₁ hk₁⟩ hk₁ ⟨k₂, (hmax 2).2 k₂ hk₂⟩ hk₂
      rw [← hlv0 ⟨k₁, (hmax 2).2 k₁ hk₁⟩ ⟨k₂, (hmax 2).2 k₂ hk₂⟩]
      exact this
    have hk' : (k : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := hk
    have hmem : F (ξ.1 + Y, b₁, b₂) ∈ ω₄ ∪ F '' (C ×ˢ ω₂ ×ˢ ω₂) :=
      Or.inr (Set.mem_image_of_mem F ⟨hξ, hb₁, hb₂'⟩)
    have hδ : nn ξ.1 * lv (g₁ : G1 K 2) (g₂ : G1 K 2) 0 ∈ PK K := ((pkLaws (K := K)).2.1 _).2 ⟨ξ, g₁, g₂, rfl⟩
    refine ⟨nn ξ.1 * lv (g₁ : G1 K 2) (g₂ : G1 K 2) 0, hδ, Fin.append r₁ r₂,
      ⟨hρ, F (ξ.1 + Y, b₁, b₂), hmem, blk k₁ k₂ * (k : AdelicGLn.AdelicGL K (2 + 2)),
        Subgroup.mul_mem _ hkk hk', ?_⟩, ?_, ?_⟩
    · rw [blk_diag]
      simp only [Fin.append_left, Fin.append_right, F, Subgroup.coe_mul, hlv0, coe_unipOne, unipGL_add]
      rw [hlv]
      change unipGL ξ.1 * blk (AdelicGLn.diagonal K _ γ₁) (AdelicGLn.diagonal K _ γ₂) * _ = _
      simp only [← mul_assoc]
      rw [mul_assoc (unipGL ξ.1) _ (unipGL X), hY, ← mul_assoc, mul_assoc (unipGL ξ.1 * unipGL Y), hmul,
        mul_assoc (unipGL ξ.1 * unipGL Y) (blk b₁ b₂), hmul, mul_assoc (unipGL ξ.1 * unipGL Y) (blk (b₁ * _) (b₂ * _)), hmul,
        ← e₁, ← e₂]
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hr₁ 1).le).trans (hrt₁ 0 1 rfl)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hr₂ 1).le).trans (hrt₂ 0 1 rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.RootDecay
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

open scoped Pointwise

private theorem sub_ct_le_of_altSum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n) (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne K n r s * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => rc μ f φ (unipOne K n r s * x) with hH
  set c : ℂ := ct r (rc μ f φ) x with hc
  have hHc : Continuous H :=
    (continuous_rconv (Gam K n) μ f φ).comp ((continuous_unipOne r).mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := by
    intro ξ hξ s
    simp only [H, rc]
    rw [unipOne_add, mul_assoc,
      rconv_mul_left (Gam K n) μ f φ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hcint : IntegrableOn (fun _ : UPos n r → 𝔸[K] => c) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    integrableOn_const (by rw [hD1]; exact ENNReal.one_ne_top)
  have hmean0 : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = c := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    rfl
  have hi0 : IntegrableOn H (scaledUnipFD K n r M) (unipMeasure K n r) := by simpa using hint 0
  have hmean : ∫ y in scaledUnipFD K n r M, (H y - c) ∂unipMeasure K n r = 0 := by
    rw [integral_sub hi0 hcint, hmean0, setIntegral_const, measureReal_def, hD1]
    simp
  have h0 := norm_le_of_forall_altSum_le hD hD1 (k + 1) (fun s => H s - c)
    (fun ξ hξ s => by simp only [hper ξ hξ s]) (fun t => (hint t).sub hcint) hmean B (fun y hy => by
      have := hB y hy
      rw [altSum_succ] at this ⊢
      simpa only [sub_sub_sub_cancel_right] using this)
  simpa [H, unipOne_zero] using h0

private theorem sub_ct_le_of_altSum_inf {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n)
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, f ((x⁻¹ * unipOne K n r z * x)⁻¹ * w) = f w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  refine sub_ct_le_of_altSum (r := r) μ f φ hM x k fun y hy => ?_
  have key : ∀ ε : Fin (k + 1) → Bool,
      rc μ f φ (unipOne K n r (0 + altPoint y ε) * x) =
        rc μ f φ (unipOne K n r (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipOne K n r (altPoint y ε) * x = unipOne K n r (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipOne K n r (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipOne_add, truncInf_add_truncFin]
    rw [hP]
    exact rconv_mul_right μ f φ hfinP _
  have heq : altSum (k + 1) (fun s => rc μ f φ (unipOne K n r s * x)) y 0 =
      altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.rootDecay :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n), IsLeftSmooth a → ∀ (ω : Set (AdelicGLn.AdelicGL K n)) (t : ℝ), Bor ω → 0 < t →
      ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ (φ : L2 μ) (ρ : Fin n → ℝ) (x : G1 K n) (R : ℝ), Sg ω ρ x → Full t ρ → 1 ≤ R → Rat R ρ →
        ‖rc μ a φ x - ct r (rc μ a φ) x‖ ≤ C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * R ^ N * ‖φ‖ := by
  intro K _ _ n μ _ f hf ω t hBor ht r hr hrn
  obtain ⟨hω, hωB⟩ := hBor
  obtain ⟨U, hU, hUf⟩ := hf.2
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL K n)
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht hV₀c
  refine ⟨N, fun k => ?_⟩
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  set R₁ := C₁' * t⁻¹
  obtain ⟨c, hc⟩ := diffBd f hf (k + 1) R₁
  set c' := max c 0
  have h𝒞 := isCompact_unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁)
  set Q := archProj K n '' unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) *
    tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun g => (fun y => y * g) '' V₀) fun g _ => by
    have := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hV₀
    rw [Homeomorph.coe_mulRight] at this
    simpa only [one_mul] using this
  refine ⟨c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)), ?_⟩
  rintro φ ρ x R ⟨hρ, b, hb, kk, hkk, hx⟩ hsieg hR1 hR
  obtain ⟨m₀, hmC₀, hm₀⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = s.card * m₀ := ⟨_, rfl⟩
  have hm : ∀ z : normOneGL K n,
      {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
    intro z
    have := encard_le_of_subset_mul s hs hm₀ z
    rw [hmdef]
    exact_mod_cast this
  have hmC : (m : ℝ) ≤ s.card * Cc * R ^ N := by
    rw [hmdef, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC₀ (Nat.cast_nonneg _)
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hgR : C₁' * gain ≤ R₁ := mul_le_mul_of_nonneg_left hgain hC₁'0
  have hg0 : 0 ≤ C₁' * gain := mul_nonneg hC₁'0 hgain0
  set b₀ := c' * ((C₁' * gain) ^ k * R₁)
  have hb₀ : 0 ≤ b₀ := mul_nonneg hc'0 (mul_nonneg (pow_nonneg hg0 _) (hg0.trans hgR))
  have hfinal : ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ b₀ * √(μ.real Q * m) * ‖φ‖ := by
    refine sub_ct_le_of_altSum_inf (r := r) μ f φ hM x ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hxu : x⁻¹ * unipOne K n r z * x = finOne K n (u : AdelicGLn.integralFiniteGL K n) := by
        refine Subtype.ext ?_
        change (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL z * (x : AdelicGLn.AdelicGL K n) =
          finEmb K n _
        rw [hx]
        exact hu
      rw [hxu, ← map_inv]
      exact hUf _ (U.inv_mem u.2) w
    · intro y hy
      set Y : Fin (k + 1) → ArchMatrix K n :=
        fun i => conjArch K n (x : AdelicGLn.AdelicGL K n) (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
        intro i
        have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)
        have h2 : Y i = archMat K n ((((b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) *
            kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            blockEntry (truncInf (y i)) * ((b * diagUnits n (fun i => posIdele (K := K) (ρ i)
              (hρ i)) * kk : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
          simp only [Y, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYR : ∀ i, ‖Y i‖ ≤ R₁ := fun i => (hYn i).trans hgR
      have hex : ∀ ε : Fin (k + 1) → Bool, ∃ C : ArchUnits K n,
          archProj K n C = x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x ∧
            (C : ArchMatrix K n) = 1 + altPoint Y ε := by
        intro ε
        obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq_conj x (truncInf (altPoint y ε)) fun p => rfl
        refine ⟨C, hC1, ?_⟩
        rw [hC2, ← truncInfHom_apply, map_altPoint (truncInfHom n r),
          map_altPoint (conjArch K n (x : AdelicGLn.AdelicGL K n))]
        rfl
      choose Cε hCε1 hCε2 using hex
      have hsum : altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0 =
          ∑ ε, (altSign ε : ℂ) * rconv (rationalGLOne K n) μ f φ (x * archProj K n (Cε ε)) := by
        rw [altSum_eq_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [zero_add, hCε1 ε, zsmul_eq_mul]
        have : x * (x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x) =
            unipOne K n r (truncInf (altPoint y ε)) * x := by group
        rw [this]
      rw [hsum]
      have hb' : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (Cε ε))⁻¹ * w)‖ ≤ b₀ := by
        intro w
        refine (hc Y hYY hYR Cε hCε2 w).trans ?_
        have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ (k + 1) := by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
        have hprod' : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k * R₁ := by
          refine hprod.trans ?_
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hgR (pow_nonneg hg0 _)
        calc c * ∏ i, ‖Y i‖ ≤ c' * ∏ i, ‖Y i‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ b₀ := mul_le_mul_of_nonneg_left hprod' hc'0
      have hmem : ∀ ε, Cε ε ∈ unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) := fun ε =>
        mem_unipBall_of_val_eq hYY hYR (hCε2 ε)
      have hsq := enorm_sum_altSign_rconv_sq_le μ f φ x h𝒞 Cε hmem hb' hm
      have hA : ENNReal.ofReal b₀ ^ 2 * μ Q * (m : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hQ.measure_lt_top.ne) (by simp)
      have hle := norm_le_of_enorm_sq_le hA (by rw [mul_assoc]; exact hsq)
      refine hle.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb₀,
        ENNReal.toReal_natCast, Real.sqrt_mul (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hb₀, measureReal_def, mul_assoc, Real.sqrt_mul ENNReal.toReal_nonneg]
  refine hfinal.trans ?_
  have hμQ : 0 ≤ μ.real Q := measureReal_nonneg
  have hRN : 1 ≤ R ^ N := one_le_pow₀ hR1
  have hm' : (m : ℝ) ≤ s.card * max Cc 0 * R ^ N :=
    hmC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg _)) (pow_nonneg (by linarith) _))
  have hsqrt : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * √(R ^ N) := by
    rw [← Real.sqrt_mul (mul_nonneg hμQ (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' hμQ
  have hsR : √(R ^ N) ≤ R ^ N := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsqrt' : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * R ^ N :=
    hsqrt.trans (mul_le_mul_of_nonneg_left hsR (Real.sqrt_nonneg _))
  calc b₀ * √(μ.real Q * m) * ‖φ‖
      ≤ b₀ * (√(μ.real Q * (s.card * max Cc 0)) * R ^ N) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt' hb₀) (norm_nonneg _)
    _ = c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)) * gain ^ k * R ^ N * ‖φ‖ := by
        simp only [b₀, mul_pow]
        ring
end

