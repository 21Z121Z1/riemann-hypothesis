import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Mathlib

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatArch
section
noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEst.LatArchPf

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mul_realAd {u : AF F} (hu : evI F u = 0) (t : ℝ) : u * realAd F t = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem emb_realAd (hF : IsTotallyReal F) (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = t := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) with ha
  have h1 : InfiniteAdeleRing.ringEquiv_mixedSpace F a = algebraMap ℝ _ t := by
    rw [ha, RingEquiv.apply_symm_apply]
  have h2 := congrFun (congrArg Prod.fst h1) ⟨w, hw⟩
  have h3 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w) = t := h2
  change InfinitePlace.Completion.extensionEmbedding w (a w) = t
  rw [← h3]
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw (a w)).symm

theorem piInf_alg {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]

theorem piInf_rId (hF : IsTotallyReal F) {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  rw [piInf_alg, rId, map_add, map_add, map_one, map_one, emb_realAd hF]
  push_cast
  ring

theorem sz_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z := by
  unfold sz
  positivity

theorem sz_mul_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (M : ℝ) (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ M) :
    sz τ (y * Bᵀ) ≤ d * M * sz τ y := by
  unfold sz
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ∀ j, ‖piInf (τ w) ((y * Bᵀ) i j)‖ ≤ M * ∑ k, ‖piInf (τ w) (y i k)‖ := fun j => by
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [map_mul, norm_mul, Matrix.transpose_apply, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB w j k) (norm_nonneg _)
  refine (Finset.sum_le_sum fun j _ => h j).trans ?_
  simp [mul_assoc]

theorem incM_mul {n : ℕ} (x y : Matrix (Fin n) (Fin n) E) : incM F (x * y) = incM F x * incM F y :=
  Matrix.map_mul

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem torus (hb : FrameBasis) (hc : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ}
    {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J) (fr : Frame σ J) (hg : fr.IsGood) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Cone fr.r, At (evI F) (mat (fr.a t) - 1) ∧
      ∀ w i j, ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤ K * Real.exp (∑ j, t j) := by
  obtain ⟨b, lam, ix, iy, -, h2, h3, -, h5⟩ := hb F E σ hc d J hJ fr hg
  set P := incM F b.1 with hP
  set Q := incM F (b⁻¹).1 with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← incM_mul, Units.mul_inv, incM_one]
  refine ⟨∑ w, ∑ i, ∑ j, ∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖, by positivity, fun t ht => ?_⟩
  set D : Matrix (Fin d) (Fin d) (AE F E) :=
    Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t)) with hD
  have hB : mat (fr.a t) = P * D * Q := by
    rw [← h5 t, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hlam : ∀ k, lam k t ≤ ∑ j, t j := fun k => by
    have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
    by_cases hk : ∀ i, ix i ≠ k ∧ iy i ≠ k
    · rw [h3 k hk]
      exact h0
    · obtain ⟨i, hi⟩ := not_forall.1 hk
      rcases not_and_or.1 hi with e | e
      · rw [← not_not.1 e, (h2 i t).1]
        exact Finset.single_le_sum (fun j _ => ht.2 j) (Finset.mem_univ i)
      · rw [← not_not.1 e, (h2 i t).2]
        exact (neg_nonpos.2 (ht.2 i)).trans h0
  refine ⟨fun u hu => ?_, fun w i j => ?_⟩
  · have hu' : u • (D - 1) = 0 := by
      ext k l
      by_cases e : k = l
      · subst e
        simp only [hD, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
          Matrix.zero_apply, rId, map_add, map_one, add_sub_cancel_left]
        rw [Algebra.smul_def, ← map_mul, mul_realAd hu, map_zero]
      · simp [hD, Matrix.diagonal_apply_ne _ e, Matrix.one_apply_ne e]
    have e : mat (fr.a t) - 1 = P * (D - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, hB]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.mul_zero, Matrix.zero_mul]
  · have h1 : ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤
        (∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) * Real.exp (∑ j, t j) := by
      rw [hB, Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [hD, Matrix.mul_diagonal, map_mul, map_mul, piInf_rId hc.1, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_right_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hlam k)) (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem maj_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (K s : ℝ) (hK : 0 ≤ K) (hs : 1 ≤ s) (h1 : At (evI F) (B - 1))
    (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ K * s) :
    maj τ C N y ≤ ((1 + d * K) * s) ^ N * maj τ C N (y * Bᵀ) := by
  have hy := sz_nonneg τ y
  have hz := sz_nonneg τ (y * Bᵀ)
  have hs0 : 0 < s := by linarith
  unfold maj
  split_ifs with h2 h3 h3
  · have h4 := sz_mul_le τ y B _ hB
    have h5 : 1 + sz τ (y * Bᵀ) ≤ (1 + d * K) * s * (1 + sz τ y) := by
      have : 0 ≤ d * K * s := by positivity
      have : 0 ≤ s * sz τ y := by positivity
      nlinarith
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h5 N
  · refine absurd ?_ h3
    obtain ⟨c, hc, h⟩ := h2
    refine ⟨c, hc, fun u hu => ?_⟩
    have e : y * Bᵀ - c = (y - c) + y * (B - 1)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.transpose_one, Matrix.mul_one]
      abel
    rw [e, smul_add, h u hu, zero_add, ← Matrix.mul_smul, ← Matrix.transpose_smul, h1 u hu, Matrix.transpose_zero,
      Matrix.mul_zero]
  · positivity
  · simp

end PositivityTheory.ThKEst.LatArchPf

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK LatArchPf

theorem latArch_of (hb : FrameBasis) : LatArch := by
  intro F E _ _ _ _ _ σ hc τ n d J J' _ hJ' fr hg C N hC
  obtain ⟨K, hK, h⟩ := torus hb hc τ hJ' fr hg
  refine ⟨C, Real.toNNReal ((1 + d * K) ^ N), hC, fun S g t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
  have h3 := maj_le τ C N (mat g⁻¹ * incM F x.1 * (mat (fr.a t)⁻¹)ᵀ) (mat (fr.a t)) K _ hK (Real.one_le_exp h0) h1 h2
  have e : mat (fr.a t) * mat (fr.a t)⁻¹ = mat (1 : UA σ J')⁻¹ := by
    rw [inv_one, ← mul_inv_cancel (fr.a t)]
    rfl
  rw [Matrix.mul_assoc _ _ (mat (fr.a t))ᵀ, ← Matrix.transpose_mul, e] at h3
  change _ ≤ ENNReal.ofReal ((1 + d * K) ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h3.trans_eq ?_)
  rw [mul_pow, Real.exp_nat_mul]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatCpt
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientCompactness

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem topRing : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change infEmb τ (compInf F E w (a ⊗ₜ[F] (1 : E))) = _
    change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
    rw [infEmb_tmul, map_one, mul_one]
    rfl
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

theorem continuous_sz {n d : ℕ} : Continuous (sz τ : Ten F E n d → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_piInf (τ w)).comp ((continuous_apply j).comp (continuous_apply i))).norm

theorem sz_nonneg {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem entry_le_sz {n d : ℕ} (z : Ten F E n d) (w : InfinitePlace F) (i : Fin n) (j : Fin d) :
    ‖piInf (τ w) (z i j)‖ ≤ sz τ z := by
  unfold sz
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖piInf (τ w) (z i j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem sz_mul_mul_le {n d : ℕ} (A : Ten F E n n) (B : Ten F E d d) (z : Ten F E n d) :
    sz τ (A * z * Bᵀ : Ten F E n d) ≤ (n * d * (sz τ A * sz τ B)) * sz τ z := by
  have hA := sz_nonneg τ A
  have hB := sz_nonneg τ B
  have key : ∀ w i j, ‖piInf (τ w) ((A * z * Bᵀ : Ten F E n d) i j)‖ ≤
      (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ := by
    intro w i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := entry_le_sz τ A w i k
    have h2 := entry_le_sz τ B w j l
    calc _ ≤ sz τ A * ‖piInf (τ w) (z k l)‖ * sz τ B := by gcongr
      _ = _ := by ring
  calc sz τ (A * z * Bᵀ : Ten F E n d)
      ≤ ∑ w, ∑ _i : Fin n, ∑ _j : Fin d, (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key w i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show sz τ z = ∑ w, ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

theorem maj_nonneg {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) : 0 ≤ maj τ C N z := by
  have := sz_nonneg τ z
  unfold maj
  split_ifs
  · positivity
  · exact le_rfl

theorem maj_le {n d : ℕ} (C C' : Set (Ten F E n d)) (N : ℕ) (A : Ten F E n n) (B : Ten F E d d) (K : ℝ) (hK : 1 ≤ K)
    (hAB : n * d * (sz τ A * sz τ B) ≤ K) (hC : ∀ c ∈ C, (A * c * Bᵀ : Ten F E n d) ∈ C') (z : Ten F E n d) :
    maj τ C N z ≤ K ^ N * maj τ C' N (A * z * Bᵀ : Ten F E n d) := by
  by_cases h : ∃ c ∈ C, At (evI F) (z - c)
  · have h' : ∃ c ∈ C', At (evI F) ((A * z * Bᵀ : Ten F E n d) - c) := by
      obtain ⟨c, hc, hz⟩ := h
      refine ⟨_, hC c hc, fun u hu => ?_⟩
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu, Matrix.mul_zero,
        Matrix.zero_mul]
    unfold maj
    rw [if_pos h, if_pos h']
    have h0 := sz_nonneg τ z
    have h1 := sz_nonneg τ (A * z * Bᵀ : Ten F E n d)
    have h2 : 1 + sz τ (A * z * Bᵀ : Ten F E n d) ≤ K * (1 + sz τ z) := by
      have := (sz_mul_mul_le τ A B z).trans (mul_le_mul_of_nonneg_right hAB h0)
      linarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 N
  · have := maj_nonneg τ C' N (A * z * Bᵀ : Ten F E n d)
    rw [maj, if_neg h]
    positivity

theorem continuous_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g :=
  Units.continuous_val.comp continuous_subtype_val

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g κ : UA σ J) : mat κ * mat (g * κ)⁻¹ = mat g⁻¹ := by
  rw [← mat_mul, mul_inv_rev, mul_inv_cancel_left]

end LatticeQuotientCompactness

open LatticeQuotientCompactness in

theorem latCpt_of : LatCpt := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ Ω Ω' hΩ hΩ' C N hC
  have := topRing (F := F) (E := E)
  obtain ⟨M, hM⟩ := (hΩ.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  obtain ⟨M', hM'⟩ := (hΩ'.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  let K : ℝ := max 1 (n * d * (M * M'))
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K ^ N := by positivity
  let f : UA σ J × Ten F E n d × UA σ J' → Ten F E n d := fun p => mat p.1 * p.2.1 * (mat p.2.2)ᵀ
  have hf : Continuous f :=
    ((continuous_mat.comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_mat.comp (continuous_snd.comp continuous_snd)).matrix_transpose
  refine ⟨f '' (Ω ×ˢ C ×ˢ Ω'), ⟨K ^ N, hK0⟩, (hΩ.prod (hC.prod hΩ')).image hf, fun S g h κ hκ κ' hκ' => ?_⟩
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have a1 : sz τ (mat κ) ≤ M := hM ⟨κ, hκ, rfl⟩
  have a2 : sz τ (mat κ') ≤ M' := hM' ⟨κ', hκ', rfl⟩
  have b1 := sz_nonneg τ (mat κ)
  have b2 := sz_nonneg τ (mat κ')
  have hAB : n * d * (sz τ (mat κ) * sz τ (mat κ')) ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ M := b1.trans a1
    gcongr
  have key := maj_le τ C (f '' (Ω ×ˢ C ×ˢ Ω')) N (mat κ) (mat κ') K hK hAB
    (fun c hc => ⟨(κ, c, κ'), ⟨hκ, hc, hκ'⟩, rfl⟩) (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ)
  have e : mat κ * (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ) * (mat κ')ᵀ =
      mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ := by
    rw [← mat_mul_inv g κ, ← mat_mul_inv h κ', Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at key
  refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_eq_coe_nnreal hK0]
  rfl

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientMeasure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def e0 : AF F := ((0 : Ainf F), (1 : Af F))

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evI F) z ↔ e0 F • z = 0 := by
  constructor
  · intro h
    apply h
    show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  · intro h u hu
    have hu1 : u.1 = 0 := by
      have hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)
    have hue : u = u * e0 F := by
      refine Prod.ext ?_ ?_
      · show u.1 = u.1 * (0 : Ainf F)
        rw [hu1, zero_mul]
      · show u.2 = u.2 * (1 : Af F)
        rw [mul_one]
    rw [hue, mul_smul, h, smul_zero]

variable (F) in
theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  haveI : T2Space (NumberField.InfiniteAdeleRing F) :=
    show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance
  show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  infer_instance

variable (F E) in
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI := t2Space_adeleRing_of_numberField F
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)

variable (F E) in
theorem ring_AE : IsTopologicalRing (AE F E) := by
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

omit [NumberField E] in
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  let φ : AF F →+* ℂ := (NumberField.InfinitePlace.Completion.extensionEmbedding w).comp
    (GlobalTheory.AdelicU.evInf F w).toRingHom
  have hφ : Continuous φ :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  letI : Module (AF F) ℂ := Module.compHom ℂ φ
  haveI : ContinuousSMul (AF F) ℂ := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  have hpt : ∀ (b : AF F) (e : E), piInf τ (b ⊗ₜ[F] e) = φ b * (τ.1 e) := fun b e => rfl
  let Lm : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b e =>
          rw [TensorProduct.smul_tmul', hpt, hpt, smul_eq_mul, map_mul]
          show φ a * φ b * τ.1 e = φ a * (φ b * τ.1 e)
          ring
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add, smul_add] }
  exact IsModuleTopology.continuous_of_linearMap Lm

variable {n d : ℕ}

theorem continuous_sz (τ : ∀ w : InfinitePlace F, EmbOver E w) : Continuous (sz τ : Ten F E n d → ℝ) := by
  exact continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm

theorem isClosed_supp {C : Set (Ten F E n d)} (hC : IsCompact C) :
    IsClosed {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} := by
  haveI := t2Space_cm_host_adeles F E
  have hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} =
      (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]
    constructor
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
  rw [hset]
  exact (hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))

theorem measurable_maj {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {C : Set (Ten F E n d)} (hC : IsCompact C) (N : ℕ)
    {f : G → Ten F E n d} (hf : Continuous f) : Measurable fun g => maj τ C N (f g) := by
  have hcl := isClosed_supp (F := F) (E := E) (n := n) (d := d) hC
  delta maj
  refine Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const
  exact ((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv

omit [NumberField E] in
theorem continuous_mat_inv {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g⁻¹ := by
  exact Units.continuous_coe_inv.comp continuous_subtype_val

end LatticeQuotientMeasure

open LatticeQuotientMeasure in

theorem latMeas : LatMeas := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h
  haveI := ring_AE F E
  haveI := t2Space_cm_host_adeles F E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩
  delta latSum
  refine Measurable.ennreal_tsum fun x => ENNReal.measurable_ofReal.comp ?_
  exact measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)

theorem latMeas_of : GrpTop → LatMeas := by
  exact fun _ => latMeas

end PositivityTheory.ThKEst

end
end

