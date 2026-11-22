import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0001

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatTor
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_pos_lam {n d q y : ℕ} {lam : Fin n → (Fin q → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin q ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    {lam' : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1' : ∀ i j, jx i ≠ jy j)
    (h2' : ∀ i t, lam' (jx i) t = t i ∧ lam' (jy i) t = -t i) (h3' : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam' k = 0)
    {s : Fin q → ℝ} {t : Fin y → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone y) :
    ∑ k, ∑ l, max 0 (lam k s + lam' l t) = posWt n d s t := by
  let G : ℝ → ℝ := fun u => ∑ l, max 0 (u + lam' l t)
  have hG : ∀ u, G u = ∑ j, max 0 (u + t j) + ∑ j, max 0 (u + -t j) + ((d : ℝ) - 2 * y) * max 0 (u + 0) := fun u =>
    sum_lam h1' h2' h3' (fun v => max 0 (u + v)) t
  have h0 : G 0 = ∑ j, t j := by
    rw [hG]
    have a : ∀ j, max 0 (0 + t j) = t j := fun j => by rw [zero_add, max_eq_right (ht.2 j)]
    have b : ∀ j, max 0 (0 + -t j) = 0 := fun j => by rw [zero_add, max_eq_left (by linarith [ht.2 j])]
    simp only [a, b]
    simp
  have hs' : ∀ i, G (s i) + G (-s i) = ∑ j, 2 * max (s i) (t j) + ((d : ℝ) - 2 * y) * s i := by
    intro i
    have a : ∀ j, 2 * max (s i) (t j) =
        max 0 (s i + t j) + max 0 (s i + -t j) + (max 0 (-s i + t j) + max 0 (-s i + -t j)) := by
      intro j
      have := hs.2 i
      have := ht.2 j
      simp only [max_def]
      split_ifs <;> linarith
    rw [hG, hG, add_zero, add_zero, max_eq_right (hs.2 i), max_eq_left (by linarith [hs.2 i] : -s i ≤ 0)]
    simp only [a, Finset.sum_add_distrib]
    ring
  have := sum_lam h1 h2 h3 G s
  rw [← Finset.sum_add_distrib, h0] at this
  simp only [hs', Finset.sum_add_distrib, ← Finset.mul_sum] at this
  refine this.trans ?_
  simp only [posWt, ← Finset.mul_sum]

theorem tsum_fin_prod {α : Type} (q : ℕ) (φ : Fin q → α → ℝ≥0∞) :
    ∑' x : Fin q → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← (Fin.consEquiv fun _ : Fin (q + 1) => α).tsum_eq, ENNReal.tsum_prod', Fin.prod_univ_succ, ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [Fin.prod_univ_succ]
    rfl

theorem tsum_fun_prod {ι α : Type} [Fintype ι] (φ : ι → α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.prod_comp, ← tsum_fin_prod, ← (e.arrowCongr (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← e.prod_comp]
  simp

def oneMaj (τ : ∀ w : InfinitePlace F, EmbOver E w) (m N : ℕ) (ν : ℝ) : E → ℝ≥0∞ :=
  Set.indicator {x | IsIntegral ℤ ((m : E) * x)} fun x =>
    ENNReal.ofReal (((1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x‖) ^ N)⁻¹)

theorem tsum_oneMaj (hO : OneVar) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ≥0, ∀ ν, ∑' x, oneMaj τ m (Module.finrank ℚ E + 1) ν x ≤
      K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν)) := by
  classical
  obtain ⟨K, hK⟩ := hO (mixedEmbedding.mixedSpace E) (mixedEmbedding.integerLattice E) (Module.finrank ℚ E + 1)
    (by rw [mixedEmbedding.finrank]; omega)
  rw [mixedEmbedding.finrank] at hK
  set N := Module.finrank ℚ E + 1
  refine ⟨(m : ℝ≥0) ^ N * K, fun ν => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let i : {x : E | IsIntegral ℤ ((m : E) * x)} → mixedEmbedding.integerLattice E := fun x =>
    ⟨mixedEmbedding E (m * x.1), ⟨⟨_, x.2⟩, rfl⟩⟩
  have hi : Function.Injective i := fun x y hxy => by
    have := (mixedEmbedding E).injective (congrArg Subtype.val hxy)
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hm.ne') this)
  have hn : ∀ x : E, ‖mixedEmbedding E x‖ ≤ ∑ w, ‖(τ w).1 x‖ := by
    intro x
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun v _ => ?_
    obtain ⟨w, hw⟩ := norm_emb h τ v.embedding
    rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq, hw]
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  rw [oneMaj, ← tsum_subtype]
  calc _ ≤ ∑' x : {x : E | IsIntegral ℤ ((m : E) * x)}, ((m : ℝ≥0) ^ N : ℝ≥0) *
          ENNReal.ofReal (((1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖) ^ N)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : 0 ≤ ∑ w, ‖(τ w).1 x.1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h1 : ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤ m * ∑ w, ‖(τ w).1 x.1‖ := by
          refine (hn _).trans (le_of_eq ?_)
          simp [Finset.mul_sum]
        have h2 : 1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤
            m * (1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x.1‖) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-ν)).le
          linarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 N
        rw [mul_pow] at h3
        push_cast
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        exact h3.trans_eq (mul_comm _ _)
    _ ≤ ((m : ℝ≥0) ^ N : ℝ≥0) * (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi _).trans (hK ν)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

theorem latTor_of : FrameBasis → OneVar → LatTor := by
  intro hB hO F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  set N₀ := Module.finrank ℚ E + 1 with hN₀
  set c := Fintype.card (Fin n × Fin d) with hc
  refine ⟨N₀ * c, fun C hC => ?_⟩
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  obtain ⟨K₁, hK₁⟩ := tsum_oneMaj hO hσ τ hm
  refine ⟨K.toNNReal ^ (N₀ * c) * K₁ ^ c, fun s hs t ht => ?_⟩
  let i : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → (Fin n × Fin d → E) := fun x p =>
    ((b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ) p.1 p.2
  have hi : Function.Injective i := fun x y hxy => by
    have e : (b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ = (b⁻¹).1 * y.1 * (b'⁻¹).1ᵀ := by
      ext k l
      exact congrFun hxy (k, l)
    have e' : ∀ z : Matrix (Fin n) (Fin d) E, b.1 * ((b⁻¹).1 * z * (b'⁻¹).1ᵀ) * b'.1ᵀ = z := by
      intro z
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
    exact Subtype.ext (by rw [← e' x.1, e, e'])
  let g : (Fin n × Fin d → E) → ℝ≥0∞ := fun ξ => ∏ p, oneMaj τ m N₀ (lam p.1 s + lam' p.2 t) (ξ p)
  calc _ ≤ ∑' x, (K.toNNReal ^ (N₀ * c) : ℝ≥0) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        obtain ⟨ha, hb⟩ := h s t x.1
        unfold maj
        split_ifs with hx
        swap
        · simp
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        set z := sz τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        let A : Fin n × Fin d → ℝ := fun p => Real.exp (-(lam p.1 s + lam' p.2 t)) * ∑ w, ‖(τ w).1 (i x p)‖
        have hA0 : ∀ p, 0 ≤ A p := fun p => by positivity
        have hA : ∀ p, 1 + A p ≤ K * (1 + z) := fun p => by
          have : ∑ p, A p ≤ K * z := by
            refine le_trans (le_of_eq ?_) hb
            rw [Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            exact Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _
          have h4 := Finset.single_le_sum (f := A) (fun p _ => hA0 p) (Finset.mem_univ p)
          linarith
        have hg : g (i x) = ENNReal.ofReal (∏ p, (1 + A p) ^ N₀)⁻¹ := by
          rw [← Finset.prod_inv_distrib, ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hA0 p; positivity]
          exact Finset.prod_congr rfl fun p _ =>
            Set.indicator_of_mem (s := {x | IsIntegral ℤ ((m : E) * x)}) (a := i x p) (ha hx p.1 p.2) _
        have h5 : ∏ p, (1 + A p) ^ N₀ ≤ (K * (1 + z)) ^ (N₀ * c) := by
          rw [pow_mul, hc, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod (fun p _ => by have := hA0 p; positivity)
            fun p _ => pow_le_pow_left₀ (by have := hA0 p; positivity) (hA p) _
        have h6 : 0 < ∏ p, (1 + A p) ^ N₀ := Finset.prod_pos fun p _ => by have := hA0 p; positivity
        rw [hg, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        rw [Real.coe_toNNReal _ (by linarith), ← div_eq_mul_inv, le_div_iff₀ h6, inv_mul_le_iff₀ (by positivity),
          ← mul_pow]
        exact h5.trans_eq (by rw [mul_comm K])
    _ ≤ (K.toNNReal ^ (N₀ * c) : ℝ≥0) * ∏ p : Fin n × Fin d, (K₁ * ENNReal.ofReal
          (Real.exp (Module.finrank ℚ E * max 0 (lam p.1 s + lam' p.2 t)))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        refine (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans ?_
        rw [tsum_fun_prod]
        exact Finset.prod_le_prod' fun p _ => hK₁ _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hc,
          ← ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum,
          Fintype.sum_prod_type, sum_pos_lam h1 h2 h3 h1' h2' h3' hs ht]
        push_cast
        rw [mul_assoc]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt
section
noncomputable section

namespace PositivityTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem realAd_snd (t : ℝ) : (realAd F t).2 = 0 := rfl

theorem realAd_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((realAd F t).1 w) = t := by
  have hw := IsTotallyReal.isReal w
  have e := congrArg (fun z => z.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t))
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact congrArg _ e

theorem rId_snd (t : ℝ) : (rId F t).2 = 1 := add_zero _

theorem rId_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = Real.exp t := by
  change InfinitePlace.Completion.extensionEmbedding w (1 + (realAd F (Real.exp t - 1)).1 w) = _
  rw [map_add, map_one, realAd_inf]
  push_cast
  ring

theorem rId_add [IsTotallyReal F] (s t : ℝ) : rId F (s + t) = rId F s * rId F t := by
  refine Prod.ext (funext fun w => (InfinitePlace.Completion.extensionEmbedding w).injective ?_) ?_
  · change _ = InfinitePlace.Completion.extensionEmbedding w ((rId F s).1 w * (rId F t).1 w)
    rw [map_mul, rId_inf, rId_inf, rId_inf, Real.exp_add, Complex.ofReal_mul]
  · change _ = (rId F s).2 * (rId F t).2
    rw [rId_snd, rId_snd, rId_snd, mul_one]

theorem rId_zero' : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

theorem continuous_rId [IsTotallyReal F] : Continuous (rId F) := by
  refine Continuous.prodMk (f := fun t => (rId F t).1) (g := fun t => (rId F t).2) (continuous_pi fun w => ?_) ?_
  · refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.continuous_iff.2 ?_
    have : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (rId F t).1 w) = fun t => (Real.exp t : ℂ) :=
      funext fun t => rId_inf w t
    rw [this]
    fun_prop
  · simp only [rId_snd]
    exact continuous_const

variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

omit [NumberField F] [NumberField E] in
theorem yx_eq_one (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  have cc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => hs _
  have cJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

omit [NumberField F] [NumberField E] in
theorem two_mul_le_of_wittFrame (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : 2 * r ≤ n := by
  have e : Matrix.fromRows (cT (σ : E →+* E) Y * J) (cT (σ : E →+* E) X * J) * Matrix.fromCols X Y = 1 := by
    rw [Matrix.fromRows_mul_fromCols, yx_eq_one hs hJ hW, hW.xx, hW.yy, hW.xy, Matrix.fromBlocks_one]
  have e2 := congrArg Matrix.rank e
  rw [Matrix.rank_one, Fintype.card_sum, Fintype.card_fin] at e2
  have := (Matrix.rank_mul_le_right _ _).trans' e2.symm.le |>.trans (Matrix.rank_le_card_height _)
  rw [Fintype.card_fin] at this
  omega

omit [NumberField F] [NumberField E] in

theorem ext_of_frame (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {A : Type} [CommRing A]
    (φ : E →+* A) {m m' : Matrix (Fin n) (Fin n) A} (h1 : m * X.map φ = m' * X.map φ) (h2 : m * Y.map φ = m' * Y.map φ)
    (h3 : ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      m *ᵥ (fun i => φ (z i)) = m' *ᵥ fun i => φ (z i)) : m = m' := by
  set P : Matrix (Fin n) (Fin n) E := 1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J) with hP
  have p1 : cT (σ : E →+* E) X * J * P = 0 := by
    simp only [hP, Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]
    simp
  have p2 : cT (σ : E →+* E) Y * J * P = 0 := by
    simp only [hP, Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx_eq_one hs hJ hW]
    simp
  have h4 : m * P.map φ = m' * P.map φ := Matrix.ext fun i j =>
    congrFun (h3 (fun k => P k j) (funext fun k => congrFun (congrFun p1 k) j)
      (funext fun k => congrFun (congrFun p2 k) j)) i
  have e : (1 : Matrix (Fin n) (Fin n) A) =
      P.map φ + X.map φ * (cT (σ : E →+* E) Y * J).map φ + Y.map φ * (cT (σ : E →+* E) X * J).map φ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add φ), ← Matrix.map_add _ (map_add φ), hP,
      ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    congr 1
    abel
  rw [← Matrix.mul_one m, ← Matrix.mul_one m', e]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, h1, h2, h4]

theorem isTorusElt_unique (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ}
    {a a' : GAd σ J} (ha : IsTorusElt σ J X Y t a) (ha' : IsTorusElt σ J X Y t a') : a = a' := by
  refine GAd_ext σ J (fun w => ?_) fun v => by
    rw [mem_infPts_iff_forall.1 ha.1 v, mem_infPts_iff_forall.1 ha'.1 v]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  apply (archEquiv J h τ).injective
  refine Subtype.ext (Units.ext ?_)
  rw [← archMat_eq_archEquiv J h, ← archMat_eq_archEquiv J h]
  exact ext_of_frame (sigma_sigma h) hJ hW τ.1 ((ha.2 w τ).1.trans (ha'.2 w τ).1.symm)
    ((ha.2 w τ).2.1.trans (ha'.2 w τ).2.1.symm) fun z h1 h2 =>
      ((ha.2 w τ).2.2 z h1 h2).trans ((ha'.2 w τ).2.2 z h1 h2).symm

theorem le_height_of_isTorusElt (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ} {a : GAd σ J}
    (ha : IsTorusElt σ J X Y t a) (i : Fin r) : t i ≤ height σ J a := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set M := archMat σ J τ (projArch σ J w a) with hM
  have h1 : opNorm M ≤ height σ J a :=
    ((normInf_le_iff F w).1 (le_htOf (normInf F w) (matHom _ σ J (projArch σ J w a))) τ).trans (htInf_le_height σ J w a)
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun k => τ.1 (X k i)
  have hv : v ≠ 0 := fun e => by
    have hx : ∀ k, X k i = 0 := fun k => τ.1.injective ((congrArg (fun z : EuclideanSpace ℂ (Fin n) => z k) e).trans
      (map_zero _).symm)
    have := congrFun (congrFun hW.xy i) i
    simp [Matrix.mul_apply, cT, hx] at this
  have h2 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M v = (t i : ℂ) • v := by
    ext k
    have := congrFun (congrFun (ha.2 w τ).1 k) i
    rw [mul_diagonal, mul_comm] at this
    exact this
  have h3 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M).le_opNorm v
  rw [h2, norm_smul, Complex.norm_real] at h3
  have h4 := le_of_mul_le_mul_right h3 (norm_pos_iff.2 hv)
  exact (le_abs_self _).trans (h4.trans (show ((opNorm M : ℝ≥0) : ℝ) ≤ _ from h1))

theorem exists_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a : (Fin r → ℝ) → GAd σ J, (∀ s t, a (s + t) = a s * a t) ∧ Continuous a ∧
      (∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)) ∧ ∀ t,
      (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))) ∧
      (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))) ∧
      ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z := by
  have := h.1
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let ι := algebraMap (AF F) (AE F E)
  let d : ℝ → (AE F E)ˣ := fun x => ⟨ι (rId F x), ι (rId F (-x)),
    by rw [← map_mul, ← rId_add, add_neg_cancel, rId_zero', map_one],
    by rw [← map_mul, ← rId_add, neg_add_cancel, rId_zero', map_one]⟩
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
      adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c1]; simp only [adMat, JR, Matrix.map_mul]
  have key := fun t : Fin r → ℝ => exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X)
    (Y := adMat F Y)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    ((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))
    ((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) (fun i => d (t i))
    (fun i => congrArg (rId F (t i) ⊗ₜ[F] ·) (map_one σ))
  choose m hm hX hY he using key
  have hZ : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (m t).1 *ᵥ incV F z = incV F z := fun t z hz hz' => by
    have h4 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (σ : E →+* E) Z * J) *ᵥ z = 0 →
        (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ incV F z = 0 :=
      fun Z hZ => funext fun i => by
        have e : (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) =
          (cT (σ : E →+* E) Z * J).map (inclR (F := F) (AF F)) := by
          rw [c1, Matrix.map_mul]; rfl
        rw [e]
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ z i).symm.trans (by rw [hZ]; exact map_zero _)
    rw [he, add_mulVec, add_mulVec, ← mulVec_mulVec, h4 Y hz', mulVec_zero, ← mulVec_mulVec, h4 X hz]
    simp
  have hadd : ∀ s t, m (s + t) = m s * m t := fun s t => by
    refine Units.ext (ext_of_frame (sigma_sigma h) hJ hW (inclR (F := F) (AF F)) ?_ ?_ fun z h1 h2 => ?_)
    · rw [Units.val_mul, Matrix.mul_assoc, hX, hX, ← Matrix.mul_assoc, hX, Matrix.mul_assoc, diagonal_mul_diagonal]
      exact congrArg (_ * diagonal ·) (funext fun i => (congrArg ι (rId_add _ _)).trans (map_mul ι _ _))
    · rw [Units.val_mul, Matrix.mul_assoc, hY, hY, ← Matrix.mul_assoc, hY, Matrix.mul_assoc, diagonal_mul_diagonal]
      exact congrArg (_ * diagonal ·) (funext fun i => (congrArg ι ((congrArg (rId F) (neg_add _ _)).trans
        (rId_add _ _))).trans (map_mul ι _ _))
    · exact (hZ _ z h1 h2).trans (by
        rw [Units.val_mul, ← mulVec_mulVec]
        exact ((congrArg _ (hZ t z h1 h2)).trans (hZ s z h1 h2)).symm)
  have h0 : m 0 = 1 := by simpa using hadd 0 0
  have hinv : ∀ t, (m t)⁻¹ = m (-t) := fun t => inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hι : Continuous ι := continuous_algebraMap _ _
  have hc : Continuous fun t => (m t).1 := by
    simp only [he]
    refine Continuous.add (Continuous.add continuous_const (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const))
      (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const)
    · exact (hι.comp (continuous_rId.comp (continuous_apply i))).sub continuous_const
    · exact (hι.comp (continuous_rId.comp (continuous_apply i).neg)).sub continuous_const
  have hc' : Continuous m := Units.continuous_iff.2 ⟨hc, by simp only [hinv]; exact hc.comp continuous_neg⟩
  refine ⟨fun t => ⟨m t, hm t⟩, fun s t => Subtype.ext (hadd s t), hc'.subtype_mk _, fun t => ⟨?_, fun w τ => ?_⟩,
    fun t => ⟨hX t, hY t, hZ t⟩⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    let ψ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    have h1 : ∀ x, ψ (d x).1 = 1 := fun x => congrArg (· ⊗ₜ[F] (1 : E)) (rId_snd (F := F) x)
    have h2 : ∀ x, ψ (d x)⁻¹.1 = 1 := fun x => congrArg (· ⊗ₜ[F] (1 : E)) (rId_snd (F := F) (-x))
    change ψ ((m t).1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [he]
    simp only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add, map_sum, map_mul, map_sub, h1,
      h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ, map_zero]
  · let φ := (infEmb τ).comp (compInf F E w)
    have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
    have h1 : ∀ x : ℝ, φ (ι (rId F x)) = Real.exp x := fun x => by
      change infEmb τ ((rId F x).1 w ⊗ₜ[F] 1) = _
      rw [infEmb_tmul, map_one, mul_one, rId_inf]
    have h2 : ∀ Z : Matrix (Fin n) (Fin r) E, (adMat F Z).map φ = Z.map τ.1 := fun Z => Matrix.ext fun i j => h0 _
    have h3 : archMat σ J τ (projArch σ J w ⟨m t, hm t⟩) = (m t).1.map φ := rfl
    rw [h3]
    refine ⟨?_, ?_, fun z hz hz' => ?_⟩
    · rw [← h2, ← Matrix.map_mul, hX, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => h1 _)
    · rw [← h2, ← Matrix.map_mul, hY, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => (h1 (-t i)).trans (by rw [Real.exp_neg, Complex.ofReal_inv]))
    · funext i
      rw [show (fun i => τ.1 (z i)) = φ ∘ incV F z from funext fun i => (h0 _).symm,
        ← RingHom.map_mulVec, hZ t z hz hz']
      exact h0 _

end PositivityTheory.ThKEst.Sieg

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.UMGSmooth
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def umgComp (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (w : InfinitePlace F) :
    UA σ J →* Matrix (Fin d) (Fin d) ℂ :=
  (piInf (τ w)).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem umg_continuousMul {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : ContinuousMul (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  exact (Subgroup.instIsTopologicalGroupSubtypeMem _).toContinuousMul

theorem umg_cj_mem {d : ℕ} {W : Spc F E d} {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) (x : UA σ W.J) :
    UMGS.cj x γ ∈ Lines σ W := by
  have := umg_continuousMul (σ := σ) W.J
  refine ⟨((continuous_const.mul hγ.1).mul continuous_const).congr fun s => (UMGS.cj_apply x γ s).symm,
    fun t u hu => ?_⟩
  have h := hγ.2 t u hu
  have hm : ∀ a b : UA σ W.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have h1 : mat x⁻¹ * mat x = 1 := by rw [← hm, inv_mul_cancel]; rfl
  have e : mat (UMGS.cj x γ t) - 1 = mat x⁻¹ * (mat (γ t) - 1) * mat x := by
    rw [UMGS.cj_apply, hm, hm, mul_sub, sub_mul, mul_one, h1]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero, Matrix.zero_mul]

open scoped Matrix.Norms.Operator in
theorem umgSmooth_of (hL : LinDer) (hG : LineGen) : UMGSmooth := by
  intro F E _ _ _ _ _ σ hcm τ d W hW f hf k γ hγ g
  obtain ⟨r, β, c, hβ, hl⟩ := hL F E σ hcm τ d W hW
  obtain ⟨k₀, S, hfS, hS⟩ := hf
  have := umg_continuousMul (σ := σ) W.J
  have hGn : ∀ (δ : Multiplicative ℝ →* UA σ W.J) Y, UMGS.Gn (umgComp τ W.J) δ Y ↔ Gen τ W δ Y := fun δ Y =>
    forall₂_congr fun w t => by rw [Complex.coe_smul]; rfl
  refine contDiff_infty.2 fun n => ?_
  exact UMGS.contDiff_comp_pr (umgComp τ W.J) (Lines σ W) (fun _ h => h.1) (fun _ h x => umg_cj_mem h x)
    (fun δ h => (hG F E σ hcm τ d W hW δ h).imp fun Y hY => (hGn δ Y).2 hY.2) β c hβ
    (fun f f' h δ hδ Y hY => hl f f' h δ hδ Y ((hGn δ Y).1 hY)) S
    (fun f hf => ⟨(hS f hf).1, (hS f hf).2.2⟩) γ hγ g n f hfS

end PositivityTheory.ThKEst

end
end

