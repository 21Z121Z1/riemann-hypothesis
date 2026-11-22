import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProof
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BalancedPointPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem conj_mem_iff (X : Data E r) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ ↔ σ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate σ)]
  simp [ComplexEmbedding.conjugate, star_star]

theorem sum_eq_two_mul (X : Data E r) (f : (E →+* ℂ) → ℝ)
    (hf : ∀ σ, f (ComplexEmbedding.conjugate σ) = f σ) :
    ∑ σ, f σ = 2 * ∑ τ : X.Ψ, f τ.1 := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ, Finset.sum_coe_sort X.Ψ f]
  have h : ∑ σ ∈ X.Ψᶜ, f σ = ∑ σ ∈ X.Ψ, f σ := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      exact (conj_mem_iff X σ).2 hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).1 hσ
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; exact (hf σ).symm
  rw [h]; ring

theorem card_Ψ (X : Data E r) : (Fintype.card X.Ψ : ℝ) = fdeg E := by
  have h := sum_eq_two_mul X (fun _ => (1 : ℝ)) (fun _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Embeddings.card E ℂ] at h
  have h2 : Module.finrank ℚ E = 2 * Fintype.card X.Ψ := by exact_mod_cast h
  rw [fdeg, h2, Nat.mul_div_cancel_left _ two_pos]

end

end GlobalTheory.BalancedPointPf

namespace GlobalTheory.BalancedPointPf

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem embVec_conj (σ : E →+* ℂ) (v : Fin r → E) :
    ReciprocityTheory.MultiplicativeHeights.embVec (ComplexEmbedding.conjugate σ) v = star (ReciprocityTheory.MultiplicativeHeights.embVec σ v) := by
  funext k
  simp [ReciprocityTheory.MultiplicativeHeights.embVec, ComplexEmbedding.conjugate_coe_eq]

theorem maj_eq_hq (X : Data E r) (H : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r)
    (ho : IsOrth X x) (hH : ∀ τ : X.Ψ, (mat x τ)ᴴ * H τ.1 * mat x τ = 1) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = ReciprocityTheory.MultiplicativeHeights.hq (H τ.1) u := by
  have hmo := GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth r X x ho
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hmo.1 τ)
  have e : H τ.1 = ((mat x τ)⁻¹)ᴴ * (mat x τ)⁻¹ := by
    calc H τ.1 = (mat x τ * (mat x τ)⁻¹)ᴴ * H τ.1 * (mat x τ * (mat x τ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hu]; simp
      _ = ((mat x τ)⁻¹)ᴴ * ((mat x τ)ᴴ * H τ.1 * mat x τ) * (mat x τ)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hH τ, Matrix.mul_one]
  rw [hmo.2 τ u, e, GlobalTheory.Up.BallExPf.hq_ct_mul]
  rfl

theorem balancedPoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  intro E _ _ _ r X
  obtain ⟨M, hss, hNC⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L'
    (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)
  have hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ,
      xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧
        xᴴ * M.H τ.1 * x = 1 := fun τ => by
    obtain ⟨P, hP, hPg⟩ := X.signature τ
    exact GlobalTheory.Up.BallExPf.exists_frame (M.posDef τ.1) (M.major τ.1) hP
      ((GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 P).1 hPg)
  choose y hy1 hy2 using hex
  let x0 : Frame X.Ψ r := fun τ => y τ
  have h0 : IsOrth X.toData x0 := fun τ => (GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 _).2 (hy1 τ)
  have hmaj : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj x0 τ u = ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) u :=
    maj_eq_hq X.toData M.H x0 h0 hy2
  refine ⟨x0, IW.orth_mem_dom X.toData x0 h0, ?_, ?_⟩
  · intro N hN hlt
    have key : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ≠ 0 →
        ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) (N.map τ.1 *ᵥ w) < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := by
      intro τ w hw
      obtain ⟨c, hc0, hc1, hc⟩ := hlt τ
      have h1 := hc w
      rw [hmaj, hmaj] at h1
      have hpos : 0 < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := (M.posDef τ.1).re_dotProduct_pos hw
      have hc2 : c ^ 2 < 1 := by nlinarith
      nlinarith
    refine hNC N hN fun σ u hu => ?_
    by_cases hσ : σ ∈ X.Ψ
    · exact key ⟨σ, hσ⟩ u hu
    · have hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (conj_mem_iff X.toData σ).2 hσ
      have hsu : star u ≠ 0 := fun h => hu (by simpa using congrArg star h)
      have h := key ⟨_, hσ'⟩ (star u) hsu
      have e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) := M.conj_compat σ
      have e2 : N.map (ComplexEmbedding.conjugate σ) *ᵥ star u = star (N.map σ *ᵥ u) := by
        funext k
        simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]
      simp only at h
      rwa [e1, e2, GlobalTheory.Up.BallExPf.hq_conj, GlobalTheory.Up.BallExPf.hq_conj] at h
  · intro v hv hv0
    classical
    set h : (E →+* ℂ) → ℝ := fun σ => ReciprocityTheory.MultiplicativeHeights.hq (M.H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ v) with hhdef
    have hpos : ∀ σ, 0 < h σ := by
      intro σ
      refine (M.posDef σ).re_dotProduct_pos fun h0 => hv0 ?_
      funext k
      have := congrFun h0 k
      simp only [ReciprocityTheory.MultiplicativeHeights.embVec, Pi.zero_apply, map_eq_zero] at this
      exact this
    have hconj : ∀ σ, h (ComplexEmbedding.conjugate σ) = h σ := by
      intro σ
      simp only [hhdef]
      rw [embVec_conj, show M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) from
        M.conj_compat σ, GlobalTheory.Up.BallExPf.hq_conj]

    set B : Submodule (𝓞 E) (Fin r → E) := Submodule.span (𝓞 E) {v} with hB
    have hrange : Set.range ![v] = {v} := by simp
    have hBL : B ≤ X.L' := by rw [hB, Submodule.span_le]; simpa using hv
    have hbasis : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn B ![v] := by
      refine ⟨fun i => ?_, ?_, fun y hy => ?_⟩
      · rw [Fin.eq_zero i]; exact Submodule.subset_span rfl
      · exact linearIndependent_unique_iff.2 (by simpa using hv0)
      · rw [hB, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        rw [hrange]
        have : (algebraMap (𝓞 E) E a) • v ∈ Submodule.span E ({v} : Set (Fin r → E)) :=
          Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        rwa [algebraMap_smul] at this
    have hdeg := hss.2 B hBL 1 ![v] hbasis
    have hidx : (Submodule.span (𝓞 E) (Set.range ![v])).toAddSubgroup.relIndex B.toAddSubgroup = 1 := by
      rw [hrange, ← hB]; exact AddSubgroup.relIndex_self _
    have hdet : ∀ σ, (ReciprocityTheory.MultiplicativeHeights.gramC (M.H σ) σ ![v]).det.re = h σ := by
      intro σ
      rw [Matrix.det_unique]
      rfl
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hidx, Nat.cast_one, Real.log_one, zero_sub, hdet] at hdeg
    have hsum : 0 ≤ ∑ σ, Real.log (h σ) := by linarith
    rw [sum_eq_two_mul X.toData (fun σ => Real.log (h σ)) (fun σ => by simp only [hconj])] at hsum
    have hlog : ∀ τ : X.Ψ, Real.log (h τ.1) ≤ h τ.1 - 1 := fun τ => Real.log_le_sub_one_of_pos (hpos τ.1)
    have hsum2 : 0 ≤ ∑ τ : X.Ψ, (h τ.1 - 1) :=
      (by linarith : 0 ≤ ∑ τ : X.Ψ, Real.log (h τ.1)).trans (Finset.sum_le_sum fun τ _ => hlog τ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_Ψ X.toData] at hsum2
    have e : ∀ τ : X.Ψ, X.maj x0 τ (Data.emb τ.1 v) = h τ.1 := fun τ => hmaj τ _
    simp only [e]
    linarith

end GlobalTheory.BalancedPointPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefinite
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
open scoped ComplexConjugate

namespace GlobalTheory.DefConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def detPow (Ψ : Finset (E →+* ℂ)) (a : ℤ) (x : Frame Ψ r) : ℂ := ∏ τ, (mat x τ).det ^ a

theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ), (∀ i, f i ≠ 0) →
    ∏ i : Fin n, f i.succ / f i.castSucc = f (Fin.last n) / f 0
  | 0, f, h => by
    rw [Fin.prod_univ_zero]; exact (div_self (h 0)).symm
  | n + 1, f, h => by
    rw [Fin.prod_univ_castSucc]
    have ih : ∏ i : Fin n, f i.succ.castSucc / f i.castSucc.castSucc =
        f (Fin.last n).castSucc / f (0 : Fin (n + 1)).castSucc :=
      telescope n (fun i => f i.castSucc) (fun i => h _)
    simp only [Fin.succ_castSucc]
    rw [ih, Fin.succ_last, Fin.castSucc_zero]
    have h1 := h (Fin.last n).castSucc
    have h2 := h 0
    field_simp

theorem lminor_zero (M : Matrix (Fin r) (Fin r) ℂ) : lminor M 0 = 1 := by
  unfold lminor
  exact Matrix.det_eq_one_of_card_eq_zero (by simp; exact Fintype.card_eq_zero)

theorem lminor_last (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  unfold lminor
  exact Matrix.det_submatrix_equiv_self (finCongr (Fin.val_last r)) M

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = x.transpose * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x).det = x.det * (G.map τ).det * starRingEnd ℂ x.det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (starRingEnd ℂ) x).symm

theorem dmin_ne (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

theorem pnorm_factor (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (a : ℤ) (τ : X.Ψ) :
    ‖(mat x τ).det ^ a‖ * ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  have hD : (mat x τ).det ≠ 0 := (hx τ).1
  have hpos : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hD
  have ht := telescope r (fun i => ‖dmin X.Gm x τ i‖) (fun i => norm_ne_zero_iff.mpr (dmin_ne X hx τ i))
  beta_reduce at ht
  have hprod : ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      (‖dmin X.Gm x τ (Fin.last r)‖ / ‖dmin X.Gm x τ 0‖) ^ (-(a : ℝ) / 2) := by
    simp_rw [norm_div]
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ht]
  rw [hprod]
  have h0 : dmin X.Gm x τ 0 = 1 := lminor_zero _
  have hl : dmin X.Gm x τ (Fin.last r) = (mat x τ).det * (X.Gm.map τ.1).det * starRingEnd ℂ (mat x τ).det := by
    unfold dmin; rw [lminor_last, det_gram]
  rw [h0, hl, norm_one, div_one, norm_mul, norm_mul, Complex.norm_conj, norm_zpow]
  have hg : 0 ≤ ‖(X.Gm.map τ.1).det‖ := norm_nonneg _
  rw [show ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x τ).det‖ =
      ‖(mat x τ).det‖ * ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ by ring,
    Real.mul_rpow (by positivity) hg, Real.mul_rpow hpos.le hpos.le, ← Real.rpow_intCast,
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  have : (a : ℝ) + -(a : ℝ) / 2 + -(a : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

theorem pnorm_detPow (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) (a : ℤ)
    (hla : ∀ τ i, la τ i = a) :
    X.pnorm la (detPow X.Ψ a) x = ∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  unfold Data.pnorm detPow
  simp only [hla, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => pnorm_factor X hx a τ

theorem det_diff (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Differentiable ℂ (fun x : Frame Ψ r => (mat x τ).det) := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem detPow_diff (X : Data E r) (a : ℤ) : DifferentiableOn ℂ (detPow X.Ψ a) X.dom := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  unfold detPow
  have h : ∀ τ : X.Ψ, DifferentiableAt ℂ (fun y : Frame X.Ψ r => (mat y τ).det ^ a) x :=
    fun τ => (det_diff X.Ψ τ x).zpow (Or.inl (hx τ).1)
  fun_prop

theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact 1 x = x := by
  funext τ
  simp [lact, mat, Matrix.map_one]
  rfl

theorem chi_one (X : Data E r) (la : Wt X.Ψ r) : X.χ la 1 = 1 := by
  have h1 : (1 : GL (Fin r) E) ∈ X.Γ := X.Γ.one_mem
  have hm := X.χ_mul la 1 h1 1 h1
  rw [mul_one] at hm
  obtain ⟨n, hn, hf⟩ := X.χ_fin la
  have hne : X.χ la 1 ≠ 0 := fun h0 => by
    have := hf 1 h1
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ)
    (v w : Fin r → ℂ) :
    hermC τ G (P.mulVec v) (P.mulVec w) = ∑ k, ∑ l, v k * gram τ G P k l * conj (w l) := by
  have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
      ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := by
    intro f
    calc ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ a, ∑ k, ∑ b, ∑ l, f a b k l :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, ∑ l, f a b k l := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ l, ∑ b, f a b k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc _ = ∑ a, ∑ b, ∑ k, ∑ l, P a k * v k * τ (G a b) * conj (P b l * w l) := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, P a k * v k * τ (G a b) * conj (P b l * w l) := sw _
    _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul]; ring

theorem not_iso (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, (X.cmType _).2 ?_⟩
      simpa using h
  obtain ⟨P, hP, hg⟩ := X.signature ⟨τ, hτ⟩
  set u : Fin r → ℂ := fun a => τ (ξ a) with hu_def
  have hu : hermC τ X.Gm u u = 0 := by
    have := congrArg τ h0
    simp only [herm, cc, map_sum, map_mul, map_zero, IsCMField.complexEmbedding_complexConj] at this
    simpa [hermC, u] using this
  obtain ⟨e, he, hsg⟩ : ∃ e : ℂ, e ≠ 0 ∧ ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) = e := by
    rcases hp with h | h
    · exact ⟨-1, by norm_num, fun a => by simp [sgn, h]⟩
    · exact ⟨1, one_ne_zero, fun a => by simp [sgn, h, a.isLt]⟩
  set v := P⁻¹.mulVec u with hv_def
  have hPv : P.mulVec v = u := by
    rw [hv_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have hsum : hermC τ X.Gm u u = e * ∑ a, v a * conj (v a) := by
    rw [← hPv, hermC_mulVec, hg]
    simp only [Matrix.diagonal_apply, hsg, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hv : v = 0 := by
    have h1 : ∑ a, (Complex.normSq (v a) : ℂ) = 0 := by
      have := hsum.symm.trans hu
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h he
      · simpa [Complex.mul_conj] using h
    have h2 : ∑ a, Complex.normSq (v a) = 0 := by exact_mod_cast h1
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)] at h2
    funext a
    simpa using h2 a (Finset.mem_univ _)
  have hu0 : u = 0 := by rw [← hPv, hv, Matrix.mulVec_zero]
  apply hne
  funext a
  have := congrFun hu0 a
  simpa [u] using this

theorem detPow_mem_SS (X : Data E r) (hΓ : ∀ γ ∈ X.Γ, γ = 1) (hdef : ∀ ξ, ¬ X.IsIso ξ) (la : Wt X.Ψ r)
    (a : ℤ) (hla : ∀ τ i, la τ i = a) : detPow X.Ψ a ∈ X.SS la := by
  refine ⟨⟨⟨detPow_diff X a, ?_, ?_⟩, ⟨_, fun x hx => (pnorm_detPow X hx la a hla).le⟩⟩,
    fun ξ hξ => absurd hξ (hdef ξ)⟩
  · intro x _ b hb
    unfold detPow bchar
    have hb' : ∀ τ : X.Ψ, (mat b τ).det = ∏ i, b τ i i := fun τ =>
      Matrix.det_of_upperTriangular (fun i j hij => (hb τ).2 i j hij)
    have e1 : ∀ τ : X.Ψ, (mat (rmul x b) τ).det ^ a = (mat x τ).det ^ a * ∏ i, b τ i i ^ la τ i := by
      intro τ
      rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, mul_zpow, hb' τ]
      simp only [hla]
      rw [Finset.prod_zpow]
    simp only [e1, Finset.prod_mul_distrib]
    ring
  · intro γ hγ x _
    rw [hΓ γ hγ, lact_one, chi_one, one_mul]

theorem exists_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom,
      ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  intro E _ _ _ r X hΓ hp s x hx
  refine ⟨detPow X.Ψ (if X.p0 = 0 then ((s / 2 : ℕ) : ℤ) else -((s / 2 : ℕ) : ℤ)),
    detPow_mem_SS X hΓ (not_iso X hp) _ _ ?_, ?_⟩
  · intro τ i
    by_cases h0 : X.p0 = 0
    · simp [deMul, h0]
    · have h : X.p0 = r := hp.resolve_left h0
      have hr : r ≠ 0 := h ▸ h0
      simp [deMul, h0, h, hr, i.isLt]
  · exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).1

end GlobalTheory.DefConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotent
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LevelSplit

theorem primesOver_eq (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) = {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} := by
  ext P
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨hP, ?_⟩
    have h1 : (g : ℤ) ∈ Ideal.span {(g : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hL.over] at h1
    simpa using (Ideal.mem_comap.mp h1)
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hgP

end GlobalTheory.LevelSplit

theorem GlobalTheory.levelHyp_totallySplit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  intro E _ _ _ r U C _ _ M hM
  obtain ⟨g, ⟨hg, hcard⟩, hgr, hU⟩ := hM
  have hset := GlobalTheory.LevelSplit.primesOver_eq E hg
  refine ⟨g, ⟨hg, ?_⟩, hgr, ?_⟩
  · rw [hset]; exact hcard
  · intro c β hβ P hP
    rw [hset] at hP
    exact ⟨r, fun v hv => hU c β hβ P hP.1 hP.2 v hv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperArithmeticGroupUnipotentUnitary
section
set_option autoImplicit false

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem tr_one_mem (M : TwoLevels E r U C) (c : C) : M.tr 1 c ∈ (M.comp c).Γ := by
  have h := M.tr_mul 1 1 c
  simp only [mul_one, one_smul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at h
  simpa using (M.comp c).Γ.inv_mem h

def upperSub (M : TwoLevels E r U C) (c : C) : Subgroup (GL (Fin r) E) where
  carrier := M.upper c
  one_mem' := ⟨1, one_smul U c, (M.tr 1 c)⁻¹, (M.comp c).Γ.inv_mem (tr_one_mem M c), by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, δ, hδ, rfl⟩
    have hc := (M.tr_conj u c δ).1 hδ
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [hv, mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * δ * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact (M.comp c).Γ.mul_mem ((M.comp c).Γ.mul_mem hγ hc) ((M.comp c).Γ.inv_mem hm)
    · group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [hu, inv_mul_cancel, one_smul] at hm
    have h1 := tr_one_mem M c
    have hε : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := (M.comp c).Γ.mul_mem ((M.comp c).Γ.inv_mem hm) h1
      simpa [mul_inv_rev, mul_assoc] using this
    have hc : (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c ∈ (M.comp c).Γ := by
      rw [M.tr_conj u c, hu]
      simpa [mul_assoc] using (M.comp c).Γ.inv_mem hγ
    refine ⟨u⁻¹, hu', (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c * (M.tr u⁻¹ c * M.tr u c)⁻¹,
      (M.comp c).Γ.mul_mem hc ((M.comp c).Γ.inv_mem hε), ?_⟩
    group

theorem prime_and_mem_of_primesOver {g : ℕ} {P : Ideal (𝓞 E)}
    (hP : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E)) : P.IsPrime ∧ (g : 𝓞 E) ∈ P := by
  obtain ⟨hp, hl⟩ := hP
  refine ⟨hp, ?_⟩
  have hg : (g : ℤ) ∈ P.under ℤ := by
    rw [← hl.over]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap] at hg
  simpa using hg

theorem upper_subgroup (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) (g : ℕ) (hU : M.UnipotentOver g) :
    ∃ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab (M.comp c).Gm (M.comp c).L' γ) ∧
      (∀ γ ∈ Γo, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g γ) ∧
      ∀ u : U, u • c = c → M.tr u c ∈ Γo := by
  refine ⟨upperSub M c, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, δ, hδ, rfl⟩
    have hs := (M.comp c).Γ_stab δ hδ
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm, M.tr_herm]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, M.tr_L' u c v, hu]
      exact M.Γ_L' c δ hδ _
  · intro γ hγ P hP
    obtain ⟨hp, hg⟩ := prime_and_mem_of_primesOver hP
    exact ⟨r, fun v hv => hU c γ hγ P hp hg v hv⟩
  · intro u hu
    exact ⟨u, hu, 1, (M.comp c).Γ.one_mem, (one_mul _).symm⟩

end GlobalTheory.UpperArith
end

