import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section cpt

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cpt_zero (Bs : B.RealPlaceData k ρ Wp Wq) : KB.CptCoef Bs (fun _ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩

theorem cpt_add_smul (Bs : B.RealPlaceData k ρ Wp Wq) {F₁ F₂ : B.Mat k ρ → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (F₁ + c • F₂) := by
  obtain ⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩ := h₁
  obtain ⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩ := h₂
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩,
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (hR₂ g hg this).trans (le_max_right _ _)
    · exact (hR₁ g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (min_le_right _ _).trans (hG₂ g hg this)
    · exact (min_le_left _ _).trans (hG₁ g hg h0)

theorem cpt_sum (Bs : B.RealPlaceData k ρ Wp Wq) {ι : Type} (S : Finset ι) (c : ι → ℂ) (F : ι → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hF : ∀ i, KB.CptCoef Bs (F i)) : KB.CptCoef Bs (∑ i ∈ S, c i • F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact cpt_zero Bs
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, add_comm]
    exact cpt_add_smul Bs (c b) ih (hF b)

theorem nice_of_cpt (Bs : B.RealPlaceData k ρ Wp Wq) {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) :
    ∃ ε, JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, -, hG⟩⟩ := h
  refine ⟨ε, hs, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ R)
    (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

theorem nice_vec_of_cpt {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq) {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : ∀ a, KB.CptCoef Bs (x a)) : ∃ ε, ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  have hx : ∀ a, KB.CptCoef Bs (x a) := h

  choose εf hεf using fun a => (hx a).2.2
  by_cases hS : Nonempty S
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty εf, fun a => ?_⟩
    obtain ⟨ε', hε'⟩ := nice_of_cpt Bs (hx a)
    refine ⟨hε'.1, hε'.2.1, fun g hg hne => ?_⟩
    exact (Finset.inf'_le _ (Finset.mem_univ a)).trans ((hεf a).2 g hg hne)
  · refine ⟨0, fun a => (hS ⟨a⟩).elim⟩

end cpt

section shift

theorem poly_shift {E : Type} [AddCommGroup E] [Module ℂ E] (d : ℕ) (c : Fin (d + 1) → E) (δ : ℂ) :
    ∃ c' : Fin (d + 1) → E, c' (Fin.last d) = c (Fin.last d) ∧
      ∀ t : ℂ, ∑ l : Fin (d + 1), (t + δ) ^ (l : ℕ) • c l = ∑ m : Fin (d + 1), t ^ (m : ℕ) • c' m := by
  refine ⟨fun m => ∑ l : Fin (d + 1),
    (if (m : ℕ) ≤ l then (((l : ℕ).choose m : ℂ) * δ ^ ((l : ℕ) - m)) else 0) • c l, ?_, fun t => ?_⟩
  · dsimp only
    rw [Finset.sum_eq_single (Fin.last d)]
    · simp
    · intro l _ hl
      have := l.isLt
      have hl' : (l : ℕ) ≠ d := fun e => hl (Fin.ext (by simp [e]))
      rw [if_neg (by simp; omega), zero_smul]
    · simp
  · simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_smul]
    congr 1
    have hl := l.isLt
    rw [Fin.sum_univ_eq_sum_range (fun m => t ^ m * if m ≤ (l : ℕ) then ((l : ℕ).choose m : ℂ) * δ ^ ((l : ℕ) - m) else 0)
      (d + 1)]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (d + 1)) (fun m => m ≤ (l : ℕ))]
    have h1 : (Finset.range (d + 1)).filter (fun m => m ≤ (l : ℕ)) = Finset.range ((l : ℕ) + 1) := by
      ext m; simp; omega
    rw [h1, Finset.sum_eq_zero (s := (Finset.range (d + 1)).filter (fun m => ¬ m ≤ (l : ℕ)))
      (fun m hm => by simp at hm; rw [if_neg (by omega), mul_zero]), add_zero, add_pow]
    apply Finset.sum_congr rfl
    intro m hm
    simp at hm
    rw [if_pos (by omega)]
    ring

end shift

section vand

theorem vand_ident {n : ℕ} (τ : Fin n → ℂ) (hτ : Function.Injective τ) (t : ℂ) (m : Fin n) :
    ∑ i : Fin n, (∑ l : Fin n, t ^ (l : ℕ) * (Matrix.vandermonde τ)⁻¹ l i) * τ i ^ (m : ℕ) = t ^ (m : ℕ) := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hinv : (Matrix.vandermonde τ)⁻¹ * Matrix.vandermonde τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  calc ∑ i : Fin n, (∑ l : Fin n, t ^ (l : ℕ) * (Matrix.vandermonde τ)⁻¹ l i) * τ i ^ (m : ℕ)
      = ∑ l : Fin n, t ^ (l : ℕ) * ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i * Matrix.vandermonde τ i m := by
        simp only [Finset.sum_mul, Finset.mul_sum, Matrix.vandermonde_apply]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ l : Fin n, t ^ (l : ℕ) * (1 : Matrix (Fin n) (Fin n) ℂ) l m := by
        apply Finset.sum_congr rfl; intro l _; rw [← Matrix.mul_apply, hinv]
    _ = t ^ (m : ℕ) := by
        simp [Matrix.one_apply]

theorem vand_row {n : ℕ} (τ : Fin n → ℂ) (hτ : Function.Injective τ) (l m : Fin n) :
    ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i * τ i ^ (m : ℕ) = if l = m then 1 else 0 := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hinv : (Matrix.vandermonde τ)⁻¹ * Matrix.vandermonde τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have := congrFun (congrFun hinv l) m
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [Matrix.vandermonde_apply] using this

end vand

section slicepoly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sliceAt_zero (z z' : Fin (2 * r + k + 1) → ℂ) (p : C.LPt) :
    D.sliceAt k r z z' (fun _ => (0 : Wq →L[ℂ] Wp)) p = fun _ => 0 := by
  funext γ
  unfold D.sliceAt
  split_ifs
  · simp [U.PhiFun, D.castF]
  · rfl

theorem slicePoly_of_pt (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (h : C.LPt) (hh : D.IsLocPt h j) (w' : List C.Letter) (b : Bool) (δ : ℝ)
    (e : Fin 2)
    (hpt : ∀ (a : Wd.Ix (Fin w'.length)), ∀ g ∈ B.GV k r, Dmin k r T.base.z T.base.z' g ⟨j, by omega⟩ ≠ 0 →
      ∃ c : Fin (j + 1) → (Wq →L[ℂ] Wp), c (Fin.last j) = (if e = 0 then D.uwG k r T.base.z T.base.z' F j hj w' a g else 0) ∧
        ∀ t : ℝ, D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a) g = ∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • c l) :
    ∃ Cf : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      Cf (Fin.last j) = (if e = 0 then KB.slv T F j hj w' h hh.2 else 0) ∧
      (∀ l, ∃ ε, ∀ a, JC.NiceCoef (T.bs j) ε (Cf l a)) ∧
      ∀ t : ℝ, EqGV (fun a => KB.slv T F j hj ((b, t + δ) :: w') h hh.2 (Fin.cons e a))
        (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l) := by
  classical
  set τ : Fin (j + 1) → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b' hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  set Vi := (Matrix.vandermonde τ)⁻¹ with hVi
  set Vt : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) :=
    fun i a => KB.slv T F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') h hh.2 (Fin.cons e a) with hVt
  set top : Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) :=
    if e = 0 then KB.slv T F j hj w' h hh.2 else 0 with htop
  refine ⟨fun l => if l = Fin.last j then top else ∑ i, Vi l i • Vt i, if_pos rfl, ?_, ?_⟩
  ·
    have hc : ∀ (i : ℕ) (hi : i ≤ r) (hi1 : 1 ≤ i) (w : List C.Letter) (hp : D.IsLocPt h i) (a : Wd.Ix (Fin w.length)),
        KB.CptCoef (T.bs i) (KB.slv T F i hi w h hp.2 a) := fun i hi hi1 w hp a =>
      Formalism.FourierDecayAlt.P.PBE.slice_pos_cpt k r Wp Wq T F hF i hi hi1 w h (by rw [hp.2]) hp a
    intro l
    by_cases hl : l = Fin.last j
    · by_cases he : e = 0
      · simp only [hl, if_pos rfl, htop, he, if_true]
        exact nice_vec_of_cpt (T.bs j) (fun a => hc j hj hj1 w' hh a)
      · simp only [hl, if_pos rfl, htop, he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · simp only [hl, if_false]
      refine nice_vec_of_cpt (T.bs j) (fun a => ?_)
      have e1 : (∑ i, Vi l i • Vt i) a = ∑ i, Vi l i • Vt i a := by simp [Finset.sum_apply]
      rw [e1]
      exact cpt_sum (T.bs j) _ _ _ (fun i => hc j hj hj1 _ hh _)
  ·
    intro t a γ hγ
    have hcast : r - j = r - D.ptSize h := by rw [hh.2]
    have hγ' : D.castM hcast γ ∈ B.GV k (r - D.ptSize h) := Formalism.FourierDecayAlt.P.PBE.castM_GV hcast hγ

    have hL := sliceAt_lincomb k r Wp Wq T F hF j hj hj1 h hh Finset.univ
      (fun i => ∑ l : Fin (j + 1), (t : ℂ) ^ (l : ℕ) * Vi l i) (fun i => (b, ((i : ℕ) : ℝ) + δ) :: w')
      (fun _ => Fin.cons e a) (D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a)) (by
        intro g hg hD
        obtain ⟨c, -, hc⟩ := hpt a g hg hD
        rw [hc t]
        simp only [hc]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [← Finset.sum_smul]
        congr 1
        have := vand_ident τ hτ (t : ℂ) m
        simp only [hτdef] at this
        rw [← this]) (D.castM hcast γ) hγ'

    have hT := sliceAt_lincomb k r Wp Wq T F hF j hj hj1 h hh Finset.univ
      (fun i => Vi (Fin.last j) i) (fun i => (b, ((i : ℕ) : ℝ) + δ) :: w')
      (fun _ => Fin.cons e a) (if e = 0 then D.uwG k r T.base.z T.base.z' F j hj w' a else fun _ => 0) (by
        intro g hg hD
        obtain ⟨c, hcl, hc⟩ := hpt a g hg hD
        simp only [hc]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ m : Fin (j + 1), ∑ i : Fin (j + 1), (Vi (Fin.last j) i * ((((i : ℕ) : ℝ) : ℂ)) ^ (m : ℕ)) • c m =
            (if Fin.last j = m then (1 : ℂ) else 0) • c m := by
          intro m
          rw [← Finset.sum_smul]
          congr 1
          have := vand_row τ hτ (Fin.last j) m
          simp only [hτdef] at this
          rw [← this]
        simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [hcl]
        split_ifs <;> simp) (D.castM hcast γ) hγ'

    show D.castF _ (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a)) h) γ = _
    simp only [D.castF]
    rw [hL]
    simp only [Finset.sum_apply, Pi.smul_apply]
    have hR : ∀ x : Fin (j + 1), (if x = Fin.last j then top else ∑ i, Vi x i • Vt i) a γ =
        ∑ q, Vi x q • D.sliceAt k r T.base.z T.base.z'
          (D.uwG k r T.base.z T.base.z' F j hj ((b, ((q : ℕ) : ℝ) + δ) :: w') (Fin.cons e a)) h (D.castM hcast γ) := by
      intro x
      by_cases hx : x = Fin.last j
      · rw [if_pos hx, hx, ← hT]
        simp only [htop]
        by_cases he : e = 0
        · simp only [he, if_true, KB.slv, D.castF]
        · simp only [he, if_false, sliceAt_zero, Pi.zero_apply]
      · rw [if_neg hx]
        simp only [Finset.sum_apply, Pi.smul_apply, hVt, KB.slv, D.castF]
    simp only [hR, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end slicepoly

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransformSquareIntegrable
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section L2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wt0 (c' : Cf r 0) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem level_zero_weight_measurable : Measurable (wt0 (r := r)) := by
  unfold wt0
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelZeroSquareIntegrable (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u u (glue 0 c c'))

theorem pairAt_meas0 (μ : Measure (Mt k r)) [SFinite μ] (u v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable (fun c' : Cf r 0 => pairAt μ u v (glue 0 c c')) :=
  (pair_measurable c u v).stronglyMeasurable.integral_prod_right'

theorem hsInner_self_ofReal (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_self (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofReal]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_self, norm_pairAt_self]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_cross (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelZeroSquareIntegrable μ u c) (Iv : LevelZeroSquareIntegrable μ v c) :
    Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u v (glue 0 c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    (level_zero_weight_measurable.aestronglyMeasurable.mul (pairAt_meas0 μ u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wt0 c' * pairAt μ u v (glue 0 c c')‖ ≤
    ‖wt0 c' * pairAt μ u u (glue 0 c c')‖ + ‖wt0 c' * pairAt μ v v (glue 0 c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_le μ hμ hu hv _) (norm_nonneg _)

theorem pairAt_zero_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) :
    pairAt μ (0 : RadSp k r z z' π π') 0 c = 0 := by
  unfold pairAt
  simp [hsInner_zero_left]

theorem pairAt_add_add (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (u + v) (u + v) c = pairAt μ u u c + pairAt μ u v c + pairAt μ v u c + pairAt μ v v c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    show B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
    rw [Formalism.FourierDecayAlt.P.B6.hsInner_add_left, Formalism.FourierDecayAlt.P.B6.hsInner_add_right, Formalism.FourierDecayAlt.P.B6.hsInner_add_right]
    ring
  have e2 : (∫ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ∂μ) =
      ∫ g, ((fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)))) g ∂μ := by
    congr 1; funext g; rw [e g]; rfl
  rw [e2, integral_add' (((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)).add (int_lc μ hμ hv hu c))
      (int_lc μ hμ hv hv c),
    integral_add' ((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)) (int_lc μ hμ hv hu c),
    integral_add' (int_lc μ hμ hu hu c) (int_lc μ hμ hu hv c)]

variable (k r z z' π π') in

def squareIntegrableSmoothSubmoduleGL (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    Submodule ℂ (RadSp k r z z' π π') where
  carrier := {u | u ∈ lcSub k r z z' π π' ∧ ∀ c, LevelZeroSquareIntegrable μ u c}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun c => by
    unfold LevelZeroSquareIntegrable
    simp only [pairAt_zero_zero, mul_zero]
    exact integrable_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    refine ⟨(lcSub k r z z' π π').add_mem hu hv, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_add_add μ hμ hu hv, mul_add]
    exact (((Iu c).add (int_cross μ hμ hu hv c (Iu c) (Iv c))).add
      (int_cross μ hμ hv hu c (Iv c) (Iu c))).add (Iv c)
  smul_mem' := by
    rintro a u ⟨hu, Iu⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a hu, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_smul_left, pairAt_smul_right]
    have e : (fun c' : Cf r 0 => wt0 c' * (a * ((starRingEnd ℂ) a * pairAt μ u u (glue 0 c c')))) =
        fun c' => (a * (starRingEnd ℂ) a) * (wt0 c' * pairAt μ u u (glue 0 c c')) := by
      funext c'; ring
    rw [e]
    exact (Iu c).const_mul _

theorem unimodular_multiplier_preserves_L2 (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (hm : ∀ c g, ‖m c g‖ = 1) : ∀ u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ, W u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ := by
  rintro u ⟨hu, Iu⟩
  refine ⟨mul_lc hW u hu, fun c => ?_⟩
  have e : ∀ c0, pairAt μ (W u) (W u) c0 = pairAt μ u u c0 := by
    intro c0
    unfold pairAt
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show B.hsInner ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) = _
    rw [hW u c0 (Matrix.of g), hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hm]
    simp
  unfold LevelZeroSquareIntegrable
  simp_rw [e]
  exact Iu c

theorem norm_fsv (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [this, Real.exp_zero]

end L2

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem radial_transform_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => F) (fun _ => F) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hF.1.1) (fun _ => hF.1.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

theorem compact_kernel_le_L2 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') :
    herKc S P z z' π π' L st l0 D 0 ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ => exact fun _ => radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun c _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun c _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
    | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun _ _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun _ _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
  exact key 0 Φ hΦ rfl

end Classes

end Formalism.FourierDecayAlt.P5.HerC
end
end

