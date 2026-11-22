import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x2

lemma c2x3_tel (y : ℕ → ℝ) (hy : ∀ i, y i ≠ 0) :
    ∀ n, ∏ l ∈ Finset.range n, y (l + 1) / y l = y n / y 0 := by
  intro n
  induction n with
  | zero => simp [div_self (hy 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, div_mul_div_comm, mul_comm (y n) (y (n + 1)),
      mul_div_mul_right _ _ (hy n)]

lemma c2x3_w2core (y : ℕ → ℝ) (hy : ∀ i, 0 < y i) (h0 : y 0 = 1) (K : ℕ) : ∀ r : ℕ,
    ∏ l ∈ Finset.range r, (y (l + 1) / y l) ^ (4 * (r - l) + K) =
      y r ^ K * ∏ l ∈ Finset.range r, y (l + 1) ^ 4 := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ r ih =>
    have hsplit : ∀ l ∈ Finset.range (r + 1), (y (l + 1) / y l) ^ (4 * (r + 1 - l) + K) =
        (y (l + 1) / y l) ^ 4 * (y (l + 1) / y l) ^ (4 * (r - l) + K) := by
      intro l hl
      rw [Finset.mem_range] at hl
      rw [← pow_add]; congr 1; omega
    rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_pow,
      c2x3_tel y (fun i => (hy i).ne') (r + 1), h0, div_one,
      Finset.prod_range_succ (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + K)), ih, Nat.sub_self,
      mul_zero, zero_add, Finset.prod_range_succ (fun l => y (l + 1) ^ 4)]
    have hr0 := (hy r).ne'
    have hq : y r ^ K * (y (r + 1) / y r) ^ K = y (r + 1) ^ K := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero K hr0)]
    calc y (r + 1) ^ 4 * (y r ^ K * (∏ l ∈ Finset.range r, y (l + 1) ^ 4) * (y (r + 1) / y r) ^ K)
        = y (r + 1) ^ 4 * (∏ l ∈ Finset.range r, y (l + 1) ^ 4) * (y r ^ K * (y (r + 1) / y r) ^ K) := by ring
      _ = y (r + 1) ^ K * ((∏ l ∈ Finset.range r, y (l + 1) ^ 4) * y (r + 1) ^ 4) := by rw [hq]; ring

theorem gram_product_identity : C2.GramProductIdentity := by
  intro k r x Gv hk hx0 hxpos hG
  obtain ⟨y, hyx, hypos⟩ : ∃ y : ℕ → ℝ, (∀ i (h : i < r + 1), y i = x ⟨i, h⟩) ∧ ∀ i, 0 < y i :=
    ⟨fun i => if h : i < r + 1 then x ⟨i, h⟩ else 1, fun i h => dif_pos h,
     fun i => by dsimp only; split_ifs; exacts [hxpos _, one_pos]⟩
  have hy0 : y 0 = 1 := by
    rw [hyx 0 (Nat.succ_pos r)]
    have : (⟨0, Nat.succ_pos r⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
    rw [this, hx0]
  have hsucc : ∀ l : Fin r, x l.succ = y (l.val + 1) := by
    intro l; rw [hyx _ (by omega)]; rfl
  have hcast : ∀ l : Fin r, x l.castSucc = y l.val := by
    intro l; rw [hyx _ (by omega)]; rfl
  have hlast : x (Fin.last r) = y r := by rw [hyx _ (Nat.lt_succ_self r)]; rfl
  have hexp : ∀ l : Fin r, 2 * (C2.Ml k r (l.val + 1) - 2) = 4 * (r - l.val) + 2 * (k - 1) := by
    intro l; unfold C2.Ml; have := l.isLt; omega
  simp only [hsucc, hcast, hexp, hlast]
  rw [Fin.prod_univ_eq_prod_range (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + 2 * (k - 1))) r,
    Fin.prod_univ_eq_prod_range (fun l => y (l + 1) ^ 4) r, c2x3_w2core y hypos hy0 (2 * (k - 1)) r]
  have := (hypos r).ne'
  rw [div_pow, pow_mul]
  field_simp

lemma c2x3_iSet_card {m a : ℕ} (h : a ≤ m) : (C2.iSet m a).card = a := by
  unfold C2.iSet
  rw [Fin.card_filter_val_lt]; omega

lemma c2x3_wSet_card {m a : ℕ} (w : Equiv.Perm (Fin m)) (h : a ≤ m) : (C2.wSet w a).card = a := by
  unfold C2.wSet
  rw [Finset.card_image_of_injective _ w.injective, c2x3_iSet_card h]

lemma c2x3_det_mono_ne {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (e f : Fin k → Fin m) (he : Function.Injective e) (hf : Function.Injective f)
    (hs : ∀ j, ∃ i, e i = w (f j)) : ((C2.monoP w d).submatrix e f).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply Matrix.isUnit_det_of_left_inverse
    (B := Matrix.of fun j i => if e i = w (f j) then (d (f j))⁻¹ else 0)
  ext j j'
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply, C2.monoP]
  obtain ⟨i0, hi0⟩ := hs j
  rw [Finset.sum_eq_single i0]
  · rw [if_pos hi0]
    by_cases hjj : j = j'
    · subst hjj; rw [if_pos hi0, Matrix.one_apply_eq]; field_simp [hd (f j)]
    · rw [if_neg, mul_zero, Matrix.one_apply_ne hjj]
      intro e'; apply hjj; rw [hi0] at e'; exact hf (w.injective e')
  · intro i _ hi
    rw [if_neg, zero_mul]
    intro e'; apply hi; exact he (e'.trans hi0.symm)
  · simp

theorem minor_C_nonzero : C2.MinorCNonzero := by
  intro m w d hd a ha
  have hI := c2x3_wSet_card w ha
  have hJ := c2x3_iSet_card ha
  unfold C2.minorS
  rw [dif_pos (hI.trans hJ.symm)]
  apply c2x3_det_mono_ne w d hd _ _ (RelEmbedding.injective _) (RelEmbedding.injective _)
  intro j
  have hmem : w ((C2.iSet m a).orderEmbOfFin (hI.trans hJ.symm).symm j) ∈ C2.wSet w a :=
    Finset.mem_image_of_mem w (Finset.orderEmbOfFin_mem _ _ j)
  have hr := Finset.range_orderEmbOfFin (C2.wSet w a) (rfl : (C2.wSet w a).card = (C2.wSet w a).card)
  rw [← Finset.mem_coe, ← hr] at hmem
  exact hmem

theorem stabilizer_antidiagonal_exact : C2.StabAntidiagExact := by
  intro s l u t hu ht
  have hW := c2x2_antiW_sq s
  constructor
  · intro h
    have h1 : l * C2.antiW s * u = C2.antiW s := by
      have : t • (l * C2.antiW s * u) = t • C2.antiW s := by
        rw [← h]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      exact smul_right_injective _ ht this
    calc l = l * C2.antiW s * u * u⁻¹ * C2.antiW s := by
          rw [Matrix.mul_assoc (l * C2.antiW s) u, Matrix.mul_nonsing_inv _ (ut_unit hu), Matrix.mul_one,
            Matrix.mul_assoc, hW, Matrix.mul_one]
      _ = C2.antiW s * u⁻¹ * C2.antiW s := by rw [h1]
  · rintro rfl
    exact (stabilizer_antidiagonal s u t hu ht).2.1

lemma c2x3_cs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (U : Submodule ℂ (Fin n → ℂ))
    (hpos : ∀ v ∈ U, v ≠ 0 → 0 < (herm H v v).re) (a b : Fin n → ℂ) (ha : a ∈ U) (hb : b ∈ U) :
    Complex.normSq (herm H a b) ≤ (herm H a a).re * (herm H b b).re := by
  have hnn : ∀ v ∈ U, 0 ≤ (herm H v v).re := by
    intro v hv
    by_cases h0 : v = 0
    · subst h0; simp [herm]
    · exact le_of_lt (hpos v hv h0)
  have hreal : ∀ v, (herm H v v).im = 0 := by
    intro v
    have := ggHerm_swap H hH v v
    have h2 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  by_cases hb0 : b = 0
  · subst hb0; simp [herm]
  have hbpos := hpos b hb hb0
  set β := herm H a b with hβ
  set q : ℝ := (herm H b b).re with hq
  have hbb : herm H b b = (q : ℂ) := Complex.ext rfl (by rw [hreal]; simp)
  have hba : herm H b a = conj β := by rw [ggHerm_swap H hH b a]; rfl
  set s : ℂ := β / (q : ℂ) with hs
  have hx : a - s • b ∈ U := U.sub_mem ha (U.smul_mem s hb)
  have hexp : herm H (a - s • b) (a - s • b) =
      herm H a a - conj s * β - s * herm H b a + s * conj s * herm H b b := by
    simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hβ]
    simp only [Complex.star_def]
    ring
  have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hkey : herm H (a - s • b) (a - s • b) = herm H a a - ((Complex.normSq β / q : ℝ) : ℂ) := by
    rw [hexp, hba, hbb, hs]
    have hn : ((Complex.normSq β : ℝ) : ℂ) = conj β * β := Complex.normSq_eq_conj_mul_self
    rw [map_div₀, Complex.conj_ofReal]
    push_cast
    rw [hn]
    field_simp
    ring
  have h1 := hnn _ hx
  rw [hkey, Complex.sub_re, Complex.ofReal_re] at h1
  have : Complex.normSq β / q ≤ (herm H a a).re := by linarith
  rw [div_le_iff₀ hbpos] at this
  linarith

theorem projection_property : C2.ProjClaim := by
  intro n H P U c hH hH2 hpos hPU horth hc hPn v hv
  have hE : ∀ x : Fin n → ℂ, star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
    intro x
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  have hEnn : ∀ x : Fin n → ℂ, 0 ≤ ∑ i, Complex.normSq (x i) :=
    fun x => Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hHv : ∀ u : Fin n → ℂ, herm H (H *ᵥ v) u = star u ⬝ᵥ v := by
    intro u; simp only [herm, Matrix.mulVec_mulVec, hH2, Matrix.one_mulVec]
  set w := P *ᵥ (H *ᵥ v) with hw
  have hwU : w ∈ U := hPU _
  have hwu : ∀ u ∈ U, herm H w u = star u ⬝ᵥ v := by
    intro u hu
    have := horth (H *ᵥ v) u hu
    simp only [herm, Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at this
    rw [← hHv u]; simp only [herm]; exact this.symm

  have hEH : ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
    have h1 := hE (H *ᵥ v)
    have h2 := hE v
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec, h2] at h1
    exact_mod_cast h1.symm
  set Ev := ∑ i, Complex.normSq (v i) with hEv
  set Ew := ∑ i, Complex.normSq (w i) with hEw
  have hw2 : Ew ≤ c ^ 2 * Ev := by rw [← hEH]; exact hPn _

  have hcsU := c2x3_cs H hH U hpos w v hwU hv
  rw [hwu v hv, hE v, Complex.normSq_ofReal] at hcsU

  have hpos1 : ∀ x ∈ (⊤ : Submodule ℂ (Fin n → ℂ)), x ≠ 0 → 0 < (herm 1 x x).re := by
    intro x _ hx0
    simp only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))
  have hcs1 := c2x3_cs 1 (by simp) ⊤ hpos1 v w Submodule.mem_top Submodule.mem_top
  simp only [herm, Matrix.one_mulVec, hE, Complex.ofReal_re] at hcs1

  set ρ := (herm H w w).re with hρ
  have hρ2 : ρ ^ 2 ≤ (c * Ev) ^ 2 := by
    have h1 : ρ ^ 2 ≤ Complex.normSq (herm H w w) := by
      rw [hρ, Complex.normSq_apply]; nlinarith [sq_nonneg (herm H w w).im]
    rw [hwu w hwU] at h1
    have h2 : Complex.normSq (star w ⬝ᵥ v) ≤ Ev * Ew := hcs1
    have h3 : Ev * Ew ≤ Ev * (c ^ 2 * Ev) := mul_le_mul_of_nonneg_left hw2 (hEnn v)
    nlinarith
  have hcE : 0 ≤ c * Ev := mul_nonneg hc (hEnn v)
  have hρle : ρ ≤ c * Ev := by nlinarith
  have hvv := hcsU
  have hhv : 0 ≤ (herm H v v).re := by
    by_cases h0 : v = 0
    · subst h0; simp [herm]
    · exact le_of_lt (hpos v hv h0)
  by_cases hE0 : Ev = 0
  · rw [hE0]; exact mul_nonneg hc hhv
  · have hEpos : 0 < Ev := lt_of_le_of_ne (hEnn v) (Ne.symm hE0)
    have : Ev * Ev ≤ c * Ev * (herm H v v).re := by nlinarith
    nlinarith

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TorusArgumentMultiplicative
section
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder

namespace Formalism.FourierDecayAlt.P

theorem torus_action_group : C7.TaGroup := by
  intro a b φ ψ
  refine ⟨?_, ?_, ?_⟩
  · unfold C7.taS; rw [Complex.norm_exp]; simp
  · unfold C7.taS; rw [← Complex.exp_add]; congr 1; push_cast; ring
  · simp [C7.taS]

theorem torus_argument_multiplicative : C7.TaArgMul := by
  intro a b Dr ζ hDr hζ
  have h := Complex.arg_mul_coe_angle hDr hζ
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  have e : Complex.arg (Dr * ζ) = Complex.arg Dr + Complex.arg ζ + 2 * Real.pi * m := by linarith
  unfold C7.taS
  rw [← Complex.exp_add, e, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(m * (a + b)), ?_⟩
  push_cast; ring

theorem hilbertSchmidt_frame : C7.HSFrame := by
  intro E E' _ _ _ _ _ _ U U' J₁ J₂
  have hadj : ∀ J : E' →L[ℂ] E, ContinuousLinearMap.adjoint (C7.frameConj U U' J) =
      (U'.symm.toContinuousLinearEquiv : E' →L[ℂ] E') ∘L ContinuousLinearMap.adjoint J ∘L
        (U.toContinuousLinearEquiv : E →L[ℂ] E) := by
    intro J
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [C7.frameConj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [← U'.inner_map_map, LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left,
      ← U.inner_map_map (x := x), LinearIsometryEquiv.apply_symm_apply]
  have e : ((ContinuousLinearMap.adjoint (C7.frameConj U U' J₂) ∘L C7.frameConj U U' J₁ : E' →L[ℂ] E') :
      E' →ₗ[ℂ] E') = (U'.symm.toLinearEquiv).conj
        ((ContinuousLinearMap.adjoint J₂ ∘L J₁ : E' →L[ℂ] E') : E' →ₗ[ℂ] E') := by
    apply LinearMap.ext; intro x
    rw [hadj]
    simp [C7.frameConj, LinearEquiv.conj_apply]
  rw [e, LinearMap.trace_conj']

theorem schur_product_posSemidef : C7.SchurProductPSD := by
  intro ι _ _ A C hA hC
  exact hA.hadamard hC

theorem c7_form_mono : C7.FormMono := by
  intro ι _ _ H _ _ V K K' hA
  have hG : ((Matrix.gram ℂ V)ᵀ).PosSemidef := (Matrix.posSemidef_gram (𝕜 := ℂ) V).transpose
  have hM := hA.hadamard hG
  have := hM.dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  simpa [dotProduct, mulVec, Matrix.hadamard_apply, Matrix.gram_apply, Matrix.transpose_apply] using this

theorem c7_form_mono_of_schur : C7.FormMonoOfSchur := fun _ => c7_form_mono

theorem extend_by_zero_posSemidef : C7.ExtendZeroPSD := by
  intro ι _ _ S _ K hK
  classical
  let P : Matrix S ι ℂ := Matrix.of fun s w => if (s : ι) = w then 1 else 0
  convert hK.conjTranspose_mul_mul_same P using 1
  ext w w'
  simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hw : w ∈ S <;> by_cases hw' : w' ∈ S
  · rw [dif_pos ⟨hw, hw'⟩]
    rw [Finset.sum_eq_single ⟨w', hw'⟩]
    · rw [Finset.sum_eq_single ⟨w, hw⟩]
      · simp
      · intro s _ hs; have : (s : ι) ≠ w := fun h => hs (Subtype.ext h); simp [this]
      · simp
    · intro s _ hs; have : (s : ι) ≠ w' := fun h => hs (Subtype.ext h); simp [this]
    · simp
  all_goals
    rw [dif_neg (by tauto)]
    symm
    apply Finset.sum_eq_zero
    intro s _
  · have : (s : ι) ≠ w' := fun h => hw' (h ▸ s.2); simp [this]
  · have : ∀ t : S, (t : ι) ≠ w := fun t h => hw (h ▸ t.2); simp [this]
  · have : ∀ t : S, (t : ι) ≠ w := fun t h => hw (h ▸ t.2); simp [this]

theorem schur_isotypic_decomposition : C7.SchurIsotypic := by
  intro K _ E E' R _ _ _ _ _ _ _ _ _ π π' ρ hπ hπ' _ hno J hJ φ hφ v x
  have unit : ∀ {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (σ : K →* (A →L[ℂ] A)),
      C7.IsUnitaryRep σ → ∀ k a b, ⟪σ k a, b⟫_ℂ = ⟪a, σ k⁻¹ b⟫_ℂ := by
    intro A _ _ σ hσ k a b
    have e : σ k (σ k⁻¹ b) = b := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← e]
    exact hσ k a (σ k⁻¹ b)
  let ψ : R →L[ℂ] E' := ContinuousLinearMap.adjoint J ∘L φ
  have hψ : C7.Intertw ρ π' ψ := by
    intro k
    ext y
    apply ext_inner_right ℂ
    intro z
    simp only [ψ, ContinuousLinearMap.comp_apply]
    rw [unit π' hπ', ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    have h1 := DFunLike.congr_fun (hJ k⁻¹) z
    have h2 := DFunLike.congr_fun (hφ k) y
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [← h1, ← unit π hπ, h2]
  have h0 := hno ψ hψ
  have : ⟪φ x, J v⟫_ℂ = ⟪ψ x, v⟫_ℂ := by
    simp only [ψ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [this, h0]; simp

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordIntegralScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (L : ι → E →L[ℂ] E) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => L i (φ i p)).sum) μ ∧
      ∫ p, (l.map fun i => L i (φ i p)).sum ∂μ = (l.map fun i => L i (∫ p, φ i p ∂μ)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hLi : Integrable (fun p => L i (φ i p)) μ := (L i).integrable_comp hi
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hLi.add hl1, ?_⟩
    rw [integral_add hLi hl1, hl2, ContinuousLinearMap.integral_comp_comm _ hi]

theorem smul_list {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (L : ι → E →L[ℂ] E)
    (x : ι → E) : c • (l.map fun i => L i (x i)).sum = (l.map fun i => L i (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons, map_smul]

variable {k r : ℕ}

theorem lr_nrm (v : List (Mat k r)) :
    (B4.lr [] v).map B4.nrm = B4.lr [] (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  simp [B4.lr, B4.nrm, List.map_map, Function.comp_def]

theorem rw_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = B4.pn (B4.lr [] v) • Rw (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) f := by
  have h := B4.W_nrm (B4.lr [] v) f
  rw [lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq] at h
  exact h

end Formalism.FourierDecayAlt.P.WordIntegralScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem theta_bessel_commute_of_parts : Formalism.FourierDecayAlt.JF.JThetaOfParts := by
  intro hW hR k r Wp Wq _ _ _ _ _ _ D A m F Θ ho hT hF hC g hg
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast ho) hCk
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp F hCo g hg]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

end Formalism.FourierDecayAlt.P
end
end

