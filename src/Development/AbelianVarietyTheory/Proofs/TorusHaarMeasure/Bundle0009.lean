import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfHermOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix

namespace GlobalTheory.TwoLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_one_two (x y : Fin 2 → E) :
    herm (1 : Matrix (Fin 2) (Fin 2) E) x y = x 0 * cc (y 0) + x 1 * cc (y 1) := by
  simp [herm, Fin.sum_univ_two, Matrix.one_apply]

theorem emb_herm_one (φ : E →+* ℂ) (x : Fin 2 → E) :
    φ (herm (1 : Matrix (Fin 2) (Fin 2) E) x x) = ((‖φ (x 0)‖ ^ 2 + ‖φ (x 1)‖ ^ 2 : ℝ) : ℂ) := by
  rw [herm_one_two, map_add, map_mul, map_mul, emb_cc, emb_cc, Complex.mul_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem eq_zero_of_herm_one (x : Fin 2 → E) (h : herm (1 : Matrix (Fin 2) (Fin 2) E) x x = 0) :
    x = 0 := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have h1 := emb_herm_one φ x
  rw [h, map_zero] at h1
  have h2 : ‖φ (x 0)‖ ^ 2 + ‖φ (x 1)‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  have hsq0 := sq_nonneg ‖φ (x 0)‖
  have hsq1 := sq_nonneg ‖φ (x 1)‖
  have hx0 : x 0 = 0 := by
    have h3 : ‖φ (x 0)‖ ^ 2 = 0 := by linarith
    simpa using h3
  have hx1 : x 1 = 0 := by
    have h3 : ‖φ (x 1)‖ ^ 2 = 0 := by linarith
    simpa using h3
  funext i
  fin_cases i <;> simp [hx0, hx1]

omit [IsCMField E] in
theorem bounded_finite :
    {γ : GL (Fin 2) E | ∀ a b, IsIntegral ℤ ((γ : Matrix (Fin 2) (Fin 2) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) a b)‖ ≤ 1}.Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ 1
  have hpi : (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 1}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hS
  refine Set.Finite.subset
    (Set.Finite.preimage (f := fun (γ : GL (Fin 2) E) (a b : Fin 2) => (γ : Matrix (Fin 2) (Fin 2) E) a b)
      (fun γ _ δ _ hγδ => Units.ext (Matrix.ext fun a b => congrFun (congrFun hγδ a) b)) hpi) ?_
  intro γ hγ
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  intro a b
  exact ⟨(hγ a b).1, (hγ a b).2⟩

def intLat (E : Type) [Field E] : Submodule (𝓞 E) (Fin 2 → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

omit [NumberField E] [IsCMField E] in
theorem mem_intLat (x : Fin 2 → E) : x ∈ intLat E ↔ ∀ a, IsIntegral ℤ (x a) := by
  simp only [intLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

omit [NumberField E] [IsCMField E] in
theorem single_mem_intLat (b : Fin 2) : (Pi.single b 1 : Fin 2 → E) ∈ intLat E := by
  rw [mem_intLat]
  intro a
  by_cases hab : a = b
  · subst hab
    simp [isIntegral_one]
  · simp [hab, isIntegral_zero]

noncomputable def defData (E : Type) [Field E] [NumberField E] [IsCMField E] : Data E 2 where
  Ψ := (inhab (E := E)).Ψ
  cmType := (inhab (E := E)).cmType
  Gm := 1
  Gm_herm := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [cc_one, cc_zero]
  Gm_det := by simp
  p0 := 2
  p0_le := le_rfl
  signature := by
    intro τ
    refine ⟨1, by simp, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, sgn, Matrix.one_apply]
  Λ := intLat E
  Λ_fg := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  Λ_span := by
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → E) + x 1 • (Pi.single 1 1 : Fin 2 → E) := by
      funext i; fin_cases i <;> simp
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_intLat 0)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_intLat 1)))
  den := 1
  den_ne := one_ne_zero
  Λ_int := by
    intro x hx y hy
    rw [mem_intLat] at hx hy
    rw [herm_one_two, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
    exact ((hx 0).mul (isIntegral_cc (hy 0))).add ((hx 1).mul (isIntegral_cc (hy 1)))
  Γ := ⊥
  Γ_stab := by
    intro γ hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [IsUStab]
  Γ_index := by
    refine ⟨(bounded_finite (E := E)).toFinset, ?_⟩
    intro γ hγ
    refine ⟨γ, ?_, by simp⟩
    rw [Set.Finite.mem_toFinset]
    obtain ⟨hh, hl⟩ := hγ
    intro a b
    have hmem := (mem_intLat _).mp ((hl _).mp (single_mem_intLat b))
    have hv : ∀ c, Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) E) (Pi.single b 1) c =
        (γ : Matrix (Fin 2) (Fin 2) E) c b := by
      intro c; simp
    refine ⟨hv a ▸ hmem a, fun φ => ?_⟩
    have h1 := congrArg φ (hh (Pi.single b 1) (Pi.single b 1))
    rw [emb_herm_one, emb_herm_one, hv, hv] at h1
    have h2 : ‖φ ((Pi.single b 1 : Fin 2 → E) 0)‖ ^ 2 + ‖φ ((Pi.single b 1 : Fin 2 → E) 1)‖ ^ 2 = 1 := by
      fin_cases b <;> simp
    rw [h2] at h1
    have h3 : ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 0 b)‖ ^ 2 +
      ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 1 b)‖ ^ 2 = 1 := by exact_mod_cast h1
    have h4 : ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) a b)‖ ^ 2 ≤ 1 := by
      fin_cases a
      · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 1 b)‖]
      · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖φ ((γ : Matrix (Fin 2) (Fin 2) E) 0 b)‖]
    nlinarith [norm_nonneg (φ ((γ : Matrix (Fin 2) (Fin 2) E) a b))]
  Γ_free := fun γ hγ _ _ _ _ _ => Subgroup.mem_bot.mp hγ
  χ := fun _ _ => 1
  χ_mul := by intros; simp
  χ_add := by intros; simp
  χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
  ξ0 := (inhab (E := E)).ξ0
  ξ0_im := (inhab (E := E)).ξ0_im
  ξ0_ne := (inhab (E := E)).ξ0_ne
  κ0 := (inhab (E := E)).κ0
  κ0_xi := (inhab (E := E)).κ0_xi
  κ0_sign := (inhab (E := E)).κ0_sign
  m := 1
  m_pos := one_pos
  transv := by
    intro ξ _ hiso s _ _
    have hξ := eq_zero_of_herm_one ξ hiso
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    ext a b
    simp [transvMat, hξ, Matrix.one_apply]

theorem two_mul_card_cmType {r : ℕ} (X : Data E r) : 2 * X.Ψ.card = Module.finrank ℚ E := by
  classical
  have hinv : Function.Involutive (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    ComplexEmbedding.involutive_conjugate E
  have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
    rw [Finset.disjoint_left]
    intro τ hτ hτ'
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ'
    exact ((X.cmType σ).mp hσ) hτ
  have hunion : X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate = Finset.univ := by
    ext τ
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    by_cases hτ : τ ∈ X.Ψ
    · exact Or.inl hτ
    · refine Or.inr ⟨ComplexEmbedding.conjugate τ, ?_, hinv τ⟩
      rw [X.cmType, hinv τ]
      exact hτ
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinv.injective,
    Finset.card_univ, NumberField.Embeddings.card] at hcard
  omega

theorem exists_two {r : ℕ} (X : Data E r) (h : Module.finrank ℚ E = 4) :
    ∃ τ₁ τ₂ : X.Ψ, τ₁ ≠ τ₂ ∧ ∀ τ, τ = τ₁ ∨ τ = τ₂ := by
  classical
  have hc := two_mul_card_cmType X
  obtain ⟨a, b, hab, hΨ⟩ := Finset.card_eq_two.mp (by omega : X.Ψ.card = 2)
  have key : ∀ σ ∈ X.Ψ, σ = a ∨ σ = b := by
    intro σ hσ
    rw [hΨ] at hσ
    simpa using hσ
  have ha : a ∈ X.Ψ := by rw [hΨ]; simp
  have hb : b ∈ X.Ψ := by rw [hΨ]; simp
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun e => hab (congrArg Subtype.val e), fun τ => ?_⟩
  rcases key τ.1 τ.2 with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

end GlobalTheory.TwoLines
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder

namespace GlobalTheory.MajorantContinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_l {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_r {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma scale_lemma {n : ℕ} (s : ℝ) (A B : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, (s : ℂ) * A a * M a b * ((s : ℂ) * B b) = ((s ^ 2 : ℝ) : ℂ) * ∑ a, ∑ b, A a * M a b * B b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

lemma maj_real_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (t : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((t : ℂ) • v) = t ^ 2 * X.maj x τ v := by
  have hc : conj (t : ℂ) = t := Complex.conj_ofReal t
  have e2 : hermC τ.1 X.Gm ((t : ℂ) • v) ((t : ℂ) • v) = ((t ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_l, hermC_smul_r, hc]; push_cast; ring
  unfold Data.maj Data.posPart
  rw [e2]
  simp_rw [hermC_smul_l (a := (t : ℂ)) (u := v), map_mul, hc]
  rw [scale_lemma, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

lemma continuousAt_maj {r : ℕ} (X : Data E r) (τ : X.Ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → ℂ) :
    ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, v) := by
  have hH : ∀ f g : Frame X.Ψ r × (Fin r → ℂ) → (Fin r → ℂ), Continuous f → Continuous g →
      Continuous fun p => hermC τ.1 X.Gm (f p) (g p) := by
    intro f g hf hg
    unfold hermC
    have hf' : ∀ a, Continuous fun p => f p a := fun a => (continuous_apply a).comp hf
    have hg' : ∀ b, Continuous fun p => g p b := fun b => (continuous_apply b).comp hg
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hf' a).mul continuous_const).mul (Complex.continuous_conj.comp (hg' b))
  have hcol : ∀ k : Fin r, Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => col (mat p.1 τ) k := by
    intro k
    change Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => fun i => p.1 τ i k
    exact continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply τ).comp continuous_fst))
  have hG : Continuous fun y : Frame X.Ψ r => X.gramPos y τ := by
    unfold Data.gramPos
    exact (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_gram X τ).matrix_submatrix _ _
  have hdet : (X.gramPos x τ).det ≠ 0 := (X.gramPos_posDef hx τ).det_pos.ne'
  have hI : ContinuousAt (fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) x := by
    refine (continuousAt_matrix_inv _ ?_).comp hG.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hIab : ∀ a b : Fin X.p0,
      ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹ a b) (x, v) :=
    fun a b => by
      have hI' : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹) (x, v) :=
        ContinuousAt.comp (g := fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) (f := Prod.fst) hI
          continuous_fst.continuousAt
      exact ContinuousAt.comp (g := fun M : Matrix (Fin X.p0) (Fin X.p0) ℂ => M a b)
        (continuous_id.matrix_elem a b).continuousAt hI'
  unfold Data.maj Data.posPart
  refine ContinuousAt.sub (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_))
    (Complex.continuous_re.comp (hH _ _ continuous_snd continuous_snd)).continuousAt
  refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
  exact (((hH _ _ continuous_snd (hcol _)).continuousAt.mul (hIab a b)).mul
    (Complex.continuous_conj.comp (hH _ _ continuous_snd (hcol _))).continuousAt)

lemma exists_sphere {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ w ∈ Metric.sphere (0 : Fin r → ℂ) 1, v = ((‖v‖ : ℝ) : ℂ) • w := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine ⟨((‖v‖ : ℝ) : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hn), one_smul]

lemma maj_at_zero {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC]

lemma ne_zero_of_sphere {r : ℕ} {w : Fin r → ℂ} (hw : w ∈ Metric.sphere (0 : Fin r → ℂ) 1) :
    w ≠ 0 := by
  rintro rfl
  rw [mem_sphere_zero_iff_norm, norm_zero] at hw
  exact zero_ne_one hw

theorem eventually_comparable {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v := by
  have hdom : ∀ᶠ y in 𝓝 x, y ∈ X.dom := (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have key : ∀ τ : X.Ψ, ∀ᶠ y in 𝓝 x, ∀ w ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      X.maj x τ w < (1 + ε) * X.maj y τ w ∧ X.maj y τ w < (1 + ε) * X.maj x τ w := by
    intro τ
    refine (isCompact_sphere (0 : Fin r → ℂ) 1).eventually_forall_of_forall_eventually ?_
    intro w hw
    have hpos : 0 < X.maj x τ w := X.maj_pos hx τ (ne_zero_of_sphere hw)
    have h1 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, w) :=
      continuousAt_maj X τ hx w
    have h2 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj x τ p.2) (x, w) :=
      ContinuousAt.comp_of_eq (g := fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
        (f := fun p : Frame X.Ψ r × (Fin r → ℂ) => (x, p.2)) h1
        (continuous_const.prodMk continuous_snd).continuousAt rfl
    refine (h2.eventually_lt (continuousAt_const.mul h1) ?_).and
      (h1.eventually_lt (continuousAt_const.mul h2) ?_)
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
  filter_upwards [hdom, Filter.eventually_all.2 key] with y hy hk
  refine ⟨hy, fun τ v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hx' : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hy' : X.maj y τ v = ‖v‖ ^ 2 * X.maj y τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X y τ _ w
  obtain ⟨k1, k2⟩ := hk τ w hw
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hx', hy']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left k1.le ht]
  · nlinarith [mul_le_mul_of_nonneg_left k2.le ht]

theorem compact_bounds {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)} (hK : IsCompact K)
    (hKd : K ⊆ X.dom) : ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2 := by
  classical
  have hKS := hK.prod (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hcont : ∀ τ : X.Ψ, ContinuousOn (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
      (K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1) :=
    fun τ => continuousOn_of_forall_continuousAt fun p hp => continuousAt_maj X τ (hKd hp.1) p.2
  have hlow : ∀ τ : X.Ψ, ∃ c', 0 < c' ∧ ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1,
      c' ≤ X.maj p.1 τ p.2 :=
    fun τ => hKS.exists_forall_le' (hcont τ) fun p hp => X.maj_pos (hKd hp.1) τ (ne_zero_of_sphere hp.2)
  have hup : ∀ τ : X.Ψ, ∃ C', ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1, ‖X.maj p.1 τ p.2‖ ≤ C' :=
    fun τ => hKS.exists_bound_of_continuousOn (hcont τ)
  choose cτ hcpos hcle using hlow
  choose Cτ hCle using hup
  have hsum : 0 ≤ ∑ σ, (cτ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hcpos σ)).le
  refine ⟨(1 + ∑ σ, (cτ σ)⁻¹)⁻¹, ∑ σ, |Cτ σ|, inv_pos.2 (by linarith), ?_⟩
  intro x hx τ v
  have hc_le : (1 + ∑ σ, (cτ σ)⁻¹)⁻¹ ≤ cτ τ := by
    have h1 : (cτ τ)⁻¹ ≤ ∑ σ, (cτ σ)⁻¹ :=
      Finset.single_le_sum (f := fun σ => (cτ σ)⁻¹) (fun σ _ => (inv_pos.2 (hcpos σ)).le)
        (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  have hC_le : Cτ τ ≤ ∑ σ, |Cτ σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cτ σ|) (fun σ _ => abs_nonneg _)
      (Finset.mem_univ τ))
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hm : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hlo : cτ τ ≤ X.maj x τ w := hcle τ (x, w) ⟨hx, hw⟩
  have hhi : X.maj x τ w ≤ Cτ τ := (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm.trans_le (hCle τ (x, w) ⟨hx, hw⟩))
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hc_le.trans hlo) ht]
  · nlinarith [mul_le_mul_of_nonneg_left (hhi.trans hC_le) ht]

theorem majorant_continuity :
    ((∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) ∧ (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2)) := ⟨fun _ X _ hx _ hε => eventually_comparable X hx hε,
    fun _ X _ hK hKd => compact_bounds X hK hKd⟩

end GlobalTheory.MajorantContinuity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSelectForms
section
open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix

namespace GlobalTheory.LeviRank

theorem exists_select_forms {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n N : ℕ} (hn : Module.finrank K M = n)
    (φ : Fin N → Module.Dual K M) (hφ : ∀ x, (∀ k, φ k x = 0) → x = 0) :
    ∃ jj : Fin n → Fin N, ∀ x, (∀ k, φ (jj k) x = 0) → x = 0 := by
  classical
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    have : x = 0 := hφ x (fun k => by simpa using (Submodule.mem_iInf _).1 hx k)
    simp [this]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K φ
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    have h := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Subspace.dual_finrank_eq, hn] at h
    exact h.symm
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => a (e.symm k), fun x hx => hφ x fun k => ?_⟩
  have hk : φ k ∈ Submodule.span K (Set.range (φ ∘ a)) := by rw [hsp, hspan]; trivial
  refine Submodule.span_induction (p := fun f _ => f x = 0) ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨i, rfl⟩
    simpa using hx (e i)
  · simp
  · intro f g _ _ hf hg; simp [hf, hg]
  · intro c f _ hf; simp [hf]

theorem wJac_mulVec {n N : ℕ} (w : Fin N → V n → ℂ) (x : V n)
    (hw : ∀ k, DifferentiableAt ℂ (w k) x) (ξ : V n) (k : Fin N) :
    (wJac n N w x *ᵥ ξ.ofLp) k = fderiv ℂ (w k) x ξ := by
  have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
    ext i
    simp [bas, Pi.single_apply]
  conv_rhs => rw [hξ]
  simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hw k), map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem main : ∀ (n N : ℕ) (w : Fin N → V n → ℂ) (U : Set (V n)), IsOpen U → (0 : V n) ∈ U →
    (∀ k, DifferentiableOn ℂ (w k) U) → (∃ k, w k 0 ≠ 0) →
    (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re) →
    ∃ (j0 : Fin N) (jj : Fin n → Fin N), w j0 0 ≠ 0 ∧
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0).det ≠ 0 := by
  intro n N w U hU h0 hw ⟨j0, hj0⟩ hL
  have hC : ∀ k, ContDiffAt ℂ 2 (w k) 0 := fun k =>
    ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).contDiffAt (hU.mem_nhds h0)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hD : ∀ k, DifferentiableAt ℂ (w k) 0 := fun k => (hw k).differentiableAt (hU.mem_nhds h0)
  have hne : (fun i => w i 0) ≠ 0 := fun h => hj0 (congrFun h j0)
  have hQ : ∀ k, DifferentiableAt ℂ (fun z => w k z / w j0 z) 0 := fun k => by
    simp only [div_eq_mul_inv]
    exact (hD k).mul ((differentiableAt_inv hj0).comp (0 : V n) (hD j0))
  have hker : ∀ x : V n, (∀ k, fderiv ℂ (fun z => w k z / w j0 z) 0 x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hξ : x.ofLp ≠ 0 := fun h => hx0 (by ext i; simpa using congrFun h i)
    have h1 := hL _ hξ
    have e1 : (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) =
        fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
      funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
    rw [e1, leviLogNormSq n N w 0 x.ofLp hC hne] at h1
    have hJ : wJac n N w 0 *ᵥ x.ofLp = (fderiv ℂ (w j0) 0 x / w j0 0) • fun i => w i 0 := by
      funext k
      rw [wJac_mulVec w 0 hD]
      have hev : w k =ᶠ[𝓝 0] fun z => (w k z / w j0 z) * w j0 z := by
        filter_upwards [(hD j0).continuousAt.eventually_ne hj0] with z hz
        rw [div_mul_cancel₀ _ hz]
      rw [hev.fderiv_eq, fderiv_fun_mul (hQ k) (hD j0)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hx k, smul_eq_mul,
        Pi.smul_apply]
      ring
    have hs : ((sqNorm (fun i => w i 0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (sqNorm_pos hne).ne'
    have hP : projPerp (fun i => w i 0) *ᵥ (fun i => w i 0) = 0 := by
      rw [projPerp_mulVec, star_dotProduct_self, inv_mul_cancel₀ hs, one_smul, sub_self]
    rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at h1
    simp [sqNorm] at h1
  obtain ⟨jj, hjj⟩ := exists_select_forms (K := ℂ) (M := V n) (n := n) (by simp)
    (fun k => (fderiv ℂ (fun z => w k z / w j0 z) 0 : V n →L[ℂ] ℂ).toLinearMap) hker
  refine ⟨j0, jj, hj0, ?_⟩
  have hF : DifferentiableAt ℂ
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 :=
    differentiableAt_euclidean.2 fun k => hQ (jj k)
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot']
  intro x hx
  refine hjj x fun k => ?_
  have h2 := ((EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ).hasFDerivAt.comp (0 : V n)
    hF.hasFDerivAt).fderiv
  have h3 : (fun z => w (jj k) z / w j0 z) = (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) ∘
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) := rfl
  change fderiv ℂ (fun z => w (jj k) z / w j0 z) 0 x = 0
  rw [h3, h2, ContinuousLinearMap.comp_apply]
  change (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) (((fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) x) = 0
  rw [hx, map_zero]

end GlobalTheory.LeviRank
end

