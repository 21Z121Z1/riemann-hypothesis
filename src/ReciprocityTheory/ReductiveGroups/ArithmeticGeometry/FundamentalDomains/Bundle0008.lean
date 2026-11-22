import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralTraceNormBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds

open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

lemma cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma cc_two : cc (2 : E) = 2 := by
  unfold cc
  exact map_ofNat _ 2

lemma inner_iota_eq_trace (x y : E) :
    inner ℝ (iota E x) (iota E y) = (1 / 2 : ℝ) * (Algebra.trace ℚ E (x * cc y) : ℝ) := by
  rw [inner_iota, ← sum_re_eq_trace]
  apply Finset.sum_congr rfl
  intro w _
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj]

variable (E) in

noncomputable def ed : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate (K := ℚ) (L := E)) (integralBasis E)

lemma trace_ed (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (integralBasis E i * ed E j) = if i = j then 1 else 0 := by
  rw [← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm ℚ) _ i j

variable (E) in

noncomputable def bd (j : Free.ChooseBasisIndex ℤ (𝓞 E)) : VS E := iota E (2 * cc (ed E j))

lemma inner_bas_bd (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    inner ℝ (bas E i) (bd E j) = if i = j then 1 else 0 := by
  rw [bas_apply, bd, inner_iota_eq_trace, cc_mul, cc_cc, cc_two]
  have h2 : integralBasis E i * (2 * ed E j) = (2 : ℚ) • (integralBasis E i * ed E j) := by
    rw [Algebra.smul_def, map_ofNat]
    ring
  rw [h2, LinearMap.map_smul, trace_ed]
  split_ifs <;> norm_num

lemma trace_int (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed E j) * (γ : E)) = m := by
  obtain ⟨m, hm⟩ : ∃ m : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
      (γ : E) = ∑ i, m i • integralBasis E i := by
    refine ⟨(RingOfIntegers.basis E).repr γ, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr γ]
    simp [integralBasis_apply]
  have key : ∀ j i, Algebra.trace ℚ E ((c j • ed E j) * (m i • integralBasis E i)) =
      if i = j then ((c j * m i : ℤ) : ℚ) else 0 := by
    intro j i
    rw [smul_mul_smul_comm, map_zsmul, mul_comm (ed E j), trace_ed]
    split_ifs <;> simp
  refine ⟨∑ j, c j * m j, ?_⟩
  rw [hm, Finset.sum_mul_sum, map_sum]
  simp_rw [map_sum, key]
  simp [Finset.sum_ite_eq']

lemma norm_discr (β : E) (hβ : β ≠ 0)
    (hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * (γ : E)) = m) :
    1 ≤ |(Algebra.norm ℚ β : ℝ)| * dE E := by
  choose m hm using fun i j => hint (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
  have hbB : ∀ i, integralBasis E i = ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [integralBasis_apply]
  have hP : Matrix.of (fun i j => ((m i j : ℤ) : ℚ)) =
      Algebra.traceMatrix ℚ (integralBasis E) * Algebra.leftMulMatrix (integralBasis E) β := by
    ext i j
    rw [Matrix.of_apply, ← hm i j, Matrix.mul_apply]
    have e : β * ((RingOfIntegers.basis E i * RingOfIntegers.basis E j : 𝓞 E) : E) =
        integralBasis E i * (β * integralBasis E j) := by
      rw [hbB, hbB]
      push_cast
      ring
    rw [e]
    conv_lhs => rw [← (integralBasis E).sum_repr (β * integralBasis E j)]
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    ring
  have h1 : ((Matrix.of m).det : ℚ) = (Matrix.of (fun i j => ((m i j : ℤ) : ℚ))).det := by
    rw [show ((Matrix.of m).det : ℚ) = (Int.castRingHom ℚ) (Matrix.of m).det from rfl,
      RingHom.map_det]
    rfl
  have hdet : ((Matrix.of m).det : ℚ) = (NumberField.discr E : ℚ) * Algebra.norm ℚ β := by
    rw [h1, hP, Matrix.det_mul, NumberField.coe_discr, Algebra.discr_def,
      Algebra.norm_eq_matrix_det (integralBasis E)]
  have hN0 : Algebra.norm ℚ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
  have hD0 : (NumberField.discr E : ℚ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hZ : (Matrix.of m).det ≠ 0 := by
    intro h
    have h0 : ((Matrix.of m).det : ℚ) = 0 := by rw [h]; simp
    rw [hdet] at h0
    exact mul_ne_zero hD0 hN0 h0
  have hR : ((Matrix.of m).det : ℝ) =
      ((NumberField.discr E : ℤ) : ℝ) * ((Algebra.norm ℚ β : ℚ) : ℝ) := by
    have h2 := congrArg (Rat.cast : ℚ → ℝ) hdet
    simp only [Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2
  unfold dE
  rw [← abs_mul, mul_comm, ← hR]
  exact_mod_cast Int.one_le_abs hZ

lemma prod_norm (β : E) :
    ∏ w : CP E, ‖w.1.embedding β‖ ^ 2 = |(Algebra.norm ℚ β : ℝ)| := by
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm,
    ← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace E => IsTotallyComplex.isComplex w)).prod_comp]
  apply Finset.prod_congr rfl
  intro w _
  rw [InfinitePlace.norm_embedding_eq]
  change w.1 β ^ 2 = w.1 β ^ w.1.mult
  rw [InfinitePlace.mult_isComplex]

lemma dE_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)

lemma card_complexPlaces_pos : 0 < Fintype.card (CP E) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact Fintype.card_pos_iff.mpr ⟨⟨w, IsTotallyComplex.isComplex w⟩⟩

lemma norm_bd_ge (x : VS E) (hx : x ∈ span ℤ (Set.range (bd E))) (hx0 : x ≠ 0) :
    4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤ ‖x‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  obtain ⟨β, hβdef⟩ : ∃ β : E, β = ∑ j, c j • ed E j := ⟨_, rfl⟩
  have hxβ : x = iota E (2 * cc β) := by
    rw [← hc, hβdef]
    simp only [bd, cc, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
  have hβ0 : β ≠ 0 := by
    rintro h
    apply hx0
    rw [hxβ, h, cc, map_zero, mul_zero, map_zero]
  have hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * γ) = m := by
    intro γ
    rw [hβdef]
    exact trace_int c γ
  have hN := norm_discr β hβ0 hint
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnorm : ‖x‖ ^ 2 = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
    rw [hxβ, norm_sq_iota, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [map_mul, norm_mul, cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj,
      map_ofNat, h2n]
    ring
  have hn : (0 : ℝ) < Fintype.card (CP E) := by exact_mod_cast card_complexPlaces_pos
  have hd : 0 < dE E := dE_pos
  have hNinv : (dE E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (CP E))
    (fun _ => 1 / (Fintype.card (CP E) : ℝ)) (fun w => ‖w.1.embedding β‖ ^ 2)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  rw [Real.finset_prod_rpow _ _ (fun _ _ => by positivity), prod_norm, ← Finset.mul_sum] at hgm
  have h1 : dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤
      |(Algebra.norm ℚ β : ℝ)| ^ (1 / (Fintype.card (CP E) : ℝ)) := by
    rw [Real.rpow_neg hd.le, ← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hd.le) hNinv (by positivity)
  rw [hnorm]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans hgm)
    (by positivity : (0 : ℝ) ≤ 4 * (Fintype.card (CP E) : ℝ))
  calc 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ)))
      ≤ 4 * (Fintype.card (CP E) : ℝ) *
        (1 / (Fintype.card (CP E) : ℝ) * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2) := h3
    _ = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
      rw [← mul_assoc, mul_assoc 4, mul_one_div_cancel hn.ne', mul_one]

end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
section
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem hG_of (τ : X.Ψ) : ∀ a b, τ.1 (X.Gm b a) = conj (τ.1 (X.Gm a b)) := by
  intro a b
  rw [← X.Gm_herm a b]
  first
    | simp [NumberField.IsCMField.complexEmbedding_complexConj]
    | rw [NumberField.IsCMField.complexEmbedding_complexConj]
    | simp [NumberField.IsCMField.complexConj_apply]
    | simp [NumberField.IsCMField.conj_complexEmbedding]
    | (simp only [cc]
       exact NumberField.IsCMField.complexEmbedding_complexConj ..)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : (τ.1 X.ξ0) ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  have := norm_pos_iff.mpr h
  linarith

theorem hsg_of {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∀ i (h : i ≤ r), 0 < psgn X.p0 i * (gramF τ.1 X.Gm (famN (mat x τ) i h)).det.re := by
  intro i h
  unfold Data.dom GG at hx
  simp only [Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 ⟨i, Nat.lt_succ_of_le h⟩
  first
    | exact h1
    | (unfold dmin lminor gram gramF famN at h1
       exact h1)

theorem dmin_eq (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = (gramF τ.1 X.Gm (famN (mat x τ) i (Nat.le_of_lt_succ i.isLt))).det := rfl

theorem famN_flow (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ)
    (h : i ≤ r) : famN (mat (X.flowV e s x) τ) i h =
      flw (-I * X.c τ * s τ) (e τ) τ.1 X.Gm (famN (mat x τ) i h) := by
  unfold Data.flowV flw famN mat
  funext a c
  show ∑ b, X.flowMatV (e τ) τ (s τ) c b * x τ b (Fin.castLE h a) =
    x τ c (Fin.castLE h a) + (-I * (X.c τ : ℂ) * s τ *
      hermC τ.1 X.Gm (fun d => x τ d (Fin.castLE h a)) (e τ)) * e τ c
  unfold Data.flowMatV hermC
  simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem alpha_re (c : ℝ) (s : ℂ) : (-I * (c : ℂ) * s) + conj (-I * (c : ℂ) * s) =
    ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

theorem det_flowMat (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (he : hermC τ.1 X.Gm e e = 0) :
    (X.flowMatV e τ s).det = 1 := by
  unfold Data.flowMatV hermC at *
  have key : (of fun a b => (if a = b then (1 : ℂ) else 0) - I * (X.c τ : ℂ) * s * e a *
      ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) =
      1 + replicateCol Unit (fun a => -(I * (X.c τ : ℂ) * s * e a)) *
        replicateRow Unit (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) := by
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, sub_eq_add_neg]
  have hd : (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
      (fun a => -(I * (X.c τ : ℂ) * s * e a)) = 0 := by
    calc (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
          (fun a => -(I * (X.c τ : ℂ) * s * e a))
        = -(I * (X.c τ : ℂ) * s) * ∑ a, ∑ b, e a * τ.1 (X.Gm a b) * (starRingEnd ℂ) (e b) := by
          simp only [dotProduct]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by rw [he, mul_zero]
  rw [key, det_one_add_replicateCol_mul_replicateRow, hd, add_zero]

section Prof
variable {x : Frame X.Ψ r} (hx : x ∈ X.dom) (e : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
include hx

theorem mt_famN (i : ℕ) (h : i ≤ r) : GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) i h) (e τ) =
    (mN τ.1 X.Gm (mat x τ) (e τ) i : ℂ) := by
  rw [mt_eq (hG_of X τ) _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h), mN, pN, dif_pos h]
  exact Complex.ext rfl (by simp [hC_self_real (hG_of X τ)])

theorem dmin_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ) (i : ℕ) (h : i ≤ r) :
    (gramF τ.1 X.Gm (famN (mat (X.flowV e s x) τ) i h)).det =
      (gramF τ.1 X.Gm (famN (mat x τ) i h)).det *
        ((1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i : ℝ) : ℂ) := by
  rw [famN_flow, det_flw (hG_of X τ) (e τ) he _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h),
    mt_famN X hx e τ i h, alpha_re]
  push_cast; ring

theorem maj_eq (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) :
    X.maj x τ (e τ) = 2 * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have : X.posPart x τ (e τ) = (GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, this, mt_famN X hx e τ X.p0 X.p0_le, he, Complex.ofReal_re, Complex.zero_re, sub_zero]

theorem maj_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ)
    (h1 : 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 ≠ 0) :
    X.maj (X.flowV e s x) τ (e τ) = 2 * (mN τ.1 X.Gm (mat x τ) (e τ) X.p0 /
      (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0)) := by
  have hα := alpha_re (X.c τ) (s τ)
  have hp : X.posPart (X.flowV e s x) τ (e τ) =
      (GramDeterminantReal.mt τ.1 X.Gm (famN (mat (X.flowV e s x) τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, hp, famN_flow, mt_flw (hG_of X τ) (e τ) he _ _
    (unit_of X.p0 (mat x τ) (hsg_of X hx τ) X.p0 X.p0_le), hα, mt_famN X hx e τ X.p0 X.p0_le, he,
    Complex.zero_re, sub_zero]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div,
      Complex.ofReal_re]
  · rw [hα, mt_famN X hx e τ X.p0 X.p0_le, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_add]
    exact_mod_cast h1

end Prof

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
section
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_kappa (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring

lemma transvMat_mul (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel

lemma transvMat_zero (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]

lemma transvMat_pow (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α : E) (n : ℕ) : transvMat G ξ α ^ n = transvMat G ξ (n * α) := by
  induction n with
  | zero => simp [transvMat_zero]
  | succ k ih =>
    rw [pow_succ, ih, transvMat_mul G hξ]
    congr 1
    push_cast
    ring

lemma transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by
  ext a b
  simp only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]
  split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring

variable (X : Data E r)

def cR (p : X.Ψ → ℝ) : X.Ψ → ℂ := fun τ => (p τ : ℂ)

lemma flow_real_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (y : Frame X.Ψ r)
    (hy : y ∈ X.dom) : X.flow ξ (cR X p) y ∈ X.dom := by
  have h0 := (flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)
  have e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im := by
    funext τ
    simp [cR]
  rw [flow_mem_dom_iff X hξ y hy, e]
  exact h0

lemma chi_pow (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]

lemma sec_periodic_gen (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a)
    (y : Frame X.Ψ r) (hy : y ∈ X.dom) :
    P (X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y) = P y := by
  obtain ⟨γ0, hγ0, hγ0m⟩ := X.transv ξ hξΛ hξ a ha hai
  have hγ : γ0 ^ X.chiOrd la ∈ X.Γ := X.Γ.pow_mem hγ0 _
  have hχ : X.χ la (γ0 ^ X.chiOrd la) = 1 := by
    rw [chi_pow X la hγ0]
    exact (X.χ_fin la).choose_spec.2 γ0 hγ0
  have hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) := by
    rw [Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]

  have hlact : lact (γ0 ^ X.chiOrd la) y =
      X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y := by
    funext τ
    have hta : τ.1 a = ((τ.1 a).re : ℂ) := by
      have h := emb_cc' τ.1 a
      rw [ha] at h
      apply Complex.ext
      · simp
      · have := congrArg Complex.im h
        simp at this
        simp
        linarith
    have hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) =
        -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ) := by
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]
      conv_lhs => rw [hta]
      simp only [cR]
      push_cast
      ring
    simp only [lact, Data.flow]
    rw [hmat, transvMat_map X ξ τ _ _ hs]
  rw [← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]

lemma cR_add (p q : X.Ψ → ℝ) : cR X (p + q) = cR X p + cR X q := by
  funext τ
  simp [cR]

lemma cR_neg (p : X.Ψ → ℝ) : cR X (-p) = -cR X p := by
  funext τ
  simp [cR]

lemma cR_zero : cR X 0 = 0 := by
  funext τ
  simp [cR]

lemma sec_periodic (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) :
    ∀ y ∈ X.dom, P (X.flow ξ (cR X p) y) = P y := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨a, ha, hai, rfl⟩ := hp
    exact fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy
  | zero =>
    intro y _
    rw [cR_zero, flow_zero]
  | add p q _ _ hp hq =>
    intro y hy
    rw [cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]
  | neg p _ hp =>
    intro y hy
    have hz := flow_real_mem_dom X hξ (-p) y hy
    have e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y := by
      rw [flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]
    rw [← hp _ hz, e]

end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
end

