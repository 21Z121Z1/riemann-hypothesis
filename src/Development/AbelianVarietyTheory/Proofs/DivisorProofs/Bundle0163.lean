import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpNegHermitianFormPosDef
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.GaussHerm

lemma finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

lemma det_toEuclideanLin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Matrix.toEuclideanLin C) = C.det := by
  have : Matrix.toEuclideanLin C = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis C := by
    ext v i : 2
    simp [Matrix.toLin_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.single_apply, Pi.single_apply]
  rw [this, LinearMap.det_toLin]

lemma quad_eq {n : ℕ} (H C : Matrix (Fin n) (Fin n) ℂ) (hC : H.transpose = C.conjTranspose * C)
    (w : V n) :
    (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re = ‖Matrix.toEuclideanLin C w‖ ^ 2 := by
  have hH : ∀ j l, H j l = ∑ k, (starRingEnd ℂ) (C k l) * C k j := by
    intro j l
    have := congrFun (congrFun hC l) j
    simpa [Matrix.mul_apply] using this
  have hc : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)) =
      ∑ k, (∑ j, C k j * w j) * (starRingEnd ℂ) (∑ l, C k l * w l) := by
    simp only [hH, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun j _ => by ring)))
  rw [hc, EuclideanSpace.norm_sq_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

theorem exists_eq_conjTranspose_mul_self {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, T = B.conjTranspose * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

theorem integral_exp_neg_herm : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧
    ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) =
      Real.pi ^ n / H.det.re := by
  intro n H hH
  have hT : H.transpose.PosDef := Matrix.PosDef.transpose_iff.mpr hH
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hT.posSemidef
  set L : V n →ₗ[ℝ] V n := (Matrix.toEuclideanLin C).restrictScalars ℝ with hL
  have hdetL : LinearMap.det L = Complex.normSq C.det := by
    rw [hL, LinearMap.det_restrictScalars, det_toEuclideanLin, Algebra.norm_complex_apply]
  have hdetC : H.det = (Complex.normSq C.det : ℂ) := by
    rw [← Matrix.det_transpose H, hC, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      mul_comm, Complex.mul_conj]
  have hdetH : H.det.re = Complex.normSq C.det := by rw [hdetC, Complex.ofReal_re]
  have hpos : 0 < Complex.normSq C.det := by
    have := hH.det_pos
    rwa [hdetC, Complex.zero_lt_real] at this
  set g : V n → ℝ := fun v => Real.exp (-1 * ‖v‖ ^ 2) with hg
  have hf : (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) =
      fun w => g (L w) := by
    funext w
    rw [quad_eq H C hC w, hg]
    simp [hL]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (V n)) (f := L)
    (by rw [hdetL]; exact hpos.ne')
  have hG : ∫ v : V n, g v = Real.pi ^ n := by
    rw [hg, GaussianFourier.integral_rexp_neg_mul_sq_norm one_pos, finrank_V, div_one]
    rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hI : ∫ w : V n, g (L w) = Real.pi ^ n / H.det.re := by
    rw [← integral_map (L.continuous_of_finiteDimensional.aemeasurable)
      hgc.aestronglyMeasurable, hmap, integral_smul_measure, hG, hdetL, hdetH,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hpos), smul_eq_mul,
      div_eq_inv_mul]
  rw [hf]
  refine ⟨Integrable.of_integral_ne_zero ?_, hI⟩
  rw [hI, hdetH]
  exact (div_pos (pow_pos Real.pi_pos n) hpos).ne'

end GlobalTheory.GaussHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGauTwistedConv
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}

theorem integral_gau_twisted_conv (hJ : ∀ x, J (J x) = -x) (a y : V) :
    ∫ u, gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ))) = gau a * gau y := by
  set m : V := (1 / 2 : ℝ) • (y - a) with hm
  have hym : y - a = m + m := by
    rw [hm, ← add_smul]; norm_num
  have hself : ∀ x : V, ⟪x, J x⟫ = 0 := by
    intro x
    have := omJ_skew hJ x x
    unfold omJ at this
    linarith
  have hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫ := fun x z => by
    have := omJ_skew hJ x z
    unfold omJ at this
    exact this
  have hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) *
      cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) =
      cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2) := by
    intro v
    have e1 : y - (v + m + a) = m - v := by
      have hy : y = m + m + a := by rw [← hym]; abel
      rw [hy]; abel
    have h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      rw [e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]; ring
    have h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫ := by
      unfold omJ
      rw [real_inner_comm v (J (a + y)), hm]
      simp only [map_add, inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]
      have h3 := hsk a y
      have h4 := hself a
      have h5 := hself y
      linarith
    have h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2 := by
      have h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2 := by linarith
      exact_mod_cast h6
    simp only [gau, ← Complex.exp_add]
    congr 1
    rw [h1c, h2]
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure V))
    (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m
  rw [← hshift]
  simp only [hpt]
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul,
    LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow,
      norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]
    ring
  have h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4 := by
    exact_mod_cast h3
  rw [h3c, mul_pow, I_sq]
  field_simp
  ring

theorem proj_heis_proj {ρ : V → B →L[ℂ] B} (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a : V) (f : B) :
    proj h (ρ a (proj h f)) = gau a • proj h f := by
  have hself : ∀ x : V, omJ J x x = 0 := fun x => by
    have := omJ_skew hJ x x
    linarith
  set F : V → V → B := fun u z =>
    (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF
  have hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z := by
    intro u
    rw [h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul,
      ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]
    congr 1
    ext w
    have hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w := by
      have h0 := hself (u + a)
      unfold omJ at h0 ⊢
      rw [map_add, inner_add_right, h0, add_zero]
    show _ = (gau u * (gau (w + (u + a) - (u + a)) *
      cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f
    rw [add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖) := by
    intro u z
    simp only [hF, norm_smul, norm_mul, h.2.2.1]
    rw [he, mul_one, mul_assoc]
  have hom : Continuous fun p : V × V => omJ J p.1 p.2 := by
    unfold omJ
    exact continuous_fst.inner (J.continuous.comp continuous_snd)
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) *
      cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f
    refine Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)
    refine (continuous_gau.comp continuous_fst).mul
      ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (hom.comp (continuous_fst.prodMk continuous_const)).add
      (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u => ?_
      have hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume :=
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      rw [← integrable_norm_iff hm]
      simp only [Function.uncurry_apply_pair, hnorm]
      exact (((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖
    · simp only [Function.uncurry_apply_pair, hnorm]
      simp only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]
      exact (integrable_gau (V := V)).norm.mul_const _
  rw [proj_apply h (ρ a (proj h f))]
  simp_rw [hin]
  rw [integral_integral_swap hint]
  have hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f := by
    intro z
    simp only [hF]
    rw [integral_smul_const, integral_gau_twisted_conv hJ a z]
  simp_rw [hinner]
  rw [proj_apply h f, ← integral_smul]
  congr 1
  ext z
  rw [smul_smul]

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMemFinDimSubspace
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_mem_span_eval_of_finiteDimensional {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) :=
  _root_.UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional E φ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRowSpaceBasisExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_row_space_basis_exists : ∀ (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k), (∀ c, Matrix.vecMul c P = 0 → c = 0) → ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  first | exact @GlobalTheory.exists_basis_matrix_of_integral_preimage | exact GlobalTheory.exists_basis_matrix_of_integral_preimage | (intros; apply GlobalTheory.exists_basis_matrix_of_integral_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFromPadicNormBound
section
open NumberField Polynomial

namespace GlobalTheory

def unitBallSubring (A : Type) [NormedField A] [IsUltrametricDist A] : Subring A :=
  GlobalTheory.ClosedBallValuationSubring.closedBallSubring A

theorem den_eq_one_of_padicNorm_le_one (c : ℚ)
    (h : ∀ q : ℕ, q.Prime → padicNorm q c ≤ 1) : c.den = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  haveI := Fact.mk hq
  have hc : c ≠ 0 := by
    rintro rfl; simp at hne
  have h1 := h q hq
  rw [padicNorm.eq_zpow_of_nonzero hc] at h1
  have hv : 0 ≤ padicValRat q c := by
    by_contra hlt
    push_neg at hlt
    have hq1 : (1 : ℚ) < q := by exact_mod_cast hq.one_lt
    have : (1 : ℚ) < (q : ℚ) ^ (-padicValRat q c) := one_lt_zpow₀ hq1 (by omega)
    linarith
  have hden : 1 ≤ padicValNat q c.den :=
    one_le_padicValNat_of_dvd c.den_nz hqd
  have hnum : padicValInt q c.num = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdvd
    have hcop := c.reduced
    have : q ∣ Nat.gcd c.num.natAbs c.den :=
      Nat.dvd_gcd (Int.natCast_dvd.mp hdvd) hqd
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  unfold padicValRat at hv
  omega

theorem isIntegral_of_forall_padicAlgCl_norm_le_one :
    ∀ (M : Type) [Field M] [NumberField M] (a : M),
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ a‖ ≤ 1) → IsIntegral ℤ a := by
  intro M _ _ a h
  set f := minpoly ℚ a with hf
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hmon : f.Monic := minpoly.monic hint
  have hcoeff : ∀ q : ℕ, q.Prime → ∀ n, padicNorm q (f.coeff n) ≤ 1 := by
    intro q hq n
    haveI := Fact.mk hq
    let S := unitBallSubring (PadicAlgCl q)
    set g := f.map (algebraMap ℚ (PadicAlgCl q)) with hg
    have hroots : ∀ b ∈ g.roots, b ∈ S := by
      intro b hb
      have hb' : b ∈ f.rootSet (PadicAlgCl q) := by
        rw [Polynomial.mem_rootSet]
        obtain ⟨hne, hr⟩ := (mem_roots'.mp hb)
        refine ⟨fun h0 => hne (by rw [hg, h0, Polynomial.map_zero]), ?_⟩
        rw [← eval_map_algebraMap]; exact hr
      rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly] at hb'
      obtain ⟨τ, rfl⟩ := hb'
      exact h q τ
    have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
    have hgmon : g.Monic := hmon.map _
    have hgc : g.coeff n ∈ S := by
      by_cases hn : n ≤ g.natDegree
      · rw [coeff_eq_esymm_roots_of_card hcard hn, hgmon.leadingCoeff, one_mul]
        refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
        unfold Multiset.esymm
        refine S.multiset_sum_mem _ fun x hx => ?_
        obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
        refine S.multiset_prod_mem _ fun y hy => hroots y ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp hs).1 hy
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact S.zero_mem
    have h1 : ‖algebraMap ℚ (PadicAlgCl q) (f.coeff n)‖ ≤ 1 := by
      rw [← coeff_map]; exact hgc
    have e : algebraMap ℚ (PadicAlgCl q) (f.coeff n) =
        ((f.coeff n : ℚ_[q]) : PadicAlgCl q) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm] at h1
    exact_mod_cast h1
  have hlift : f ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨(f.coeff n).num, ?_⟩
    have := den_eq_one_of_padicNorm_le_one _ (fun q hq => hcoeff q hq n)
    simpa using Rat.coe_int_num_of_den_eq_one this
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨g, hgm, ?_⟩
  have h0 : aeval a f = 0 := minpoly.aeval ℚ a
  rw [← hg, ← algebraMap_int_eq, aeval_map_algebraMap] at h0
  exact h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerFixesOfLocalVacuum
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem intertwiner_fixes_of_local_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M)
    (hT : ∀ x v, T (W x v) = W (φ x) (T v)) (hTe : ∀ e, Fixes W A e → T e = e) (P : X →ₗ[R] X)
    (hP : ∀ x y, γ (P x) y = γ x (P y)) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ x, φ (x - P x) = x - P x)
    (m : M) (hm : ∀ a ∈ A, W (P a) m = m) : T m = m := by
  have hsm : ∀ (c : ℂ) e, Fixes W A e → Fixes W A (c • e) := fun c e he a ha => by rw [map_smul, he a ha]
  have key : ∀ {ι : Type} (x : ι → X) (s : Finset ι) (e : ι → M), (∀ i, Fixes W A (e i)) →
      (∀ a ∈ A, W (P a) (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i)) →
      T (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i) := by
    intro ι x s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro e he hfix
      by_cases hall : ∀ i ∈ s, P (x i) ∈ A
      · rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h1 := h.comp (x i - P (x i)) (P (x i)) (e i)
        rw [he i _ (hall i hi), sub_add_cancel] at h1
        have h2 : T (W (x i - P (x i)) (e i)) = W (x i - P (x i)) (e i) := by rw [hT, hφ, hTe _ (he i)]
        rw [h1, map_smul] at h2
        exact smul_right_injective M (h.ne_zero _ _) h2
      · push Not at hall
        obtain ⟨j, hj, hjA⟩ := hall
        rw [hA] at hjA
        push Not at hjA
        obtain ⟨a, ha, hz⟩ := hjA
        have hz' : γ (P a) (x j) ≠ 1 := by
          intro h0
          rw [hP] at h0
          exact hz (h.swap_eq_one h0)
        set z := γ (P a) (x j) with hzdef
        have hact : ∀ i, W (P a) (W (x i) (e i)) = γ (P a) (x i) • W (x i) (e i) := fun i => by
          rw [h.comm, he i _ (hPA a ha)]
        have hsum : (1 - z) • ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s.erase j, W (x i) ((γ (P a) (x i) - z) • e i) := by
          rw [Finset.sum_erase s (by simp [hzdef]), sub_smul, one_smul]
          have h4 : ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) := by
            rw [← hfix a ha, map_sum]
            exact Finset.sum_congr rfl fun i _ => hact i
          calc _ = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) - ∑ i ∈ s, z • W (x i) (e i) := by
                rw [← h4, Finset.smul_sum]
            _ = _ := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ => by rw [map_smul, sub_smul]
        have h3 := ih (s.erase j) (Finset.erase_ssubset hj) (fun i => (γ (P a) (x i) - z) • e i)
          (fun i => hsm _ _ (he i)) (fun b hb => by rw [← hsum, map_smul, hfix b hb])
        rw [← hsum, map_smul] at h3
        exact smul_right_injective M (sub_ne_zero.2 hz'.symm) h3
  have hmem : m ∈ Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} := by rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  choose x e he hge using fun i => (g i).2
  have hm' : m = ∑ i, W (x i) (c i • e i) := by
    rw [← hg]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hge i]
  rw [hm'] at hm ⊢
  exact key x Finset.univ _ (fun i => hsm _ _ (he i)) hm

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimesStatement
section
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_five_log_le_sum_inv_primes_half_interval : ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤ ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p := by
  first | exact @GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes | exact GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes | (intros; apply GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_mem_identity_component_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left), y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.inv_mem_connectedComponentIn_fibre | exact GlobalTheory.inv_mem_connectedComponentIn_fibre | (intros; apply GlobalTheory.inv_mem_connectedComponentIn_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactorStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_norm_class_remove_rational_factor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  first | (exact @GlobalTheory.RatRed.ratred) | (exact GlobalTheory.RatRed.ratred) | (intros; apply GlobalTheory.RatRed.ratred  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrCharOneMulFinsumConjMul
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem exists_sum_conj_eq_smul_one {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x : G) :
    ∃ c : ℂ, ∑ h : G, ρ (h * x * h⁻¹) = c • (1 : Module.End ℂ V) := by
  have hc : ∀ g : G, (∑ h : G, ρ (h * x * h⁻¹)) * ρ g = ρ g * ∑ h : G, ρ (h * x * h⁻¹) := by
    intro g
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_).symm
    rw [← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := ∑ h : G, ρ (h * x * h⁻¹)
      isIntertwining' := fun g => hc g }
  obtain ⟨c, hT⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 T
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  change T v = c • v
  rw [← hT, Algebra.algebraMap_eq_smul_one]
  rfl

theorem character_one_mul_sum_conj_mul {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x y : G) :
    ρ.character 1 * ∑ h : G, ρ.character (h * x * h⁻¹ * y)
      = (Fintype.card G : ℂ) * (ρ.character x * ρ.character y) := by
  obtain ⟨c, hc⟩ := exists_sum_conj_eq_smul_one ρ x
  have key : ∀ z : G, ∑ h : G, ρ.character (h * x * h⁻¹ * z) = c * ρ.character z := by
    intro z
    have := congrArg (fun A => LinearMap.trace ℂ V (A * ρ z)) hc
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, ← map_mul] at this
    exact this
  have h1 := key 1
  simp only [mul_one, Representation.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [key y, ← mul_assoc, mul_comm _ c, ← h1, mul_assoc]

theorem irrChar_one_mul_finsum_conj_mul : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsIrrChar ℂ ℂ χ → ∀ x y : G, χ 1 * ∑ᶠ h : G, χ (h * x * h⁻¹ * y) = (Nat.card G : ℂ) * (χ x * χ y) := by
  intro G _ _ χ hχ x y
  let := Fintype.ofFinite G
  obtain ⟨n, ρ, hρ, h⟩ := hχ
  have hh : χ = ρ.character := by
    funext g
    simpa using h g
  subst hh
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  exact character_one_mul_sum_conj_mul ρ x y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I J : Ideal R), I ≤ J → IsAdicComplete J R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | exact GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | (intros; apply GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing <;> assumption)
end

