import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
section
noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

def TraceOpen (R : Type) [CommRing R] [TopologicalSpace R] (a b : R) : Prop :=
  ∀ g : ℍ[R, a, b], nrm g = 1 → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g →
    ∃ O : Set R, IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t

def SqOpen (K : Type) [Monoid K] [TopologicalSpace K] : Prop :=
  ∀ V ∈ 𝓝 (1 : K), ∃ U ∈ 𝓝 (1 : K), ∀ r ∈ U, ∃ μ ∈ V, μ ^ 2 = r

end GlobalTheory.QSA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFiniteStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_open_subgroups_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @GlobalTheory.LocalBoxIndicator.indicator_box_translate | exact GlobalTheory.LocalBoxIndicator.indicator_box_translate | (intros; apply GlobalTheory.LocalBoxIndicator.indicator_box_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCharacterInvariantForm
section
open MeasureTheory

namespace GlobalTheory.CharMult

theorem multiplier_symm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  intro V _ _ _ μ hμ T hT m f f' g g' hf' hg'
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨d, A, h, hm⟩ := GlobalTheory.T.schwartz_fourier_representation V m
  obtain ⟨Φf, hΦf, cΦf, bΦf⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ A f
  obtain ⟨Φg, hΦg, cΦg, bΦg⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ (-A) g
  obtain ⟨Λ1, hΛ1⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T g)
  obtain ⟨Λ2, hΛ2⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T f)
  have hint : ∀ (Φ : EuclideanSpace ℝ (Fin d) → SchwartzMap V ℂ), Continuous Φ →
      (∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n)) →
      ∀ (c : EuclideanSpace ℝ (Fin d) → ℂ), (∀ ξ, ‖c ξ‖ = ‖h ξ‖) →
      ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) := by
    intro Φ hΦ hb c hc k n
    obtain ⟨C, hC⟩ := hb k n
    have hcont : Continuous (fun ξ => SchwartzMap.seminorm ℂ k n (Φ ξ)) :=
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)).comp hΦ
    have i1 : Integrable (fun ξ => ‖h ξ‖) := h.integrable.norm
    have i2 : Integrable (fun ξ => ‖ξ‖ ^ n * ‖h ξ‖) := h.integrable_pow_mul volume n
    refine Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_
    · simp_rw [hc]
      exact (h.continuous.norm.mul hcont).aestronglyMeasurable
    · filter_upwards with ξ
      rw [hc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]
      calc ‖h ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ ‖h ξ‖ * (C * (1 + ‖ξ‖ ^ n)) :=
            mul_le_mul_of_nonneg_left (hC ξ) (norm_nonneg _)
        _ = C * (‖h ξ‖ + ‖ξ‖ ^ n * ‖h ξ‖) := by ring

  have hkey : ∀ ξ, Λ1 (T (Φf ξ)) = ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    intro ξ
    rw [hΛ1]
    refine hT (A ξ) f (Φf ξ) (Φg ξ) g (hΦf ξ) (fun x => ?_)
    rw [hΦg, ← mul_assoc, ← Complex.exp_add]
    simp [ContinuousLinearMap.neg_apply]
  have lhs : ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    rw [← hΛ1]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φf cΦf h h.continuous.aestronglyMeasurable
      (hint Φf cΦf bΦf h (fun _ => rfl)) f' (fun x => by
        rw [hf', hm, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦf]; ring) (Λ1.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]; simp_rw [hkey]
  have rhs : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    have e1 : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = starRingEnd ℂ (Λ2 (T g')) := by
      rw [hΛ2, ← integral_conj]; congr 1; funext x; simp [mul_comm]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φg cΦg (fun ξ => starRingEnd ℂ (h ξ))
      (Complex.continuous_conj.comp h.continuous).aestronglyMeasurable
      (hint Φg cΦg bΦg _ (fun _ => Complex.norm_conj _)) g' (fun x => by
        rw [hg', hm, ← integral_conj, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦg]
        simp only [map_mul, ContinuousLinearMap.neg_apply, ← Complex.exp_conj]
        simp [Complex.ofReal_neg]; ring) (Λ2.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [e1, this, ← integral_conj]
    congr 1; funext ξ
    rw [map_mul, Complex.conj_conj, hΛ2, ← integral_conj]
    congr 2; funext x; simp [mul_comm]
  rw [lhs, rhs]

end GlobalTheory.CharMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
section
noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CuspBlock

def tripSizes (l d N : ℕ) : Fin 3 → ℕ := ![l, d, N - (l + d)]

theorem tripSizes_sum {l d N : ℕ} (h : l + d ≤ N) : ∑ j, tripSizes l d N j = N := by
  simp only [tripSizes, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  omega

def tripPlace {l d N : ℕ} (h : l + d ≤ N) : (Σ j : Fin 3, Fin (tripSizes l d N j)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr (tripSizes_sum h))

variable (k : Type) [CommRing k]

def midHom (l d N : ℕ) : GL (Fin d) k →* Levi k (fun j : Fin 3 => Fin (tripSizes l d N j)) :=
  MonoidHom.mulSingle (fun j : Fin 3 => GL (Fin (tripSizes l d N j)) k) 1

variable {k} in

def glCast {a b : ℕ} (h : a = b) : GL (Fin a) k →* GL (Fin b) k := h ▸ MonoidHom.id _

@[simp] theorem glCast_rfl {a : ℕ} : glCast (k := k) (rfl : a = a) = MonoidHom.id _ := rfl

end GlobalTheory.CuspBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedGaussianIntegralUniformPosSemidef
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.TruncGauss

noncomputable def qf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) : ℂ :=
  ∑ j, ∑ l, A j l * w j * (starRingEnd ℂ) (w l)

theorem qf_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (A + B) w = qf A w + qf B w := by
  simp only [qf, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem qf_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (c • A) w = c * qf A w := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem qf_one {n : ℕ} (w : V n) : qf (1 : Matrix (Fin n) (Fin n) ℂ) w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [qf, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem qf_re_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (w : V n) :
    0 ≤ (qf H w).re := by
  have h := hH.dotProduct_mulVec_nonneg (fun j => (starRingEnd ℂ) (w j))
  have e : star (fun j => (starRingEnd ℂ) (w j)) ⬝ᵥ (H.mulVec (fun j => (starRingEnd ℂ) (w j))) = qf H w := by
    simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.conj_conj]; ring
  rw [e] at h
  exact (Complex.le_def.mp h).1

theorem isCompact_bdd (n : ℕ) (C : ℝ) :
    IsCompact {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 C
  have e : {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} =
      (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    ext H
    show _ ↔ ∀ j ∈ Set.univ, ∀ l ∈ Set.univ, H j l ∈ closedBall (0 : ℂ) C
    simp [mem_closedBall, dist_zero_right]
  rw [e]; exact h

theorem exists_det_bound (n : ℕ) (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) → ‖H.det‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_bdd n C).exists_bound_of_continuousOn
    (continuous_id.matrix_det).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun H hH => (hK H hH).trans (le_max_left _ _)⟩

theorem exists_det_shift (n : ℕ) (C r : ℝ) (hr : 0 < r) : ∃ η : ℝ, 0 < η ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) →
      ‖(H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ H ∈ {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C},
      ‖(H + (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
    refine (isCompact_bdd n C).eventually_forall_of_forall_eventually fun H _ => ?_
    have hc : Continuous fun z : ℝ × Matrix (Fin n) (Fin n) ℂ =>
        ‖(z.2 + (z.1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - z.2.det‖ := by
      fun_prop
    have h0 : ‖(H + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ = 0 := by simp
    have := hc.continuousAt (x := ((0 : ℝ), H))
    exact this.eventually (gt_mem_nhds (by simpa [h0] using hr))
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  exact ⟨t, htpos, fun H hH => ht H hH⟩

theorem qf_smul_one_re {n : ℕ} (c : ℝ) (w : V n) :
    (qf ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) w).re = c * ‖w‖ ^ 2 := by
  rw [qf_smul, qf_one, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem qf_shift_re {n : ℕ} (m η : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    (qf ((m : ℂ) • (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) w).re =
      m * ((qf H w).re + η * ‖w‖ ^ 2) := by
  rw [qf_smul, qf_add, qf_smul, qf_one, Complex.re_ofReal_mul, Complex.add_re,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem trunc_lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (m : ℕ) (hm : 1 ≤ m) :
    Real.pi ^ n / (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re
        - Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n ≤
      (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Hη := H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hHη
  have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (a := η) hη
  have hHηpd : Hη.PosDef := Matrix.PosDef.posSemidef_add hH hηpd
  have hMpd : ((m : ℂ) • Hη).PosDef := hHηpd.smul (a := (m : ℝ)) hm0
  set b : ℝ := m * η / 2 with hb
  have hb0 : 0 < b := by positivity
  have hGpd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := Matrix.PosDef.one.smul (a := b) hb0
  obtain ⟨hfi, hfint⟩ := GlobalTheory.T.integral_exp_neg_hermitian_form_posDef n _ hMpd
  obtain ⟨hgi, hgint⟩ := GlobalTheory.T.integral_exp_neg_hermitian_form_posDef n _ hGpd
  set f : V n → ℝ := fun w => Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) with hf
  set g : V n → ℝ := fun w => Real.exp (-(b * ‖w‖ ^ 2)) with hg
  have ef : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((m : ℂ) • Hη) j l * w j *
      (starRingEnd ℂ) (w l)).re)) = f := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_shift_re m η H w)
  have eg : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) j l *
      w j * (starRingEnd ℂ) (w l)).re)) = g := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_smul_one_re b w)
  rw [ef] at hfi hfint
  rw [eg] at hgi hgint
  have hD : ((m : ℂ) • Hη).det.re = (m : ℝ) ^ n * Hη.det.re := by
    rw [Matrix.det_smul, Fintype.card_fin, show ((m : ℂ)) ^ n = (((m : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul]
  have hGd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re = b ^ n := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  rw [hD] at hfint
  rw [hGd] at hgint
  have hDpos : 0 < Hη.det.re := by
    have := hHηpd.det_pos
    exact (Complex.lt_def.mp this).1

  have hsplit := integral_add_compl (s := ball (0 : V n) δ) measurableSet_ball hfi
  have htail : ∫ w in (ball (0 : V n) δ)ᶜ, f w ≤ Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on hfi.integrableOn (hgi.const_mul _).integrableOn
      measurableSet_ball.compl fun w hw => ?_).trans
      (setIntegral_le_integral (hgi.const_mul _) (Eventually.of_forall fun w => by positivity))
    have hw' : δ ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw
    have hq := qf_re_nonneg H hH w
    simp only [hf, hg]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ.le hw' 2
    have h2 : 0 ≤ (m : ℝ) * η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_nonneg hm0.le hq]
  have hmain : (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w =
      Real.pi ^ n / Hη.det.re - (m : ℝ) ^ n * ∫ w in (ball (0 : V n) δ)ᶜ, f w := by
    rw [eq_sub_iff_add_eq, ← mul_add, hsplit, hfint]
    field_simp
  have hT : (m : ℝ) ^ n * (Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w) =
      Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n := by
    rw [hgint, hb]
    field_simp
    have h1 : η ^ n * η⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη.ne', one_pow]
    have h2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((m : ℝ) ^ n * Real.pi ^ n * (1 / 2 : ℝ) ^ n * 2 ^ n)) * h1 -
      ((m : ℝ) ^ n * Real.pi ^ n) * h2
  show _ ≤ (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w
  rw [hmain, ← hT]
  have := mul_le_mul_of_nonneg_left htail (pow_nonneg hm0.le n)
  linarith

theorem trunc_gauss : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) →
      1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by
  intro n C ε hε
  set P : ℝ := Real.pi ^ n with hPdef
  have hP : 0 < P := pow_pos Real.pi_pos n
  set r : ℝ := ε * P / 2 with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_det_bound n C
  obtain ⟨η, hη, hηd⟩ := exists_det_shift n C r hr
  refine ⟨η, hη, fun δ hδ => ?_⟩
  set A : ℝ := K / P + ε with hAdef
  have hA : 0 < A := by positivity
  set K2 : ℝ := K + r with hK2def
  have hK2 : 0 < K2 := by positivity
  have hs : 0 < r / K2 / A := by positivity
  have hT : Tendsto (fun m : ℕ => Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) * (η * δ ^ 2 / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const ((2 * Real.pi / η) ^ n)
    rw [zero_mul] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  filter_upwards [hT.eventually (gt_mem_nhds hs), eventually_ge_atTop 1] with m hm hm1
  intro H hH hC
  have hl := trunc_lower H hH η δ hη hδ m hm1
  show 1 ≤ _ * _ * ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set I := ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set T := Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n with hTdef
  have hT0 : 0 ≤ T := by positivity
  set d := H.det.re with hddef
  set D := (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re with hDdef
  have hd0 : 0 ≤ d := by
    have := (Complex.le_def.mp hH.det_nonneg).1
    simpa using this
  have hdK : d ≤ K := (Complex.re_le_norm _).trans (hK H hC)
  have hDd : D - d < r := by
    have := (Complex.re_le_norm _).trans_lt (hηd H hC)
    rw [Complex.sub_re] at this; exact this
  have hDpos : 0 < D := by
    have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (a := η) hη
    exact (Complex.lt_def.mp (Matrix.PosDef.posSemidef_add hH hηpd).det_pos).1
  have e1 : (d / P + ε) * (P / D) = (d + ε * P) / D := by field_simp
  have e2 : r / K2 ≤ r / D := div_le_div_of_nonneg_left hr.le hDpos (by linarith)
  have e3 : 1 + r / D ≤ (d + ε * P) / D := by
    rw [le_div_iff₀ hDpos, add_mul, div_mul_cancel₀ _ hDpos.ne']
    linarith
  have e4 : (d / P + ε) * T ≤ A * T :=
    mul_le_mul_of_nonneg_right (by have := div_le_div_of_nonneg_right hdK hP.le; linarith) hT0
  have e5 : A * T < r / K2 := by
    have := (lt_div_iff₀ hA).mp hm
    linarith
  have e6 : (d / P + ε) * (P / D - T) ≤ (d / P + ε) * ((m : ℝ) ^ n * I) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  rw [mul_assoc]
  rw [mul_sub, e1] at e6
  linarith

end GlobalTheory.TruncGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumLatticePairUnitQuotientRegroupStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_latticePair_unitQuotient_regroup : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  first | exact @GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup | exact GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup | (intros; apply GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumResidueClassSplitBySignStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_residueClass_split_by_sign : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by
  first | exact @GlobalTheory.WpFam.tsum_residue_class_split | exact GlobalTheory.WpFam.tsum_residue_class_split | (intros; apply GlobalTheory.WpFam.tsum_residue_class_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  first | (exact @GlobalTheory.Shin.twisted_class_main) | (exact GlobalTheory.Shin.twisted_class_main) | (intros; apply GlobalTheory.Shin.twisted_class_main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPowerOnExcisionNeighbourhood
section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_isPow_on_excisionNbhd : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨a, bn, ha⟩ := hn
  obtain ⟨a', bd, hb⟩ := hd
  have hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1 := by
    linear_combination (-(bd * d')) * ha + (a * g - 1) * hb
  have hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g :=
    GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd)
      (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)
  set C' := Localization.Away (n' * d') with hC'def
  have hnd : IsUnit (algebraMap B C' (n' * d')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hnd
  have hnC : IsUnit (algebraMap B C' n') := isUnit_of_mul_isUnit_left hnd
  have hdC : IsUnit (algebraMap B C' d') := isUnit_of_mul_isUnit_right hnd
  set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi
  have hDi1 : Di * algebraMap B C' d' = 1 := by rw [hDi]; exact hdC.val_inv_mul
  set ε : C' := algebraMap B C' n' * Di with hεdef
  have hε : IsUnit ε := hnC.mul (Units.isUnit _)
  have hεd : ε * algebraMap B C' d' = algebraMap B C' n' := by rw [hεdef, mul_assoc, hDi1, mul_one]
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d')
    (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)
  obtain ⟨w, hw'⟩ := Ideal.mem_span_singleton'.mp hr
  have hqC : IsUnit (q : C') := by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))
  have hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g} := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩
    have e1 := congrArg (algebraMap B C') hw'
    have e2 := congrArg (algebraMap B C') hb
    simp only [map_mul, map_sub, map_add, map_pow, map_one] at e1 e2
    rw [hεdef]
    linear_combination e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1
  obtain ⟨C, _, _, hC, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr
  letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra
  haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩
  set L := Localization.Away (algebraMap B C (f * g))
  set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ
  set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ
  have hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y) := fun _ => rfl
  have hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g)
      (algebraMap B (Localization.Away (f * g)) y) = ψ y := by
    intro y; exact IsLocalization.map_eq _ _
  have hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n' := by
    have h := congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu
    rw [map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ] at h
    rw [← map_pow ψ, ← map_mul ψ]; exact h
  have hnL : IsUnit (ψ n') := by rw [hψρ]; exact hnC.map ρ
  have hdL : IsUnit (ψ d') := by rw [hψρ]; exact hdC.map ρ
  have hεL : ρ ε * ψ d' = ψ n' := by
    have := congrArg ρ hεd; rw [map_mul] at this; rw [hψρ, hψρ]; exact this
  have hxL : algebraMap C L x ^ q = ρ ε := by
    have := congrArg (algebraMap C L) hx; rw [map_pow] at this; exact this.symm
  have hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q := by
    rw [← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]
  have hTq : IsUnit (ψ t ^ q) := by
    have h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d')) := by
      rw [hu']; exact hnL
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)
  have hT : IsUnit (ψ t) := (isUnit_pow_iff hq0).mp hTq
  have hX : IsUnit (algebraMap C L x) := by
    refine (isUnit_pow_iff hq0).mp ?_
    rw [hXU]; exact ((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq
  refine ⟨hX.unit * hT.unit⁻¹, ?_⟩
  rw [Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTAStatement
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTA_conj_det_of_isUA_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det := by
  first | exact @GlobalTheory.unitary_det_isTA | exact GlobalTheory.unitary_det_isTA | (intros; apply GlobalTheory.unitary_det_isTA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperHalfPlaneProductProdImRpowContDiffOnStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.upperHalf_prodImPow_contDiffOn | exact GlobalTheory.upperHalf_prodImPow_contDiffOn | (intros; apply GlobalTheory.upperHalf_prodImPow_contDiffOn <;> assumption)
end

