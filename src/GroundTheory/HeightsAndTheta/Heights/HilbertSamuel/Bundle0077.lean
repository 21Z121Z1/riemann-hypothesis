import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0046
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ChangeOfModel

variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]

open Classical in

def blockDeg (k₂ : K) : K → ℕ := fun k => if k = k₂ then 1 else 0

omit [Fintype K] [∀ k, Fintype (ι₂ k)] in

theorem isMultiHomog_linForm (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    IsMultiHomog (linForm A q) (blockDeg q.1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  obtain ⟨k₀, j⟩ := q
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk]

omit [∀ k, Fintype (ι₂ k)] in

theorem exists_linForm_not_mem {P : Ideal (MRing ι)} {d : ℕ} {A : ∀ k, ι₂ k → ι k → ℤ} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P (linForm A)) : ∀ k₂, ∃ j, linForm A ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => linForm A ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  have := hprime
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end ChangeOfModel

open ChangeOfModel IndefiniteRowSideFullHecke.Inter in

theorem ChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometric.Statement) : ChangeOfModelStatement := by
  intro I hI K _ ι ι₂ _ _ P d A G J L L₁ hP hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K ι₂ P d (linForm A) blockDeg hP
    (isMultiHomog_linForm A) (exists_linForm_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K))
  have e1 := hAI3 I hI K ι (K ⊕ K) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K ι₂ (K ⊕ K) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K) (Sum.elim ι ι₂) (I (K ⊕ K) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι ι₂ P d A (L₁ j) (L j) _ _ hP hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric

noncomputable section

theorem ChartSupBound.proof : ChartSupBound.Statement := by
  intro D V K ψ ν hV hK hKV hψ hν hν0
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun n _ F _ w hw => by simp [hKe] at hw⟩
  obtain ⟨r, hr0, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  set S := cthickening r K with hS
  have hSc : IsCompact S := hK.cthickening
  have hSne : S.Nonempty := hKne.mono (self_subset_cthickening K)

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M := by
    have h1 := hψ.fderiv_of_isOpen hV (m := 1) (by norm_num)
    exact hSc.exists_bound_of_continuousOn ((h1.continuousOn_fderiv_of_isOpen hV le_rfl).mono hrV)
  set M' := |M| with hM'

  obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hSne (hν.mono hrV)
  set ν₀ := ν x₀ with hν₀
  have hν₀pos : 0 < ν₀ := hν0 x₀ (hrV hx₀)
  set P : ℝ := (Real.pi * r ^ 2) ^ D with hP
  have hPpos : 0 < P := by positivity
  have hprod : ∏ _j : Fin D, gaussDiscMass 0 r = P := by
    rw [hP, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [gaussDiscMass]
  refine ⟨Real.exp (M' * r ^ 2) / (ν₀ * P), fun n hn F hF w hw => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set s := r / Real.sqrt n with hs
  have hs2 : (n : ℝ) * s ^ 2 = r ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hnpos.le]
    field_simp
  have hsr : s ≤ r := by
    rw [hs]
    refine div_le_self hr0.le ?_
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  set B := closedBall (0 : Fin D → ℂ) s with hB
  have hzS : ∀ z ∈ B, closedBall w ‖z‖ ⊆ S := fun z hz =>
    (closedBall_subset_closedBall ((mem_closedBall_zero_iff.1 hz).trans hsr)).trans
      (closedBall_subset_cthickening hw r)
  have hwzS : ∀ z ∈ B, w + z ∈ S := fun z hz => hzS z hz (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])

  set ℓ := fderiv ℝ ψ w with hℓ
  set lam : (Fin D → ℂ) →L[ℂ] ℂ := StrongDual.extendRCLike (𝕜 := ℂ) ℓ with hlam
  have hre : ∀ z, (lam z).re = ℓ z := fun z => by
    rw [hlam, StrongDual.extendRCLike_apply]
    simp
  set G : (Fin D → ℂ) → ℂ := fun z => F (w + z) * Complex.exp (((-(n : ℝ) / 2 : ℝ) : ℂ) * lam z)
    with hGdef
  have hG0 : G 0 = F w := by simp [hGdef]
  have hGan : AnalyticOnNhd ℂ G B := by
    intro z hz
    have haff : AnalyticAt ℂ (fun z : Fin D → ℂ => w + z) z := analyticAt_const.add analyticAt_id
    exact ((hF _ (hrV (hwzS z hz))).comp_of_eq haff rfl).mul
      ((analyticAt_const.mul (lam.analyticAt z)).cexp)
  have hPn := PolydiscSubmean.proof D n (fun _ => 0) r G (by omega) hr0 (fun _ => le_rfl) hGan
  simp only [zero_mul, Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at hPn
  rw [hG0, hprod] at hPn
  set k : ℝ := ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) with hk
  have hk0 : 0 ≤ k := by positivity

  have hpt : ∀ z ∈ B, ENNReal.ofReal (k * ‖G z‖ ^ 2) ≤
      ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z)) := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hGz : ‖G z‖ ^ 2 = ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := by
      simp only [hGdef]
      rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre, mul_pow, sq (Real.exp _),
        ← Real.exp_add]
      congr 2
      ring
    have hT := ChartTaylorCover.taylor_le hV hψ ((hzS z hz).trans hrV)
      (fun x hx => (hM x (hzS z hz hx)).trans (le_abs_self M))
    have hz' : ‖z‖ ≤ s := mem_closedBall_zero_iff.1 hz
    have hnz : (n : ℝ) * (M' * ‖z‖ ^ 2) ≤ M' * r ^ 2 := by
      calc (n : ℝ) * (M' * ‖z‖ ^ 2) = M' * ((n : ℝ) * ‖z‖ ^ 2) := by ring
        _ ≤ M' * ((n : ℝ) * s ^ 2) := by gcongr
        _ = M' * r ^ 2 := by rw [hs2]
    have hexp : Real.exp (-(M' * r ^ 2)) * (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z)) ≤
        Real.exp (-(n : ℝ) * ψ (w + z)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hT hnpos.le
      nlinarith
    have hνz : ν₀ ≤ ν (w + z) := isMinOn_iff.1 hmin _ (hwzS z hz)
    rw [hGz, hk]
    have hF0 : 0 ≤ ‖F (w + z)‖ ^ 2 := by positivity
    calc ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
          (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z))
        = ‖F (w + z)‖ ^ 2 * (Real.exp (-(M' * r ^ 2)) *
            (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z))) * ν₀ := by ring
      _ ≤ ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hF0) hνz hν₀pos.le (by positivity)

  have hΦ : MeasurePreserving (fun z : Fin D → ℂ => w + z) volume volume :=
    measurePreserving_add_left volume w
  have hemb : MeasurableEmbedding (fun z : Fin D → ℂ => w + z) :=
    (Homeomorph.addLeft w).isClosedEmbedding.measurableEmbedding
  have hint : ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) ≤ ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by
    calc _ ≤ ‖∫ z in B, ‖G z‖ ^ 2‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ z in B, ‖‖G z‖ ^ 2‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = _ := lintegral_congr fun z => Real.enorm_eq_ofReal (by positivity)
  have hmain : ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) ≤
      ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z) := by
    calc _ ≤ ENNReal.ofReal (k * ∫ z in B, ‖G z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPn hk0)
      _ = ENNReal.ofReal k * ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) := ENNReal.ofReal_mul hk0
      _ ≤ ENNReal.ofReal k * ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by gcongr
      _ = ∫⁻ z in B, ENNReal.ofReal k * ENNReal.ofReal (‖G z‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ z in B, ENNReal.ofReal (k * ‖G z‖ ^ 2) :=
          lintegral_congr fun z => (ENNReal.ofReal_mul hk0).symm
      _ ≤ ∫⁻ z in B, ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) *
            ν (w + z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hpt
      _ = ∫⁻ y in (fun z : Fin D → ℂ => w + z) '' B,
            ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y) :=
          hΦ.setLIntegral_comp_emb hemb
            (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y)) B
      _ ≤ _ := lintegral_mono_set (image_subset_iff.2 fun z hz => hrV (hwzS z hz))
  have hC0 : 0 ≤ Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D := by positivity
  have heq : Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D *
      (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
    have hnD : (n : ℝ) ^ D ≠ 0 := by positivity
    have he : Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hνP : ν₀ * P ≠ 0 := by positivity
    rw [hk, div_eq_mul_inv]
    calc Real.exp (M' * r ^ 2) * (ν₀ * P)⁻¹ * (n : ℝ) ^ D *
          (ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
            (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P))
        = (Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2))) * ((n : ℝ) ^ D * ((n : ℝ) ^ D)⁻¹) *
            ((ν₀ * P) * (ν₀ * P)⁻¹) * (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) := by ring
      _ = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
        rw [he, mul_inv_cancel₀ hnD, mul_inv_cancel₀ hνP]; ring
  calc ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w))
      = ENNReal.ofReal (Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D) *
          ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) := by
        rw [← ENNReal.ofReal_mul hC0, heq]
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedRestrict

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev locMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

section General

variable {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N]

theorem locMap_mk (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem locMap_cellRes (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    locMap (KH.cellMon S I) g (KH.cellRes S M J I x) = KH.cellRes S N J I (locMap (KH.cellMon S J) g x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [GenTwistGenerated.cellRes_mk h, locMap_mk, locMap_mk, GenTwistGenerated.cellRes_mk h]
  · unfold KH.cellRes
    rw [dif_neg h, dif_neg h]
    simp

end General

variable {V W : Ideal (MRingOver S ι)}

abbrev quotMap (hVW : V ≤ W) : (MRingOver S ι ⧸ V) →ₗ[MRingOver S ι] (MRingOver S ι ⧸ W) :=
  (Ideal.Quotient.factorₐ (MRingOver S ι) hVW).toLinearMap

theorem quotMap_mul (hVW : V ≤ W) (x y : MRingOver S ι ⧸ V) :
    quotMap hVW (x * y) = quotMap hVW x * quotMap hVW y := by
  simp [quotMap]

theorem quotMap_smul (hVW : V ≤ W) (s : S) (x : MRingOver S ι ⧸ V) :
    quotMap hVW (s • x) = s • quotMap hVW x :=
  LinearMap.map_smul_of_tower _ s x

theorem locMap_smul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (s : S)
    (x : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (s • x) = s • locMap T (quotMap hVW) x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.smul'_mk, locMap_mk, locMap_mk, LocalizedModule.smul'_mk, quotMap_smul]

theorem locMap_mul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (x y : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (x * y) = locMap T (quotMap hVW) x * locMap T (quotMap hVW) y := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_mul_mk, locMap_mk, locMap_mk, locMap_mk, LocalizedModule.mk_mul_mk, quotMap_mul]

theorem locMap_one (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) :
    locMap T (quotMap hVW) (1 : LocalizedModule T (MRingOver S ι ⧸ V)) = 1 := by
  have e : ∀ (P : Type) [CommRing P] [Algebra (MRingOver S ι) P],
      (1 : LocalizedModule T P) = LocalizedModule.mk 1 1 := fun _ _ _ => OreLocalization.one_def
  have h1 : quotMap hVW (1 : MRingOver S ι ⧸ V) = 1 := by simp [quotMap]
  rw [e, e, locMap_mk, h1]

theorem cechD_cechMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (f : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n f) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n f) := by
  funext I
  simp only [KH.cechD, KH.cechMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact (congrArg (fun y => KH.faceSign I.1 k i • y) (locMap_cellRes g _ I.1 (f ⟨_, h⟩))).symm.trans
      (map_zsmul (locMap (KH.cellMon S I.1) g) _ _).symm
  · simp

theorem quotMap_mem_quotPart (hVW : V ≤ W) {c : K → ℤ} {x : MRingOver S ι ⧸ V}
    (hx : x ∈ KH.quotPart S V c) : quotMap hVW x ∈ KH.quotPart S W c := by
  unfold KH.quotPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [quotMap_smul]; exact Submodule.smul_mem _ s hx

theorem locMap_mem_locPart (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    locMap T (quotMap hVW) x ∈ KH.locPart ι (KH.quotPart S W) T c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [locMap_mk]
    exact GenTwistGenerated.mk_mem_locPart _ t a ht (quotMap_mem_quotPart hVW hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [locMap_smul]; exact Submodule.smul_mem _ s hx

end GeneratedRestrict

open GeneratedRestrict in

theorem GeneratedRestrict.proof : GeneratedRestrict.Statement := by
  intro S _ K _ _ ι _ _ V W a hVW hV I
  obtain ⟨r, z, u, hz, hu, h1⟩ := hV I
  refine ⟨r, fun j => KH.cechMap S ι (quotMap hVW) 0 (z j), fun j => locMap _ (quotMap hVW) (u j),
    fun j => ?_, fun j => locMap_mem_locPart hVW _ (hu j), ?_⟩
  · obtain ⟨hzc, hzd⟩ := hz j
    refine GenTwistGenerated.mem_cechZc_zero (fun J => ?_) ?_
    · exact locMap_mem_locPart hVW _ ((Submodule.mem_pi.mp hzc) J (Set.mem_univ _))
    · rw [cechD_cechMap, LinearMap.mem_ker.mp hzd, map_zero]
  · have hc : ∀ j, KH.cechMap S ι (quotMap hVW) 0 (z j) I = locMap _ (quotMap hVW) (z j I) := fun j => rfl
    simp only [hc, ← locMap_mul, ← map_sum, h1, locMap_one]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (coordIdeal ℤ x).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) := hm
    rw [show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) =
      (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    simp only [Fintype.card_unit] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_
    rw [hform]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GenericFibreVar.proof : GenericFibreVar.Statement := by
  intro K _ ι _ Ω _ y D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (mCoordIdeal y).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0 := by
    intro m hm
    have h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq
      (D + Fintype.card K) _ ?_
    rw [hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomCharpolyForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      (∀ k, u * (l j / l k) ^ m ∈ integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω) →
      ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, c 0 = 1 ∧
        (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) ∧
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) ∧
        (u ≠ 0 → c (Module.finrank P Ω) ≠ 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

