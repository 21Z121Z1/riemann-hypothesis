import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MeasureTheory Set Filter Function ReciprocityTheory.ChartRestriction.G.Geo

namespace LintegralFibSum

variable {e : ℕ}

theorem measurable_jacN (Q : (Fin e → ℂ) → (Fin e → ℂ)) : Measurable (jacN Q) := by
  unfold jacN
  exact ((continuous_norm.comp ContinuousLinearMap.continuous_det).measurable.comp
    (measurable_fderiv ℂ Q)).pow_const 2

theorem fibSum_nonneg (D : Set (Fin e → ℂ)) (Q : (Fin e → ℂ) → (Fin e → ℂ)) {h : (Fin e → ℂ) → ℝ}
    (hh : ∀ u, 0 ≤ h u) (y : Fin e → ℂ) : 0 ≤ fibSum D Q h y :=
  finsum_nonneg fun u => finsum_nonneg fun _ => div_nonneg (hh u) (by unfold jacN; positivity)

theorem lintegral_fibSum_piece {D : Set (Fin e → ℂ)} (hD : MeasurableSet D) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQd : ∀ u ∈ D, DifferentiableAt ℂ Q u)
    (hdet : ∀ u ∈ D, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hinj : InjOn Q D) {h : (Fin e → ℂ) → ℝ} (hm : Measurable fun u : D => h u) :
    Measurable (fun y => ENNReal.ofReal (fibSum D Q h y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum D Q h y) = ∫⁻ u in D, ENNReal.ofReal (h u) := by
  have hf' : ∀ u ∈ D, HasFDerivWithinAt Q ((fderiv ℂ Q u).restrictScalars ℝ) D u :=
    fun u hu => ((hQd u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hJpos : ∀ u ∈ D, 0 < jacN Q u := fun u hu => pow_pos (norm_pos_iff.mpr (hdet u hu)) 2
  have hval : ∀ u ∈ D, fibSum D Q h (Q u) = h u / jacN Q u := by
    intro u hu
    have : D ∩ Q ⁻¹' {Q u} = {u} := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨hw, hq⟩ => hinj hw hu hq, fun hw => by subst hw; exact ⟨hu, rfl⟩⟩
    simp only [fibSum, this, finsum_mem_singleton]
  have hzero : ∀ y, y ∉ Q '' D → fibSum D Q h y = 0 := by
    intro y hy
    have : D ∩ Q ⁻¹' {y} = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun hw hq => hy ⟨w, hw, hq⟩
    simp [fibSum, this]
  have hE := measurableEmbedding_of_fderivWithin hD hf' hinj
  have hext : (fun y => ENNReal.ofReal (fibSum D Q h y)) =
      extend (D.domRestrict Q) (fun u : D => ENNReal.ofReal (h u / jacN Q u)) 0 := by
    funext y
    by_cases hy : ∃ u : D, D.domRestrict Q u = y
    · obtain ⟨u, rfl⟩ := hy
      rw [hE.injective.extend_apply]
      exact congrArg ENNReal.ofReal (hval u u.2)
    · rw [extend_apply' _ _ _ hy, hzero y fun ⟨u, hu, hq⟩ => hy ⟨⟨u, hu⟩, hq⟩]
      simp
  refine ⟨?_, ?_⟩
  · rw [hext]
    exact hE.measurable_extend (ENNReal.measurable_ofReal.comp
      (hm.div ((measurable_jacN Q).comp measurable_subtype_coe))) measurable_const
  · rw [← setLIntegral_eq_of_support_subset (s := Q '' D) (fun y hy => by
        by_contra h'
        exact hy (show ENNReal.ofReal (fibSum D Q h y) = 0 by rw [hzero y h', ENNReal.ofReal_zero])),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hf' hinj]
    refine setLIntegral_congr_fun hD fun u hu => ?_
    have hJ : |((fderiv ℂ Q u).restrictScalars ℝ).det| = jacN Q u := abs_det_restrictScalars _
    rw [hval u hu, hJ, ← ENNReal.ofReal_mul (hJpos u hu).le]
    congr 1
    field_simp [(hJpos u hu).ne']

theorem lintegral_fibSum_open {O : Set (Fin e → ℂ)} (hO : IsOpen O) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : ∀ u, 0 ≤ h u) (hm : Measurable fun u : O => h u)
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) :
    AEMeasurable (fun y => ENNReal.ofReal (fibSum O Q h y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum O Q h y) = ∫⁻ u in O, ENNReal.ofReal (h u) := by
  obtain ⟨W, hWo, hWO, hWinj, hWU⟩ := exists_inj_cover hQ hO
  set D := disjointed W with hDdef
  have hDm : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed fun n => (hWo n).measurableSet
  have hDsub : ∀ n, D n ⊆ W n := disjointed_subset W
  have hDU : ⋃ n, D n = O := iUnion_disjointed.trans hWU
  have hDd : Pairwise (Disjoint on D) := disjoint_disjointed W
  have hDO : ∀ n, D n ⊆ O := fun n => (hDsub n).trans (hWO n)
  have hp : ∀ n, Measurable (fun y => ENNReal.ofReal (fibSum (D n) Q h y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum (D n) Q h y) = ∫⁻ u in D n, ENNReal.ofReal (h u) := fun n =>
    lintegral_fibSum_piece (hDm n) (fun u hu => (hQ u (hDO n hu)).1.differentiableAt)
      (fun u hu => (hQ u (hDO n hu)).2) ((hWinj n).mono (hDsub n))
      (hm.comp (f := fun u : D n => (⟨u.1, hDO n u.2⟩ : O)) measurable_subtype_coe.subtype_mk)
  have hae : (fun y => ENNReal.ofReal (fibSum O Q h y)) =ᵐ[volume]
      fun y => ∑' n, ENNReal.ofReal (fibSum (D n) Q h y) := by
    filter_upwards [hfin] with y hy
    have hT : {n | (D n ∩ Q ⁻¹' {y}).Nonempty}.Finite := by
      refine (hy.biUnion fun u _ => (show {n | u ∈ D n}.Subsingleton from
        fun n hn m hm => by_contra fun hnm => Set.disjoint_left.mp (hDd hnm) hn hm).finite).subset ?_
      rintro n ⟨u, hu, hq⟩
      exact mem_iUnion₂.mpr ⟨u, ⟨hDO n hu, hq⟩, hu⟩
    have hsum : Summable fun n => fibSum (D n) Q h y :=
      summable_of_ne_finset_zero (s := hT.toFinset) fun n hn => by
        have : D n ∩ Q ⁻¹' {y} = ∅ := by
          rw [Set.Finite.mem_toFinset] at hn
          exact not_nonempty_iff_eq_empty.mp hn
        simp [fibSum, this]
    show ENNReal.ofReal (∑ᶠ u ∈ O ∩ Q ⁻¹' {y}, h u / jacN Q u) = _
    rw [← tsum_finsum_disjointed hDd hDU hy (fun u => h u / jacN Q u)]
    exact ENNReal.ofReal_tsum_of_nonneg (f := fun n => fibSum (D n) Q h y)
      (fun n => fibSum_nonneg _ _ hh y) hsum
  refine ⟨(Measurable.tsum fun n => (hp n).1).aemeasurable.congr hae.symm, ?_⟩
  rw [lintegral_congr_ae hae, lintegral_tsum fun n => (hp n).1.aemeasurable,
    tsum_congr fun n => (hp n).2, ← lintegral_iUnion hDm hDd, hDU]

end LintegralFibSum

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuOneCoeff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace FlagIntMuOne

open MvPolynomial Finset

noncomputable def rhoPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) : Unit × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => N - 1 - (σ p.2 : ℕ)

theorem flagInt_unit_eq (N : ℕ) (P : RootPoly Unit N) :
    flagInt Unit N P =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℚ) * coeff (rhoPerm N σ) P := by
  unfold flagInt antisym
  rw [coeff_sum, ← (Equiv.funUnique Unit (Equiv.Perm (Fin N))).symm.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_smul, smul_eq_mul]
  congr 1
  · simp [weylSign]
  · have hinj : Function.Injective (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) := by
      rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      simpa [weylAct] using h
    have hρ : rhoMono Unit N =
        Finsupp.mapDomain (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) (rhoPerm N σ) := by
      ext ⟨⟨⟩, k⟩
      obtain ⟨i, rfl⟩ := σ.surjective k
      have : ((), σ i) = weylAct Unit N ((Equiv.funUnique Unit _).symm σ) ((), i) := rfl
      rw [this, Finsupp.mapDomain_apply hinj]
      simp [rhoMono, rhoPerm, weylAct]
    rw [hρ, coeff_rename_mapDomain _ hinj]

theorem muPoly_eq_sum (N j : ℕ) :
    muPoly Unit N j = ∑ p, (if (p.2 : ℕ) < j then (0 : ℚ) else 1) • X p := by
  unfold muPoly
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp_all

theorem coeff_muPow_rhoBlock (j m : ℕ) (σ : Equiv.Perm (Fin (j + m))) :
    coeff (rhoPerm (j + m) σ)
        (muPoly Unit (j + m) j ^ (j * m) * monomial (rhoBlock Unit (j + m) j) 1) =
      ((j * m).factorial : ℚ) * ∏ i, flagMat j m i (σ i) := by
  set d := rhoPerm (j + m) σ with hd
  set s := rhoBlock Unit (j + m) j with hs
  have hdv : ∀ i : Fin (j + m), d ((), i) = j + m - 1 - (σ i : ℕ) := fun i => rfl
  have hsv : ∀ i : Fin (j + m), s ((), i) = if (i : ℕ) < j then j - 1 - (i : ℕ) else j + m - 1 - (i : ℕ) :=
    fun i => rfl

  have hpt : ∀ i : Fin (j + m), flagMat j m i (σ i) =
      if s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)
      then (((d ((), i) - s ((), i)).factorial : ℚ))⁻¹ else 0 := by
    intro i
    have hi := i.isLt
    have hσ := (σ i).isLt
    simp only [flagMat, Matrix.of_apply, hdv, hsv]
    by_cases hij : (i : ℕ) < j
    · simp only [hij, if_true, forall_const]
      by_cases h : (σ i : ℕ) = m + i
      · rw [if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j - 1 - i) = 0 by omega]
        simp
      · rw [if_neg h, if_neg (by omega)]
    · simp only [hij, if_false, false_implies, and_true]
      by_cases h : (σ i : ℕ) ≤ i
      · rw [if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j + m - 1 - i) = i - σ i by omega]
      · rw [if_neg h, if_neg (by omega)]
  rw [coeff_mul_monomial', muPoly_eq_sum, coeff_linearCombination_X_pow_of_fintype]
  by_cases hall : ∀ i : Fin (j + m), s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)
  · have hle : s ≤ d := by
      intro p
      obtain ⟨⟨⟩, i⟩ := p
      exact (hall i).1
    have hev : ∀ i : Fin (j + m), ((d - s) ((), i) : ℤ) = (i : ℤ) - (σ i : ℤ) + (if (i : ℕ) < j then (m : ℤ) else 0) := by
      intro i
      have hi := i.isLt
      have hσ := (σ i).isLt
      have := hall i
      rw [Finsupp.tsub_apply, hdv, hsv] at *
      split_ifs at * with hij <;> omega
    have hsumN : ∑ i : Fin (j + m), (d - s) ((), i) = j * m := by
      have hz : ((∑ i : Fin (j + m), (d - s) ((), i) : ℕ) : ℤ) = ((j * m : ℕ) : ℤ) := by
        have hσsum : ∑ i : Fin (j + m), ((σ i : ℕ) : ℤ) = ∑ i : Fin (j + m), ((i : ℕ) : ℤ) :=
          Equiv.sum_comp σ (fun i => ((i : ℕ) : ℤ))
        rw [Nat.cast_sum, Finset.sum_congr rfl (fun i _ => hev i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hσsum, sub_self, zero_add, Fin.sum_univ_add]
        simp
      exact_mod_cast hz
    have hsum : (d - s).sum (fun _ k => k) = j * m := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
      simpa using hsumN
    have hprod : ((d - s).prod fun r k => (if (r.2 : ℕ) < j then (0 : ℚ) else 1) ^ k) = 1 := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      refine Finset.prod_eq_one fun p _ => ?_
      obtain ⟨⟨⟩, i⟩ := p
      by_cases hij : (i : ℕ) < j
      · simp only [Finsupp.tsub_apply]
        rw [(hall i).2 hij, pow_zero]
      · simp [hij]
    have hmult : (((d - s).multinomial : ℕ) : ℚ) =
        ((j * m).factorial : ℚ) / ∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ) := by
      have h := Nat.multinomial_spec (Finset.univ : Finset (Unit × Fin (j + m))) (DFunLike.coe (d - s))
      rw [← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h
      rw [Fintype.sum_prod_type, Fintype.prod_prod_type] at h
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, PUnit.default_eq_unit] at h
      rw [hsumN] at h
      have hP : (∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ)) ≠ 0 :=
        prod_ne_zero_iff.mpr fun i _ => by positivity
      rw [eq_div_iff hP, mul_comm]
      exact_mod_cast h
    rw [if_pos hle, if_pos hsum, hprod, mul_one, mul_one, hmult, div_eq_mul_inv, ← prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hpt, if_pos (hall i), Finsupp.tsub_apply]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hpt, if_neg (by tauto)]), mul_zero]
    split_ifs with hle hsum
    · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mul_one]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ((), i)) ?_)
      obtain ⟨hij, hne⟩ := hi (hle ((), i))
      simp [hij, Finsupp.tsub_apply, hne]
    · simp
    · simp

end FlagIntMuOne

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuProdSlice
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

namespace FlagIntMuProd

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def sliceEmb (τ : Ψ) (i : Fin N) : Ψ × Fin N := (τ, i)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem sliceEmb_injective (τ : Ψ) : Function.Injective (sliceEmb (N := N) τ) := by
  intro a b h
  simpa [sliceEmb] using h

def glue (d : Ψ → (Fin N →₀ ℕ)) : Ψ × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => d p.1 p.2

omit [DecidableEq Ψ] in
theorem glue_injective : Function.Injective (glue (Ψ := Ψ) (N := N)) := by
  intro d e h
  funext τ
  ext i
  have := congrArg (fun g : Ψ × Fin N →₀ ℕ => g (τ, i)) h
  simpa [glue] using this

theorem sum_mapDomain_sliceEmb (A : Ψ → (Fin N →₀ ℕ)) :
    ∑ τ, Finsupp.mapDomain (sliceEmb τ) (A τ) = glue A := by
  ext ⟨σ, i⟩
  rw [Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single σ]
  · rw [show ((σ, i) : Ψ × Fin N) = sliceEmb σ i from rfl, Finsupp.mapDomain_apply (sliceEmb_injective σ)]
    rfl
  · intro τ _ hτ
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact hτ (congrArg Prod.fst ha)
  · intro h
    exact absurd (Finset.mem_univ σ) h

theorem coeff_glue_prod (r : Ψ → MvPolynomial (Fin N) ℚ) (d : Ψ → (Fin N →₀ ℕ)) :
    coeff (glue d) (∏ τ, rename (sliceEmb τ) (r τ)) = ∏ τ, coeff (d τ) (r τ) := by
  have h : ∀ τ, rename (sliceEmb τ) (r τ) =
      ∑ a ∈ (r τ).support, monomial (Finsupp.mapDomain (sliceEmb τ) a) (coeff a (r τ)) := by
    intro τ
    conv_lhs => rw [as_sum (r τ)]
    rw [map_sum]
    simp only [rename_monomial]
  simp_rw [h]
  rw [Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod, sum_mapDomain_sliceEmb, coeff_sum, coeff_monomial,
    glue_injective.eq_iff]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [Fintype.mem_piFinset] at hd
    push Not at hd
    obtain ⟨τ, hτ⟩ := hd
    exact (Finset.prod_eq_zero (Finset.mem_univ τ) (notMem_support_iff.mp hτ)).symm

variable (N) in

def rhoOne : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => N - 1 - (i : ℕ)

variable (N) in

def flagIntOne (q : MvPolynomial (Fin N) ℚ) : ℚ :=
  ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * coeff (rhoOne N) (rename σ q)

omit [DecidableEq Ψ] in
theorem rhoMono_eq_glue : rhoMono Ψ N = glue fun _ => rhoOne N := by
  ext p
  rfl

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rename_weylAct_sliceEmb (w : Ψ → Equiv.Perm (Fin N)) (τ : Ψ) (q : MvPolynomial (Fin N) ℚ) :
    rename (weylAct Ψ N w) (rename (sliceEmb τ) q) = rename (sliceEmb τ) (rename (w τ) q) := by
  rw [rename_rename, rename_rename]
  rfl

theorem flagInt_prod (q : Ψ → MvPolynomial (Fin N) ℚ) :
    flagInt Ψ N (∏ τ, rename (sliceEmb τ) (q τ)) = ∏ τ, flagIntOne N (q τ) := by
  unfold flagInt antisym flagIntOne
  rw [coeff_sum, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [coeff_smul, map_prod, rhoMono_eq_glue]
  simp_rw [rename_weylAct_sliceEmb]
  rw [coeff_glue_prod, weylSign, smul_eq_mul, ← Finset.prod_mul_distrib]

theorem flagIntOne_eq_zero_of_isHomogeneous {q : MvPolynomial (Fin N) ℚ} {D : ℕ} (hq : q.IsHomogeneous D)
    (hD : (rhoOne N).degree ≠ D) : flagIntOne N q = 0 := by
  unfold flagIntOne
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [(hq.rename_isHomogeneous).coeff_eq_zero hD, mul_zero]

end FlagIntMuProd

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHookFactorBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem HookFactorBranch.proof (hV : VandermondeBranch.Statement) : HookFactorBranch.Statement := by
  intro j u
  set v : Fin j → ℚ := fun r => (u r : ℚ) with hv
  set P : ℚ := ∏ r, ((u r).factorial : ℚ) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r _ => by positivity
  have key := hV j v
  have hterm : ∀ p, (if 0 < u p ∧ ∀ q, u q ≠ u p - 1 then hookFactor (Function.update u p (u p - 1))
      else 0) = v p * (Matrix.vandermonde (Function.update v p (v p - 1))).det / P := by
    intro p
    split_ifs with h
    · obtain ⟨hp, -⟩ := h
      have hcast : (fun r => ((Function.update u p (u p - 1) r : ℕ) : ℚ)) =
          Function.update v p (v p - 1) := by
        funext r
        by_cases hr : r = p
        · subst hr
          simp [hv, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp.ne')]
        · simp [hr, hv]
      have hprod : (u p : ℚ) * ∏ r, ((Function.update u p (u p - 1) r).factorial : ℚ) = P := by
        rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p),
          ← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self, ← mul_assoc,
          ← Nat.cast_mul, Nat.mul_factorial_pred hp.ne']
        congr 1
        refine Finset.prod_congr rfl fun r hr => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hr)]
      have hup : (u p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
      unfold hookFactor
      rw [hcast, ← hprod, mul_div_mul_left _ _ hup]
    · by_cases hp : u p = 0
      · simp [hv, hp]
      · push Not at h
        obtain ⟨q, hq⟩ := h (Nat.pos_of_ne_zero hp)
        have hqp : q ≠ p := by
          rintro rfl
          omega
        have hdet : (Matrix.vandermonde (Function.update v p (v p - 1))).det = 0 := by
          refine Matrix.det_vandermonde_eq_zero_iff.mpr ⟨q, p, ?_, hqp⟩
          rw [Function.update_of_ne hqp, Function.update_self]
          simp only [hv, hq]
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp), Nat.cast_one]
        rw [hdet, mul_zero, zero_div]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_div, key]
  unfold hookFactor
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVandermondeBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Polynomial Finset Equiv

theorem VandermondeBranch.det_vandermonde_eq_descPochhammer {j : ℕ} (w : Fin j → ℚ) :
    (Matrix.vandermonde w).det =
      (Matrix.of (fun r s : Fin j => (descPochhammer ℚ (s : ℕ)).eval (w r))).det :=
  Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde w (fun s => descPochhammer ℚ (s : ℕ))
    (fun _ => descPochhammer_natDegree (R := ℚ) _) (fun _ => monic_descPochhammer (R := ℚ) _)

theorem VandermondeBranch.mul_eval_sub_one (k : ℕ) (x : ℚ) :
    x * (descPochhammer ℚ k).eval (x - 1) = (descPochhammer ℚ k).eval x * (x - k) := by
  rw [← descPochhammer_succ_eval, descPochhammer_succ_left]
  simp [eval_comp]

theorem VandermondeBranch.term {j : ℕ} (v : Fin j → ℚ) (σ : Perm (Fin j)) (i₀ : Fin j) :
    v (σ i₀) * ∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v (σ i₀) (v (σ i₀) - 1) (σ i)) =
      (∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval (v (σ i))) * (v (σ i₀) - (i₀ : ℕ)) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i₀), ← Finset.mul_prod_erase univ _ (mem_univ i₀)]
  have hrest : ∏ i ∈ univ.erase i₀, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v (σ i₀) (v (σ i₀) - 1) (σ i)) =
      ∏ i ∈ univ.erase i₀, (descPochhammer ℚ (i : ℕ)).eval (v (σ i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : σ i ≠ σ i₀ := fun h => (Finset.ne_of_mem_erase hi) (σ.injective h)
    rw [Function.update_of_ne hne]
  rw [hrest, Function.update_self, ← mul_assoc, VandermondeBranch.mul_eval_sub_one]
  ring

theorem VandermondeBranch.proof : VandermondeBranch.Statement := by
  intro j v
  simp only [VandermondeBranch.det_vandermonde_eq_descPochhammer]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ a, v a * (↑↑(Perm.sign σ) * ∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v a (v a - 1) (σ i))) =
      ↑↑(Perm.sign σ) * (v a * ∏ i : Fin j, (descPochhammer ℚ (i : ℕ)).eval
        (Function.update v a (v a - 1) (σ i))) := fun a => by ring
  simp only [h1]
  rw [← Finset.mul_sum, ← Equiv.sum_comp σ]
  simp only [VandermondeBranch.term, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Equiv.sum_comp σ v]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBlockAltUnique
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def BlockAltUnique.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ L : RootPoly Ψ N →ₗ[ℚ] ℚ,
    (∀ w, IsBlockPerm Ψ N j w → ∀ P, L (rename (weylAct Ψ N w) P) = weylSign Ψ N w * L P) →
    (∀ b : Ψ × Fin N →₀ ℕ, b.degree ≠ (rhoBlock Ψ N j).degree → L (monomial b 1) = 0) →
    ∀ P, L P = L (monomial (rhoBlock Ψ N j) 1) * blockInt Ψ N j P

example : ∃ L : RootPoly Unit 2 →ₗ[ℚ] ℚ, L ≠ 0 ∧
    (∀ w, IsBlockPerm Unit 2 1 w → ∀ P, L (rename (weylAct Unit 2 w) P) = weylSign Unit 2 w * L P) ∧
    (∀ b : Unit × Fin 2 →₀ ℕ, b.degree ≠ (rhoBlock Unit 2 1).degree → L (monomial b 1) = 0) := by
  have hrho : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  have hw : ∀ w : Unit → Equiv.Perm (Fin 2), IsBlockPerm Unit 2 1 w → w = 1 := by
    unfold IsBlockPerm
    decide
  refine ⟨lcoeff ℚ 0, fun h => ?_, fun w hw' P => ?_, fun b hb => ?_⟩
  · have := LinearMap.congr_fun h 1
    simp at this
  · obtain rfl := hw w hw'
    have h1 : weylAct Unit 2 1 = id := by
      funext p
      rfl
    simp [h1, weylSign]
  · rw [hrho, map_zero] at hb
    have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
    simp [coeff_monomial]
    exact hb0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

