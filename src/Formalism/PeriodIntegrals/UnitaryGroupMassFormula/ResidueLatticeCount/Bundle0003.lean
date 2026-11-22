import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0002

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.BClass
section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

theorem vfac_eq (K : Type) [Field K] [NumberField K] :
    vfac K = ENNReal.ofReal (2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K) := by
  rw [vfac, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_ofNat, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]

theorem classLower_of (hCI : CountIntegral) (hSV : ShellVolume) (hU : Unfold) (hH : HitBound)
    (hI : IdealSetSum) : ClassLower := by
  intro K _ _ s C hs
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  set m := Module.finrank ℚ K with hm
  have hm0 : 0 < m := Module.finrank_pos
  set D : ℝ := ((|discr K| : ℤ) : ℝ) with hD
  have hD0 : 0 < D := by
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
    have : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast this
    linarith
  have hsq : 0 < √D := Real.sqrt_pos.mpr hD0
  set N : ℝ := (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) with hN
  have hN0 : 0 < N := Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors J)
  set P : ℝ := 2 * √D * N with hP
  have hP0 : 0 < P := by positivity
  set ρ : ℝ := P ^ ((1 : ℝ) / m) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hP0 _
  have hρm : ρ ^ m = P := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le, one_div,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm0.ne'), Real.rpow_one]
  have hcov : ZLattice.covolume (lat K J) = N * 2⁻¹ ^ nrComplexPlaces K * √D := by
    rw [covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
      Rat.cast_natCast, ← Int.cast_abs]
  have hcov0 : 0 < ZLattice.covolume (lat K J) := by rw [hcov]; positivity
  set c := ENNReal.ofReal (ZLattice.covolume (lat K J)) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.mpr hcov0).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hv0 : vfac K ≠ 0 := by
    rw [vfac_eq]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvT : vfac K ≠ ⊤ := by rw [vfac_eq]; exact ENNReal.ofReal_ne_top
  set S := volume (shell K) with hS
  have hSe : S = vfac K * ENNReal.ofReal (regulator K) / 2 := hSV K
  have hST : S ≠ ⊤ := by
    rw [hSe]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hvT ENNReal.ofReal_ne_top) (by norm_num)
  set T := ∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K)) with hT
  have h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S ≤ T * c := hCI K J ρ hρ0
  have h2 : 2 * c ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m) := by
    rw [vfac_eq, ← ENNReal.ofReal_mul (by positivity), hc,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [hcov, div_pow, hρm, hP, hm, ← card_add_two_mul_card_eq_rank K, pow_add, pow_mul]
    have h4 : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ (Real.pi / 4) ^ nrComplexPlaces K :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _
    have e : (2 : ℝ) ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K *
        (2 * √D * N / (2 ^ nrRealPlaces K * (2 ^ 2) ^ nrComplexPlaces K)) =
        2 * (N * (Real.pi / 4) ^ nrComplexPlaces K * √D) := by
      rw [div_pow]; norm_num; field_simp
    rw [e]
    gcongr
  have h3 : 2 * S ≤ T := by
    have : 2 * S * c ≤ T * c := by
      calc 2 * S * c = 2 * c * S := by ring
        _ ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S := by gcongr
        _ ≤ T * c := h1
    exact (ENNReal.mul_le_mul_iff_left hc0 hcT).1 this
  set Z : ℝ≥0∞ := ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
    ((torsionOrder K : ℝ≥0∞) * ENNReal.ofReal (N ^ (-s)) * classZeta K C s) with hZ
  have h4 : T ≤ S + vfac K * Z := by
    refine (hU K J ρ hρ0).trans ?_
    gcongr
    calc ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K))
        ≤ ∑' x : idealSet K J, vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
            ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          have := hH K ρ s (x : mixedSpace K) hρ0 hs (norm_pos_of_mem x.2.1)
          rwa [← hm, hρm, ENNReal.ofReal_mul (by positivity)] at this
      _ = vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
            ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ vfac K * Z := by
          rw [hZ]; gcongr; exact hI K s C J hJ
  have h5 : S ≤ vfac K * Z := by
    have : S + S ≤ S + vfac K * Z := by rw [← two_mul]; exact h3.trans h4
    exact (ENNReal.add_le_add_iff_left hST).1 this
  have h6 : ENNReal.ofReal (regulator K) ≤ 2 * Z := by
    rw [hSe, ENNReal.div_le_iff (by norm_num) (by norm_num), mul_assoc] at h5
    have := (ENNReal.mul_le_mul_iff_right hv0 hvT).1 h5
    rwa [mul_comm] at this
  refine h6.trans (le_of_eq ?_)
  rw [hZ, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : 2 * (P * (2 * P) ^ (s - 1)) = (2 * P) ^ s := by
    rw [← mul_assoc]
    nth_rewrite 1 [← Real.rpow_one (2 * P)]
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have e2 : (2 * P) ^ s * N ^ (-s) = 4 ^ s * D ^ (s / 2) := by
    have : 2 * P = 4 * √D * N := by rw [hP]; ring
    rw [this, Real.mul_rpow (by positivity) hN0.le, Real.mul_rpow (by norm_num) hsq.le, mul_assoc,
      ← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero, mul_one, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hD0.le]
    congr 2; ring
  rw [e1, mul_right_comm, e2]

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.BUnfold
section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable {K : Type} [Field K] [NumberField K]

theorem mem_lat {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ lat K J ↔ ∃ a : 𝓞 K, a ∈ (J : Ideal (𝓞 K)) ∧ mixedEmbedding K (a : K) = x := by
  rw [lat, mem_idealLattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    exact ⟨a, ha, rfl⟩

theorem smul_mem_lat {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} (u : (𝓞 K)ˣ) (hx : x ∈ lat K J) :
    u • x ∈ lat K J := by
  obtain ⟨a, ha, rfl⟩ := mem_lat.1 hx
  refine mem_lat.2 ⟨u * a, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [unitSMul_smul]
  simp [map_mul]

theorem measurableSet_shell' : MeasurableSet (shell K) := by
  have h1 : MeasurableSet {y : mixedSpace K | 1 / 2 < mixedEmbedding.norm y} :=
    (isOpen_lt continuous_const (mixedEmbedding.continuous_norm K)).measurableSet
  have h2 : MeasurableSet {y : mixedSpace K | mixedEmbedding.norm y ≤ 1} :=
    (isClosed_le (mixedEmbedding.continuous_norm K) continuous_const).measurableSet
  exact (measurableSet_fundamentalCone K).inter (h1.inter h2)

theorem measurableSet_hit' (ρ : ℝ) (x : mixedSpace K) : MeasurableSet (hit K ρ x) := by
  have : hit K ρ x = ⋂ w, {y | normAtPlace w y * normAtPlace w x < ρ} := by
    ext y; simp [hit]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    (isOpen_lt ((continuous_normAtPlace w).mul continuous_const) continuous_const).measurableSet

theorem mem_hit_smul (ρ : ℝ) (u : (𝓞 K)ˣ) (x y : mixedSpace K) :
    y ∈ hit K ρ (u • x) ↔ u • y ∈ hit K ρ x := by
  simp only [hit, Set.mem_ofPred_eq, unitSMul_smul, map_mul]
  refine forall_congr' fun w => ?_
  rw [mul_left_comm, mul_assoc]

def urep (g : (𝓞 K)ˣ ⧸ torsion K) : (𝓞 K)ˣ := Quotient.out g

def Fv (ρ : ℝ) (x : mixedSpace K) : ℝ≥0∞ := volume (shell K ∩ hit K ρ x)

theorem exists_rep {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} (hx : x ∈ lat K J) (hx0 : x ≠ 0) :
    ∃ x1 ∈ idealSet K J, ∃ g : (𝓞 K)ˣ ⧸ torsion K, urep g • x1 = x := by
  have hnx : mixedEmbedding.norm x ≠ 0 := by
    obtain ⟨a, _, rfl⟩ := mem_lat.1 hx
    exact fun h => hx0 ((norm_eq_zero_iff' ⟨_, rfl⟩).1 h)
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hnx
  obtain ⟨ζ, hζ⟩ := QuotientGroup.mk_out_eq_mul (torsion K) u⁻¹
  have hζ' : (ζ : (𝓞 K)ˣ)⁻¹ ∈ torsion K := inv_mem ζ.2
  refine ⟨(ζ : (𝓞 K)ˣ)⁻¹ • (u • x), ⟨torsion_smul_mem_of_mem hu hζ',
    smul_mem_lat _ (smul_mem_lat _ hx)⟩, QuotientGroup.mk u⁻¹, ?_⟩
  rw [urep, hζ, ← mul_smul, ← mul_smul]
  simp

theorem fib_le (hUP : UnitPreserving) (ρ : ℝ) (x1 : mixedSpace K) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K, Fv ρ (urep g • x1) ≤
      volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x1) := by
  let A : (𝓞 K)ˣ ⧸ torsion K → Set (mixedSpace K) := fun g =>
    (fun z : mixedSpace K => (urep g)⁻¹ • z) ⁻¹' shell K ∩ hit K ρ x1
  have hAm : ∀ g, MeasurableSet (A g) := fun g =>
    ((hUP K (urep g)⁻¹).measurable measurableSet_shell').inter (measurableSet_hit' _ _)
  have hFA : ∀ g, Fv ρ (urep g • x1) = volume (A g) := by
    intro g
    have e : shell K ∩ hit K ρ (urep g • x1) = (fun y : mixedSpace K => urep g • y) ⁻¹' A g := by
      ext y
      simp only [A, Set.mem_inter_iff, Set.mem_preimage, mem_hit_smul, inv_smul_smul]
    rw [Fv, e, (hUP K (urep g)).measure_preimage (hAm g).nullMeasurableSet]
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro g g' hgg
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨hz, _⟩ ⟨hz', _⟩
    apply hgg
    have h1 : (urep g)⁻¹ • z ∈ fundamentalCone K := hz.1
    have h2 : (urep g')⁻¹ • z ∈ fundamentalCone K := hz'.1
    have h3 : ((urep g')⁻¹ * urep g) • ((urep g)⁻¹ • z) ∈ fundamentalCone K := by
      rw [← mul_smul]; simpa using h2
    have h4 := (unit_smul_mem_iff_mem_torsion h1 _).1 h3
    have h5 : (QuotientGroup.mk (urep g') : (𝓞 K)ˣ ⧸ torsion K) = QuotientGroup.mk (urep g) :=
      QuotientGroup.eq.2 h4
    rw [urep, urep, QuotientGroup.out_eq', QuotientGroup.out_eq'] at h5
    exact h5.symm
  calc ∑' g, Fv ρ (urep g • x1) = ∑' g, volume (A g) := tsum_congr hFA
    _ ≤ volume (⋃ g, A g) := tsum_meas_le_meas_iUnion_of_disjoint volume hAm hdisj
    _ ≤ _ := by
        refine measure_mono (Set.iUnion_subset fun g => ?_)
        rintro z ⟨hz, hz'⟩
        refine ⟨?_, hz'⟩
        have : 1 / 2 < mixedEmbedding.norm ((urep g)⁻¹ • z) := hz.2.1
        rwa [norm_unit_smul] at this

theorem sum_ne_zero_le (J : (Ideal (𝓞 K))⁰) (F : mixedSpace K → ℝ≥0∞) :
    ∑' x : {x : lat K J // x ≠ 0}, F ((x : lat K J) : mixedSpace K) ≤
      ∑' p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K), F (urep p.2 • (p.1 : mixedSpace K)) := by
  have hex : ∀ x : {x : lat K J // x ≠ 0}, ∃ p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K),
      urep p.2 • (p.1 : mixedSpace K) = ((x : lat K J) : mixedSpace K) := by
    rintro ⟨⟨x, hx⟩, hx0⟩
    obtain ⟨x1, h1, g, hg⟩ := exists_rep hx (fun h => hx0 (Subtype.ext h))
    exact ⟨(⟨x1, h1⟩, g), hg⟩
  choose p hp using hex
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext; apply Subtype.ext
    rw [← hp x, ← hp y, hxy]
  calc _ = ∑' x : {x : lat K J // x ≠ 0}, F (urep (p x).2 • ((p x).1 : mixedSpace K)) :=
        tsum_congr fun x => by rw [hp x]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj
        (fun p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K) => F (urep p.2 • (p.1 : mixedSpace K)))

theorem tsum_eq_zero_add_ne {α : Type*} [Zero α] (f : α → ℝ≥0∞) :
    ∑' x, f x = f 0 + ∑' x : {x : α // x ≠ 0}, f x := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  change _ = f 0 + ∑' x : ↑{x : α | x ≠ 0}, f x
  rw [tsum_subtype {x : α | x ≠ 0} f]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases h : x = 0 <;> simp [h]

theorem Fv_le (ρ : ℝ) (x : mixedSpace K) : Fv ρ x ≤ volume (shell K) := by
  rw [Fv]; exact measure_mono Set.inter_subset_left

theorem lattice_sum_le_shell_volume (hUP : UnitPreserving) (J : (Ideal (𝓞 K))⁰) (ρ : ℝ) :
    ∑' x : lat K J, Fv ρ (x : mixedSpace K) ≤
      volume (shell K) +
        ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K)) := by
  rw [tsum_eq_zero_add_ne (fun x : lat K J => Fv ρ (x : mixedSpace K))]
  refine add_le_add (Fv_le ρ _) ?_
  refine (sum_ne_zero_le J (Fv ρ)).trans ?_
  rw [ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun x1 => ?_
  dsimp only
  exact fib_le hUP ρ (x1 : mixedSpace K)

theorem unfold_of (hUP : UnitPreserving) : Unfold :=
  fun _ _ _ J ρ _ => lattice_sum_le_shell_volume hUP J ρ

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.BoxEqConvexBodyLT
section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace PI.Residue

theorem box_eq_convexBodyLT (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ)
    (hr : ∀ w, 0 < r w) : box K r = convexBodyLT K (fun w => (r w).toNNReal) := by
  ext y
  simp only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall, Real.coe_toNNReal _ (hr _).le]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · simpa [normAtPlace_apply_of_isReal hw] using h w
    · simpa [normAtPlace_apply_of_isComplex hw] using h w
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw

theorem boxVolume : BoxVolume := by
  intro K _ _ r hr
  rw [box_eq_convexBodyLT K r hr, convexBodyLT_volume, vfac]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => (pow_pos (hr w) _).le)]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_pow (hr w).le]
  rfl

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.DvdSpanOfIdealSet
section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace PI.Residue

variable {K : Type} [Field K] [NumberField K]

theorem dvd_span_of_idealSet (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    (J : Ideal (𝓞 K)) ∣ Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} := by
  rw [Ideal.dvd_span_singleton]
  exact preimage_of_IdealSetMap K J x

def cof (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) : Ideal (𝓞 K) :=
  (dvd_span_of_idealSet J x).choose

theorem cof_spec (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} = (J : Ideal (𝓞 K)) * cof J x :=
  (dvd_span_of_idealSet J x).choose_spec

theorem cof_mem (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) : cof J x ∈ (Ideal (𝓞 K))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have h1 := cof_spec J x
  rw [h, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h1
  exact nonZeroDivisors.coe_ne_zero _ h1

theorem cof_class (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) (C : ClassGroup (𝓞 K))
    (hJ : ClassGroup.mk0 J = C⁻¹) : ClassGroup.mk0 ⟨cof J x, cof_mem J x⟩ = C := by
  have h1 : ClassGroup.mk0 (J * ⟨cof J x, cof_mem J x⟩) = 1 := by
    rw [ClassGroup.mk0_eq_one_iff]
    have : ((J * ⟨cof J x, cof_mem J x⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
        Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} := (cof_spec J x).symm
    rw [this]
    exact ⟨⟨_, rfl⟩⟩
  rw [map_mul, hJ] at h1
  exact (inv_mul_eq_one.mp h1).symm

theorem norm_eq_cof (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    mixedEmbedding.norm (x : mixedSpace K) =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * (Ideal.absNorm (cof J x) : ℝ) := by
  rw [← Nat.cast_mul, ← map_mul, ← cof_spec, Ideal.absNorm_span_singleton,
    ← idealSetMap_apply K J x, ← intNorm_coe, intNorm]

def toPair (J : (Ideal (𝓞 K))⁰) (C : ClassGroup (𝓞 K)) (hJ : ClassGroup.mk0 J = C⁻¹)
    (x : idealSet K J) : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K :=
  (⟨⟨cof J x, cof_mem J x⟩, cof_class J x C hJ⟩, (integerSetEquiv K (idealSetMap K J x)).2)

theorem toPair_injective (J : (Ideal (𝓞 K))⁰) (C : ClassGroup (𝓞 K))
    (hJ : ClassGroup.mk0 J = C⁻¹) : Function.Injective (toPair J C hJ) := by
  intro x y h
  have h1 : cof J x = cof J y := by
    have := congrArg (fun p => ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) h
    exact this
  have h2 : (integerSetEquiv K (idealSetMap K J x)).2 = (integerSetEquiv K (idealSetMap K J y)).2 :=
    congrArg (fun p : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K => p.2) h
  have h3 : (integerSetEquiv K (idealSetMap K J x)).1 = (integerSetEquiv K (idealSetMap K J y)).1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [integerSetEquiv_apply_fst, integerSetEquiv_apply_fst, cof_spec, cof_spec, h1]
  have h4 : idealSetMap K J x = idealSetMap K J y := (integerSetEquiv K).injective (Prod.ext h3 h2)
  apply Subtype.ext
  rw [← idealSetMap_apply K J x, ← idealSetMap_apply K J y, h4]

theorem idealSetSum : IdealSetSum := by
  intro K _ _ s C J hJ
  set g : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-s)) *
      ENNReal.ofReal ((Ideal.absNorm ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) with hg
  have h1 : ∀ x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s)) =
      g (toPair J C hJ x) := by
    intro x
    rw [norm_eq_cof, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (by positivity)]
    rfl
  calc ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))
      = ∑' x : idealSet K J, g (toPair J C hJ x) := tsum_congr h1
    _ ≤ ∑' p, g p := ENNReal.tsum_comp_le_tsum_of_injective (toPair_injective J C hJ) g
    _ = _ := by
      rw [ENNReal.tsum_prod', classZeta, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun I => ?_
      have : Fintype (torsion K) := Fintype.ofFinite _
      rw [tsum_fintype]
      simp only [hg]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
        Nat.card_eq_fintype_card, mul_assoc]

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLowerOf
section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

theorem heckeLower_of (hCL : ClassLower) (hCS : ClassSum) : HeckeLower := by
  intro E _ _ s hs hsum
  set D : ℝ := ((|discr E| : ℤ) : ℝ) with hD
  have hD1 : 1 ≤ D := by
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
    rw [hD]; exact_mod_cast this
  have hD0 : 0 < D := by linarith
  set A : ℝ := (4 : ℝ) ^ s * D ^ (s / 2) * torsionOrder E with hA
  have hz0 : 0 ≤ idealZeta E s := tsum_nonneg fun _ => by positivity
  have hA0 : 0 ≤ A := by positivity
  have hR0 : 0 ≤ regulator E := (regulator_pos E).le
  have h1 : (classNumber E : ℝ≥0∞) * ENNReal.ofReal (regulator E) ≤
      ENNReal.ofReal (A * idealZeta E s) := by
    calc _ = ∑ _C : ClassGroup (𝓞 E), ENNReal.ofReal (regulator E) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
      _ ≤ ∑ C, ENNReal.ofReal A * classZeta E C s := Finset.sum_le_sum fun C _ => hCL E s C hs
      _ = ENNReal.ofReal A * ∑ C, classZeta E C s := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (idealZeta E s) := by gcongr; exact hCS E s hsum
      _ = _ := (ENNReal.ofReal_mul hA0).symm
  have h2 : (classNumber E : ℝ) * regulator E ≤ A * idealZeta E s := by
    have : ENNReal.ofReal ((classNumber E : ℝ) * regulator E) ≤
        ENNReal.ofReal (A * idealZeta E s) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; exact h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hpow : D ^ (s / 2) = D ^ ((s - 1) / 2) * √D := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD0]; congr 1; ring
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hfac : (2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E ≤
      (2 * Real.pi) ^ Module.finrank ℚ E := by
    rw [← card_add_two_mul_card_eq_rank E, pow_add]
    have h3 : (2 : ℝ) ^ nrRealPlaces E ≤ (2 * Real.pi) ^ nrRealPlaces E :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _
    have h4 : (2 * Real.pi) ^ nrComplexPlaces E ≤ (2 * Real.pi) ^ (2 * nrComplexPlaces E) :=
      pow_le_pow_right₀ hpi (by omega)
    exact mul_le_mul h3 h4 (by positivity) (by positivity)
  have hw : (0 : ℝ) < torsionOrder E := Nat.cast_pos.mpr (torsionOrder_pos E)
  have hsq : 0 < √D := Real.sqrt_pos.mpr hD0
  rw [dedekindZeta_residue_def, ← Int.cast_abs, ← hD, div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E * regulator E * classNumber E
      = ((2 : ℝ) ^ nrRealPlaces E * (2 * Real.pi) ^ nrComplexPlaces E) *
          ((classNumber E : ℝ) * regulator E) := by ring
    _ ≤ (2 * Real.pi) ^ Module.finrank ℚ E * (A * idealZeta E s) :=
        mul_le_mul hfac h2 (by positivity) (by positivity)
    _ = _ := by rw [hA, hpow]; ring

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.IdealEquiv
section
open NumberField
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace PI.Residue

def idealEquiv (K : Type) [Field K] [NumberField K] :
    (Ideal (𝓞 K))⁰ ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  Equiv.subtypeEquivRight fun I => by rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot]

theorem classSum : ClassSum := by
  intro K _ _ s hs
  have h1 : ∑ C : ClassGroup (𝓞 K), classZeta K C s =
      ∑' I : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
    rw [← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).tsum_eq,
      ENNReal.tsum_sigma', tsum_fintype]
    rfl
  rw [h1, idealZeta, ENNReal.ofReal_tsum_of_nonneg (fun I => by positivity) hs,
    ← (idealEquiv K).tsum_eq]
  exact le_of_eq rfl

end PI.Residue
end
end

