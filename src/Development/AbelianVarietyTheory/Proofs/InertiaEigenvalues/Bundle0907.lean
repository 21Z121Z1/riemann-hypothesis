import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0899
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShells
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaGeom

theorem integral_low_geometric : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕 F hF C hC hinv χ hχ hχF s hs
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef
  set e : GA E a := splitCentre E a 1 with he
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  have hd0 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  have hL : 0 < L := mul_pos (Nat.cast_pos.2 ha) hd0
  have hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L := by
    rw [Real.exp_one_pow, hLdef]; push_cast; rfl
  have hδk : ∀ (k : ℕ) g, δ (e ^ k * g) = Real.exp (L * k) * δ g := fun k g => by
    have h := GlobalTheory.RSTheta.absDet_zpow_mul (E := E) (a := a) (k : ℤ) g
    rw [zpow_natCast, hTL, zpow_natCast, ← Real.exp_nat_mul, mul_comm (k : ℝ)] at h
    exact h
  have hFk : ∀ (k : ℕ) g, F (e ^ k * g) = χ ^ k * F g := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', mul_assoc, hχF, ih, pow_succ']; ring

  set f : GA E a → ℂ := fun g => F g * ((δ g : ℝ) : ℂ) ^ (s - 1) with hf
  have hfc : Continuous f := hF.mul ((Complex.continuous_ofReal.comp hδc).cpow continuous_const
    fun g => Complex.ofReal_mem_slitPlane.2 (hδ0 g))
  have hfr : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    simp only [hf, hinv, hδr]

  set S : ℕ → Set (GA E a) := fun k => {g | Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))} with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (isOpen_lt continuous_const hδc).measurableSet.inter (isClosed_le hδc continuous_const).measurableSet

  have hSU : (⋃ k, S k) = {g | δ g ≤ 1} := by
    ext g
    simp only [hS, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, -, h2⟩
      exact h2.trans (Real.exp_le_one_iff.2 (by have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith))
    · intro h
      have hl : 0 ≤ -Real.log (δ g) / L := div_nonneg (neg_nonneg.2 (Real.log_nonpos (hδ0 g).le h)) hL.le
      have h1 := Nat.lt_floor_add_one (-Real.log (δ g) / L)
      have h2 := Nat.floor_le hl
      set k := ⌊-Real.log (δ g) / L⌋₊
      refine ⟨k, ?_, ?_⟩
      ·
        rw [div_lt_iff₀ hL] at h1
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_lt_exp.2 (by linarith)
      · rw [le_div_iff₀ hL] at h2
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_le_exp.2 (by linarith)
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    have key : ∀ j k : ℕ, j < k → Disjoint (S j) (S k) := by
      intro j k hjk
      refine Set.disjoint_left.2 fun g hj hk => ?_
      have h1 : Real.exp (-(L * k)) ≤ Real.exp (-(L * ((j : ℝ) + 1))) := by
        refine Real.exp_le_exp.2 ?_
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        nlinarith
      exact absurd (hk.2.trans h1) (not_le.2 hj.1)
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h
    · exact (key k j h).symm

  have hint : IntegrableOn f (𝓕 ∩ {g | δ g ≤ 1}) μ := by
    have h0 := (GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ha μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C
    refine h0.mono' hfc.aestronglyMeasurable.restrict (.of_forall fun g => ?_)
    rw [hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ0 g)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (hC g) (Real.rpow_nonneg (hδ0 g).le _)
  have hsum1 := hasSum_integral_iUnion (μ := μ.restrict 𝓕) (f := f) hSm hSd
    (by rw [hSU, IntegrableOn, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet,
      Set.inter_comm]; exact hint)
  rw [hSU, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet, Set.inter_comm] at hsum1

  set r : ℂ := starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) with hr
  have hr1 : ‖r‖ < 1 := by
    have hre : (-(((L : ℝ) : ℂ) * (s - 1))).re = -(L * (s.re - 1)) := by simp
    have hpos : 0 < L * (s.re - 1) := mul_pos hL (by linarith)
    rw [hr, norm_mul, Complex.norm_conj, hχ, one_mul, Complex.norm_exp, hre]
    exact (Real.exp_lt_exp.2 (by linarith : -(L * (s.re - 1)) < 0)).trans_eq Real.exp_zero
  have hcancel : ∀ k : ℕ, r ^ k * (χ ^ k * Complex.exp (((L * k : ℝ) : ℂ) * (s - 1))) = 1 := by
    intro k
    have hc : starRingEnd ℂ χ * χ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]; simp
    have he1 : Complex.exp (((L * k : ℝ) : ℂ) * (s - 1)) = Complex.exp (((L : ℝ) : ℂ) * (s - 1)) ^ k := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [he1, ← mul_pow, ← mul_pow, hr]
    have : starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * (χ * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) =
        (starRingEnd ℂ χ * χ) * (Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) := by ring
    rw [this, hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; simp

  haveI : Countable (ratGL E a).range := by
    haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
    haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
    exact (ratGL E a).rangeRestrict_surjective.countable
  have hexp : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((t : ℝ) : ℂ) * (s - 1)) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
      Real.log_exp]
  have hfd : ∀ k : ℕ, IsFundamentalDomain (ratGL E a).range ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) μ := by
    intro k
    refine h𝓕.preimage_of_equiv (measurePreserving_mul_left μ ((e ^ k)⁻¹)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    have hc0 : Commute e (γ : GA E a) := CuspidalL2GL.splitCentre_comm 1 _
    have hc : Commute ((e ^ k)⁻¹) (γ : GA E a) := (hc0.pow_left k).inv_left
    show (e ^ k)⁻¹ * ((γ : GA E a) * x) = (γ : GA E a) * ((e ^ k)⁻¹ * x)
    rw [← mul_assoc, hc.eq, mul_assoc]
  have hG0 : ∀ (γ : (ratGL E a).range) (x : GA E a), (S 0).indicator f (γ • x) = (S 0).indicator f x := by
    rintro ⟨_, γ, rfl⟩ x
    show (S 0).indicator f (ratGL E a γ * x) = (S 0).indicator f x
    simp only [Set.indicator_apply, hS, Set.mem_setOf_eq, hδr, hfr]
  have hshell : ∀ k : ℕ, ∫ g in S k, f g ∂(μ.restrict 𝓕) = r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) := by
    intro k
    have hX : 0 < Real.exp (L * k) := Real.exp_pos _
    have hmem : ∀ g, g ∈ S k ↔ e ^ k * g ∈ S 0 := by
      intro g
      have e1 : Real.exp (L * k) * Real.exp (-(L * ((k : ℝ) + 1))) = Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have e2 : Real.exp (L * k) * Real.exp (-(L * k)) = Real.exp (-(L * ((0 : ℕ) : ℝ))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      show (Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))) ↔
        (Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) < δ (e ^ k * g) ∧ δ (e ^ k * g) ≤ Real.exp (-(L * ((0 : ℕ) : ℝ))))
      rw [hδk, ← e1, ← e2, mul_lt_mul_iff_of_pos_left hX, mul_le_mul_iff_of_pos_left hX]
    have hpt : ∀ g, (S k).indicator f g = r ^ k * (S 0).indicator f (e ^ k * g) := by
      intro g
      by_cases hg : g ∈ S k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hmem g).1 hg)]
        simp only [hf, hFk, hδk]
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (hδ0 g).le, hexp]
        linear_combination (-(F g * ((δ g : ℝ) : ℂ) ^ (s - 1))) * hcancel k
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hmem g).2 hg), mul_zero]
    have hpre : (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) = 𝓕 := by ext x; simp
    rw [← integral_indicator (hSm k), ← integral_indicator (hSm 0), integral_congr_ae (.of_forall hpt),
      integral_const_mul]
    congr 1
    calc ∫ g in 𝓕, (S 0).indicator f (e ^ k * g) ∂μ
        = ∫ g in (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕), (S 0).indicator f (e ^ k * g) ∂μ := by
          rw [hpre]
      _ = ∫ y in (fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕, (S 0).indicator f y ∂μ :=
          (measurePreserving_mul_left μ (e ^ k)).setIntegral_preimage_emb (measurableEmbedding_mulLeft _) _ _
      _ = ∫ y in 𝓕, (S 0).indicator f y ∂μ := (hfd k).setIntegral_eq h𝓕 hG0
  have hgeo := (hasSum_geometric_of_norm_lt_one hr1).mul_right (∫ g in S 0, f g ∂(μ.restrict 𝓕))
  have hsum2 : HasSum (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕))
      ((1 - r)⁻¹ * ∫ g in S 0, f g ∂(μ.restrict 𝓕)) := by
    rw [show (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕)) = fun k => r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) from
      funext hshell]
    exact hgeo
  have hS0 : S 0 = {g | Real.exp (-L) < δ g ∧ δ g ≤ 1} := by
    ext g; simp [hS]
  have hI0 : ∫ g in S 0, f g ∂(μ.restrict 𝓕) = ∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ := by
    rw [Measure.restrict_restrict (hSm 0), Set.inter_comm, hS0]
  show ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, f g ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ) / (1 - r)
  rw [← hI0, hsum1.unique hsum2, div_eq_inv_mul]

end GlobalTheory.RSThetaGeom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGL
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ShellFD

theorem isFundamentalDomain_shell : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hT0 : 0 < T := one_pos.trans hT1
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hTe : Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) = T ^ (-1 : ℤ) := by
    rw [hT, Real.exp_one_pow, _root_.zpow_neg_one, ← Real.exp_neg]
    push_cast
    rfl
  have hcomm : ∀ (n : ℤ) g, splitCentre E a 1 ^ n * g = g * splitCentre E a 1 ^ n := fun n g => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
    exact GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ g
  have hTadd : ∀ m n : ℤ, T ^ m * T ^ n = T ^ (m + n) := fun m n => (zpow_add₀ hT0.ne' m n).symm
  rw [hTe]
  refine
    { nullMeasurableSet := h𝓕.nullMeasurableSet.inter
        ((measurableSet_lt measurable_const hδc.measurable).inter
          (measurableSet_le hδc.measurable measurable_const)).nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have hN := ae_iff.1 h𝓕.ae_covers
    have hB : μ (⋃ n : ℤ, (fun x => splitCentre E a 1 ^ n * x) ⁻¹'
        {x | ¬∃ γ : (ratGL E a).range, γ • x ∈ 𝓕}) = 0 :=
      measure_iUnion_null fun n => (measurePreserving_mul_left μ _).quasiMeasurePreserving.preimage_null hN
    refine Filter.mem_of_superset (compl_mem_ae_iff.2 hB) fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq, not_exists, not_not] at hx
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow (hδ0 x) hT1
    obtain ⟨γ, hγ⟩ := not_forall_not.1 (hx (-(m + 1)))
    obtain ⟨γ0, hγ0⟩ := γ.2
    refine ⟨⟨(γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)),
      mul_mem (Subgroup.mem_sup_left γ.2) (GlobalTheory.CuspRep.CuspidalL2GL.zpow_mem_latticeGL _)⟩, ?_, ?_, ?_⟩
    · rw [Subgroup.smul_def]
      simpa only [Subgroup.smul_def, smul_eq_mul, mul_assoc] using hγ
    · rw [Subgroup.smul_def]
      change T ^ (-1 : ℤ) < δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x)
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-1 : ℤ) = T ^ (-(m + 1)) * T ^ m := by rw [hTadd]; ring_nf
        _ < T ^ (-(m + 1)) * δ x := mul_lt_mul_of_pos_left hm1 (zpow_pos hT0 _)
    · rw [Subgroup.smul_def]
      change δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x) ≤ 1
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-(m + 1)) * δ x ≤ T ^ (-(m + 1)) * T ^ (m + 1) := mul_le_mul_of_nonneg_left hm2 (zpow_pos hT0 _).le
        _ = 1 := by rw [hTadd]; simp
  · intro g1 g2 hne
    have key : ∀ (g : latticeGL E a) (γ : GL (Fin a) E) (n : ℤ),
        ratGL E a γ * splitCentre E a 1 ^ n = g → ∀ y ∈ g • (𝓕 ∩ {g | T ^ (-1 : ℤ) < δ g ∧ δ g ≤ 1}),
        T ^ (n - 1) < δ y ∧ δ y ≤ T ^ n ∧
          y ∈ splitCentre E a 1 ^ n • ((⟨ratGL E a γ, γ, rfl⟩ : (ratGL E a).range) • 𝓕) := by
      rintro g γ n hg y ⟨x, ⟨hx, hx1, hx2⟩, rfl⟩
      have hy : g • x = splitCentre E a 1 ^ n * (ratGL E a γ * x) := by
        rw [Subgroup.smul_def, smul_eq_mul, ← hg, hcomm n (ratGL E a γ * x)]
        simp only [mul_assoc, hcomm n x]
      beta_reduce
      rw [hy]
      refine ⟨?_, ?_, Set.smul_mem_smul_set (Set.smul_mem_smul_set hx)⟩
      · rw [hδz, hδr]
        calc T ^ (n - 1) = T ^ n * T ^ (-1 : ℤ) := by rw [hTadd]; ring_nf
          _ < T ^ n * δ x := mul_lt_mul_of_pos_left hx1 (zpow_pos hT0 _)
      · rw [hδz, hδr]
        calc T ^ n * δ x ≤ T ^ n * 1 := mul_le_mul_of_nonneg_left hx2 (zpow_pos hT0 _).le
          _ = T ^ n := mul_one _
    obtain ⟨γ1, n1, h1⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g1.2
    obtain ⟨γ2, n2, h2⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g2.2
    by_cases hn : n1 = n2
    · subst hn
      have hγ : (⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) ≠ ⟨ratGL E a γ2, γ2, rfl⟩ := fun h => hne <|
        Subtype.ext (by rw [← h1, ← h2, show ratGL E a γ1 = ratGL E a γ2 from congrArg Subtype.val h])
      have hd : AEDisjoint μ (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) • 𝓕))
          (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ2, γ2, rfl⟩ : (ratGL E a).range) • 𝓕)) := by
        rw [AEDisjoint, ← Set.smul_set_inter, measure_smul]
        exact h𝓕.aedisjoint hγ
      exact hd.mono (fun y hy => (key g1 γ1 n1 h1 y hy).2.2) (fun y hy => (key g2 γ2 n1 h2 y hy).2.2)
    · refine Disjoint.aedisjoint (Set.disjoint_left.2 fun y hy1 hy2 => ?_)
      obtain ⟨a1, b1, -⟩ := key g1 γ1 n1 h1 y hy1
      obtain ⟨a2, b2, -⟩ := key g2 γ2 n2 h2 y hy2
      rcases lt_or_gt_of_ne hn with h | h
      · exact absurd a2 (not_lt.2 (b1.trans (zpow_le_zpow_right₀ hT1.le (by omega : n1 ≤ n2 - 1))))
      · exact absurd a1 (not_lt.2 (b2.trans (zpow_le_zpow_right₀ hT1.le (by omega : n2 ≤ n1 - 1))))

end GlobalTheory.ShellFD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSubCharValuesOfCyclotomicGenerator
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory.CharacterUnits

theorem unit_pow_sub_isUnit {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ)
    (hu : orderOf (PadicInt.toZMod (u : ℤ_[l])) = l - 1)
    (a b : ℕ) (ha : a < l - 1) (hb : b < l - 1) (hab : a ≠ b) :
    IsUnit ((u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b) := by
  by_contra h
  have h1 : (u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b ∈ IsLocalRing.maximalIdeal ℤ_[l] := h
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_pow, sub_eq_zero] at h1
  exact hab (pow_injOn_Iio_orderOf (by rw [hu]; exact ha) (by rw [hu]; exact hb) h1)

theorem chi_sub_isUnit : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (g0 : G H.E N.Om), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 → R.t + 1 < N.l i → ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b → IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)) := by
  intro R H what₂ N i g0 hε hl a ha b hb hab
  rw [Finset.mem_Icc] at ha hb
  set e : (N.O i)ˣ := Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom
    (cycZ (F := H.E) (Ω := N.Om) (N.l i) g0) with he_def
  have h3 : ∀ c, 1 ≤ c → c ≤ R.t → N.chi i c g0 = N.chi i 1 g0 * (e⁻¹ ^ (c - 1)) := by
    intro c h1 h2
    rw [N.chi_def i c h1 h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((c : ℕ) : ℤ) - 1)) = -(((c - 1 : ℕ) : ℤ)) := by omega
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  have hu := (unit_pow_sub_isUnit _ hε (b - 1) (a - 1) (by omega) (by omega)
    (by omega)).map (algebraMap ℤ_[N.l i] (N.O i))
  rw [map_sub, map_pow, map_pow] at hu
  have he : algebraMap ℤ_[N.l i] (N.O i) ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      ((e : (N.O i)ˣ) : N.O i) := rfl
  rw [he] at hu
  rw [h3 a ha.1 ha.2, h3 b hb.1 hb.2]
  set x := N.chi i 1 g0
  have a1 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1) * (e : N.O i) ^ (a - 1) = 1 := by rw [← mul_pow]; simp
  have a2 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1) * (e : N.O i) ^ (b - 1) = 1 := by rw [← mul_pow]; simp
  have key : ((x * e⁻¹ ^ (a - 1) : (N.O i)ˣ) : N.O i) - ((x * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) =
      ((x * e⁻¹ ^ (a - 1) * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) *
        ((e : N.O i) ^ (b - 1) - (e : N.O i) ^ (a - 1)) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1))) * a2 +
      ((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1)) * a1
  rw [key]
  exact (Units.isUnit _).mul hu

end GlobalTheory.CharacterUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpBoundFamilyLarge
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LargeJumps

theorem jump_bound_of_facts_large_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x),
    GlobalTheory.NFacts.Facts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  intro eps Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a hF => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  have hA := (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
  exact GlobalTheory.JumpStatement.holds_all _ _ (hF.admJ _ hA)

end GlobalTheory.LargeJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc

section Gen
variable {l : ℕ} [Fact l.Prime]

def incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion h x, by
    have := x.2
    exact IsIntegral.map ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) this⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def incV {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) : (Fin k → ↥LL.1) →+ (Fin k → ↥LL'.1) :=
  (AddMonoidHom.compLeft (IntermediateField.inclusion h).toRingHom.toAddMonoidHom (Fin k))

def liftQ {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) :
    (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k →+ (Fin k → ↥LL'.1) ⧸ stdG ↥(OL LL') ↥LL'.1 k :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (stdG ↥(OL LL') ↥LL'.1 k).toAddSubgroup).comp (incV h k)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨fun j => incO h (u j), rfl⟩)

theorem liftQ_mk {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) (v : Fin k → ↥LL.1) :
    liftQ h k (Submodule.Quotient.mk v) = Submodule.Quotient.mk (incV h k v) := rfl

end Gen
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

def locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL) :=
  mapM (incO C.le) (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)))

def chiOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  (Units.map ((incO C.le).comp (D.nbr i w hw).eO.toRingHom).toMonoidHom).comp
    ((χ.comp (decS D.nd w)).comp (Br.iota D.nbr i w hw))

abbrev repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Representation ↥C.LL.1 (Br.G D.nbr i w hw) (Fin k → ↥C.LL.1) :=
  matRep (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) N)

def latC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Lattice (O := ↥(OL C.LL)) (repV C N) :=
  stdLatG Subtype.val_injective N

def chiT (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) :
    Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) * θ

def embC (HW : HWOf D.loc) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) :=
  ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hA.2.2).emb

end AtW
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

open Module in

def SetC (HW : HWOf D.loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
    (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
    (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ) : Prop :=
  tableLineDegreeTwo.TopHyp (Br.PD D.loc D.nbr i w hw) (embC HW C hA) D.R.t h w' η typ U
                     (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) ∧
    ∀ x, tableLineDegreeTwo.IsFull (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
      (repV C (twistM (locOC C (rTwO D.nd i r x)) θ))

end AtW
end GlobalTheory.UseLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_character_offset_unramified : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), GlobalTheory.NFacts.Facts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  first | exact @GlobalTheory.UnrNoChi.main | exact GlobalTheory.UnrNoChi.main | (intros; apply GlobalTheory.UnrNoChi.main <;> assumption)
end

