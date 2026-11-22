import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0126
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0149
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLaws
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem gam_norm_natCast_eq (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem gam_exists_max_of_tendsto (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) : ∃ n₀, ∀ n, f n ≤ f n₀ := by
  by_cases hall : ∀ n, f n = 0
  · exact ⟨0, fun n => by rw [hall n, hall 0]⟩
  push_neg at hall
  obtain ⟨m, hm⟩ := hall
  have hmpos : 0 < f m := lt_of_le_of_ne (hf0 m) (Ne.symm hm)
  have hev : ∀ᶠ n in Filter.cofinite, f n < f m := hf (Iio_mem_nhds hmpos)
  have hfin : {n | ¬ f n < f m}.Finite := Filter.eventually_cofinite.mp hev
  have hmem : m ∈ hfin.toFinset := by simp
  obtain ⟨n₀, hn₀, hmax⟩ := hfin.toFinset.exists_max_image f ⟨m, hmem⟩
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : f n < f m
  · exact hn.le.trans (hmax m hmem)
  · exact hmax n (by simpa using hn)

theorem gam_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := gam_norm_natCast_eq l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 < a := by rw [ha]; positivity

  have key : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ n : ℤ, a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j t) ∧
      (∃ n : ℤ, gam l h j t = a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ))) := by
    intro t ht0 ht1
    set f : ℤ → ℝ := fun n => a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) with hf_def
    have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg ht0 _)
    obtain ⟨n₀, hn₀⟩ := gam_exists_max_of_tendsto f hf0 (GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero l h j t h1 ht0 ht1)
    have hbdd : BddAbove (Set.range f) := ⟨f n₀, by rintro _ ⟨n, rfl⟩; exact hn₀ n⟩
    have hg : gam l h j t = ⨆ n, f n := rfl
    refine ⟨fun n => ?_, n₀, ?_⟩
    · rw [hg]; exact le_ciSup hbdd n
    · rw [hg]; exact le_antisymm (ciSup_le hn₀) (le_ciSup hbdd n₀)
  obtain ⟨hle, n₀, hn₀⟩ := key r hr0 hr1
  refine ⟨hle, ⟨n₀, hn₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [hn₀]; exact mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg hr0 _)
  · intro hr
    exact lt_of_lt_of_le (mul_pos (zpow_pos ha0 _) (Real.rpow_pos_of_pos hr _)) (hle 0)
  ·
    have hq0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hq1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
    obtain ⟨hle', m₀, hm₀⟩ := key (r ^ l ^ h) hq0 hq1
    have shift : ∀ n : ℤ, a ^ (-n) * (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) =
        a * (a ^ (-(n + 1)) * r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ))) := by
      intro n
      have e1 : (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) = r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ)) := by
        rw [← Real.rpow_natCast r (l ^ h), ← Real.rpow_mul hr0]
        congr 1
        have hl0 : (l : ℝ) ≠ 0 := by positivity
        rw [show ((n + 1) * h + j : ℤ) = (h : ℤ) + (n * h + j) by ring, zpow_add₀ hl0 (h : ℤ) (n * h + j), zpow_natCast, Nat.cast_pow]
      have e2 : a ^ (-n) = a * a ^ (-(n + 1)) := by
        rw [show -n = 1 + (-(n + 1)) by ring, zpow_add₀ ha0.ne', zpow_one]
      rw [e1, e2]; ring
    apply le_antisymm
    · rw [hm₀, shift]
      exact mul_le_mul_of_nonneg_left (hle (m₀ + 1)) ha0.le
    · rw [hn₀]
      have := hle' (n₀ - 1)
      rw [shift, show n₀ - 1 + 1 = n₀ by ring] at this
      exact this
  · intro s hrs hs1
    have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
    obtain ⟨hles, -⟩ := key s hs0.le hs1
    rw [hn₀]
    refine lt_of_lt_of_le ?_ (hles n₀)
    apply mul_lt_mul_of_pos_left _ (zpow_pos ha0 _)
    exact Real.rpow_lt_rpow hr0 hrs (zpow_pos (by positivity) _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TiltAbs

variable {l : ℕ} [Fact l.Prime]

lemma rootT_pow (x : Per.Fl l) (n : ℕ) : rootT x n ^ l ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

lemma untilt_add (x y : Per.Fl l) :
    ∃ t : Per.OC l, (x + y).untilt = x.untilt + y.untilt + (l : Per.OC l) * t := by
  have h : Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x + y).untilt =
      Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x.untilt + y.untilt) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_add, map_add, PreTilt.mk_untilt_eq_coeff_zero,
      PreTilt.mk_untilt_eq_coeff_zero]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [← ht]; ring⟩

lemma rootT_add (x y : Per.Fl l) (n : ℕ) :
    ∃ t : Per.OC l, rootT (x + y) n = rootT x n + rootT y n + (l : Per.OC l) * t := by
  unfold rootT
  rw [iterate_map_add]
  exact untilt_add _ _

lemma norm_le_one (t : Per.OC l) : ‖(t : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 t.2

lemma norm_l_lt : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt

lemma bound (x y : Per.Fl l) (n : ℕ) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖)
        (‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) := by
  obtain ⟨t, ht⟩ := rootT_add x y n
  rw [← rootT_pow (x + y) n, ← rootT_pow x n, ← rootT_pow y n]
  have h1 : ‖((rootT (x + y) n : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
        ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [ht]
    push_cast
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      (IsUltrametricDist.norm_add_le_max _ _) ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one t)
  push_cast
  simp only [norm_pow]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 (l ^ n)
  refine h2.trans ?_
  rcases max_choice (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
    ‖((l : ℕ) : ℂ_[l])‖ with h | h <;> rw [h]
  · refine le_trans ?_ (le_max_left _ _)
    rcases max_choice ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖
      with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact le_max_right _ _

lemma eq_zero_of_untilt (x : Per.Fl l) (hx : x.untilt = 0) : x = 0 := by
  apply Perfection.ext
  intro n
  have h1 : (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x).untilt = 0 := by
    have h := rootT_pow x n
    rw [hx] at h
    exact pow_eq_zero_iff (pow_ne_zero n (Fact.out : l.Prime).ne_zero) |>.1 h
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x)
  rw [h1, map_zero] at h2
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at h3
  have hc : PreTilt.coeff n x = PreTilt.coeff n 0 := by rw [map_zero, ← h3, ← h2]
  simpa only [PreTilt.coeff_def] using hc

theorem untilt_ultrametric_definite (l : ℕ) [Fact l.Prime] (x y : Per.Fl l) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧
    (x.untilt = 0 → x = 0) := by
  refine ⟨?_, eq_zero_of_untilt x⟩
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt).comp
      (tendsto_pow_atTop_atTop_of_one_lt hl)
  have h2 := (tendsto_const_nhds (x := max ‖((x.untilt : Per.OC l) : ℂ_[l])‖
    ‖((y.untilt : Per.OC l) : ℂ_[l])‖)).max ht
  have h3 := ge_of_tendsto' h2 (bound x y)
  rwa [max_eq_left (le_max_of_le_left (norm_nonneg _))] at h3

end GlobalTheory.TiltAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedCountStableLatticesProductDescentGL
section
open Polynomial

namespace GlobalTheory.UnitLemma.DescentGL

open GlobalTheory.UnitLemma

theorem stab_smul_comm {G X : Type} [CommGroup G] [MulAction G X] (t : G) (x : X) :
    MulAction.stabilizer G (t • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]

theorem countGL_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  intro O _ _ _ _ E _ _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hsep
  have hs₁ := hsep.of_mul_left
  have hs₂ := hsep.of_mul_right
  have hres : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 :=
    resultant_ne_zero _ _ hsep.isCoprime
  rw [GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E (A₁ × A₂) (g₁, g₂), GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₁ g₁, GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₂ g₂]
  haveI hf₁ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₁ g₁ hs₁
  haveI hf₂ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₂ g₂ hs₂
  obtain ⟨hfinY, hsum⟩ := GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod O E A₁ A₂ g₁ g₂ hf₁ hf₂
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hfib := GlobalTheory.T.ncard_fibre_stableLatticePairProjection O E A₁ A₂ g₁ g₂ hres
  have hstab : ∀ y : LatPair O E g₁ g₂, MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧
      (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) ≠ 0 := by
    intro y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ y (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ y.1) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ y.2)
    exact ⟨h1, by rw [h2]; exact mul_ne_zero (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₁ g₁ hs₁ y.1) (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₂ g₂ hs₂ y.2)⟩
  have hfin : ∀ y, (latProj O E g₁ g₂ ⁻¹' {y}).Finite := by
    intro y
    apply Set.finite_of_ncard_ne_zero
    have h := hfib y
    intro h0
    rw [h0, Nat.cast_zero] at h
    exact zpow_ne_zero _ hq h.symm
  have hCP := GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres (A₁ × A₂)ˣ (stLat O E ((g₁, g₂) : A₁ × A₂)) (LatPair O E g₁ g₂) (intUnits O (A₁ × A₂))
    (latProj O E g₁ g₂) (GlobalTheory.T.stableLatticePair_projection_smul_units O E A₁ A₂ g₁ g₂) hfin hstab hfinY (fun _ => 1) (fun _ _ => rfl)
  simp only [one_mul] at hCP
  rw [hCP]
  have hterm : ∀ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂),
      ((latProj O E g₁ g₂ ⁻¹' {Quotient.out o}).ncard : ℚ) *
        ((MulAction.stabilizer (A₁ × A₂)ˣ (Quotient.out o)).relIndex (intUnits O (A₁ × A₂)) : ℚ) =
      (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) *
        (((MulAction.stabilizer A₁ˣ (Quotient.out o).1).relIndex (intUnits O A₁) : ℚ) *
          ((MulAction.stabilizer A₂ˣ (Quotient.out o).2).relIndex (intUnits O A₂) : ℚ)) := by
    intro o
    rw [hfib, (GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ _ (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ _) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ _)).2, Nat.cast_mul]
  have hs := hsum (fun y => ((MulAction.stabilizer A₁ˣ y).relIndex (intUnits O A₁) : ℚ))
    (fun y => ((MulAction.stabilizer A₂ˣ y).relIndex (intUnits O A₂) : ℚ))
    (fun t y => by simp only [stab_smul_comm]) (fun t y => by simp only [stab_smul_comm])
  rw [finsum_congr hterm, ← mul_finsum, hs]

end GlobalTheory.UnitLemma.DescentGL
end

