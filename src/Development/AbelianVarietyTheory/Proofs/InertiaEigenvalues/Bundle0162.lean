import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGamGamKTorsion
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.PadicUnitSub

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_max_norm {ι : Type*} [Nonempty ι] (f : ι → ℤ_[l]) :
    ∃ i, ∀ j, ‖f j‖ ≤ ‖f i‖ := by
  classical
  by_cases h0 : ∀ j, f j = 0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, fun j => by rw [h0 j, h0 i]⟩
  · push_neg at h0
    have hex : ∃ n, ∃ j, f j ≠ 0 ∧ (f j).valuation = n := by
      obtain ⟨j, hj⟩ := h0
      exact ⟨_, j, hj, rfl⟩
    obtain ⟨i, hi, hiv⟩ := Nat.find_spec hex
    refine ⟨i, fun j => ?_⟩
    by_cases hj : f j = 0
    · rw [hj, norm_zero]; exact norm_nonneg _
    · have hle : Nat.find hex ≤ (f j).valuation := Nat.find_min' hex ⟨j, hj, rfl⟩
      rw [PadicInt.norm_eq_zpow_neg_valuation hj, PadicInt.norm_eq_zpow_neg_valuation hi, hiv]
      apply zpow_le_zpow_right₀ (by exact_mod_cast hl.out.one_lt.le)
      omega

theorem eq_one_of_pow_eq_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) (k : ℕ) (hk : 0 < k) (h : x ^ k = 1) : x = 1 := by
  have e := GlobalTheory.Cyc.norm_pow_nat_sub_one k hk.ne' x hx h2
  rw [h, sub_self, norm_zero] at e
  have hk' : ‖(k : ℤ_[l])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact_mod_cast hk.ne'
  rcases mul_eq_zero.1 e.symm with h' | h'
  · exact sub_eq_zero.1 (norm_eq_zero.1 h')
  · exact absurd h' hk'

theorem eq_of_torsion (u v : ℤ_[l]ˣ) (hu : IsOfFinOrder u) (hv : IsOfFinOrder v)
    (hx : ‖(u : ℤ_[l]) - v‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖(u : ℤ_[l]) - v‖ < (l : ℝ)⁻¹) : u = v := by
  have hw : IsOfFinOrder (u * v⁻¹) := hu.mul hv.inv
  have hnorm : ‖((u * v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = ‖(u : ℤ_[l]) - v‖ := by
    have e : ((u * v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((u : ℤ_[l]) - v) * ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [sub_mul, Units.mul_inv, Units.val_mul]
    rw [e, norm_mul, PadicInt.norm_units, mul_one]
  have h1 := eq_one_of_pow_eq_one _ (by rw [hnorm]; exact hx) (fun h => by rw [hnorm]; exact h2 h)
    (orderOf (u * v⁻¹)) hw.orderOf_pos
    (by rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one])
  have : u * v⁻¹ = 1 := Units.ext (h1.trans Units.val_one.symm)
  exact mul_inv_eq_one.1 this

theorem norm_le_of_toZModPow_eq (n : ℕ) (a b : ℤ_[l])
    (h : PadicInt.toZModPow n a = PadicInt.toZModPow n b) : ‖a - b‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h,
    sub_self]

theorem finite_torsion : {u : ℤ_[l]ˣ | IsOfFinOrder u}.Finite := by
  have : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  refine Set.Finite.of_finite_image
    (f := fun u : ℤ_[l]ˣ => PadicInt.toZModPow 2 (u : ℤ_[l])) (Set.toFinite _) ?_
  intro u hu v hv huv
  have hle := norm_le_of_toZModPow_eq 2 (u : ℤ_[l]) v huv
  have hlt : (l : ℝ) ^ (-((2 : ℕ) : ℤ)) < (l : ℝ)⁻¹ := by
    have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ h1 (by norm_num)
  exact eq_of_torsion u v hu hv (hle.trans hlt.le) (fun _ => hle.trans_lt hlt)

theorem norm_le_inv_of_lt_one (x : ℤ_[l]) (h : ‖x‖ < 1) : ‖x‖ ≤ (l : ℝ)⁻¹ := by
  have := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one x 0).1 (by simpa using h)
  simpa using this

theorem norm_lt_one_iff_toZMod (x : ℤ_[l]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma norm_natCast_padicInt_eq_one_of_not_dvd (n : ℕ) (h : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (n : ℤ)).1 (by rw [Int.cast_natCast]; exact hlt)
  exact_mod_cast this

theorem exists_teich (g : ℤ_[l]ˣ) :
    ∃ w : ℤ_[l]ˣ, IsOfFinOrder w ∧ ‖(w : ℤ_[l]) - g‖ < 1 := by
  have hl2 := hl.out.two_le
  set F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1 with hF
  have hder : ‖F.derivative.aeval (g : ℤ_[l])‖ = 1 := by
    have hn : ¬ l ∣ (l - 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Algebra.algebraMap_self, RingHom.id_apply, norm_mul, norm_pow, PadicInt.norm_units, one_pow,
      mul_one]
    exact_mod_cast norm_natCast_padicInt_eq_one_of_not_dvd (l - 1) hn
  have hval : ‖F.aeval (g : ℤ_[l])‖ < 1 := by
    have hg0 : PadicInt.toZMod (g : ℤ_[l]) ≠ 0 := (g.isUnit.map PadicInt.toZMod).ne_zero
    rw [norm_lt_one_iff_toZMod]
    simp only [hF, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_one, map_sub, map_pow,
      map_one]
    rw [ZMod.pow_card_sub_one_eq_one hg0, sub_self]
  obtain ⟨z, hz, hzg, -, -⟩ := hensels_lemma (F := F) (a := (g : ℤ_[l]))
    (by rw [hder, one_pow]; exact hval)
  rw [hder] at hzg
  have hz' : z ^ (l - 1) = 1 := by
    simpa [hF, sub_eq_zero] using hz
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz' (by omega)
  refine ⟨hu.unit, isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, by omega, Units.ext ?_⟩, ?_⟩
  · rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz', Units.val_one]
  · rw [IsUnit.unit_spec]; exact hzg

private lemma padicInt_norm_natCast_eq_one_of_not_dvd (n : ℕ) (h : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (n : ℤ)).1 (by rw [Int.cast_natCast]; exact hlt)
  exact_mod_cast this

theorem exists_gam_gamK_torsion :
    ∀ (l : ℕ) [Fact l.Prime] (s : ℕ) (Γ : Subgroup ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → u ∈ Γ) → ∃ (gam gamK : ↥Γ) (D : Finset ↥Γ), ‖((gam : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ (∀ g, g ∈ D ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1) ∧ (∀ g : ↥Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖ ≤ ‖((gamK : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖) ∧ ((∀ g : ↥Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖ ≤ ‖((gam : ℤ_[l]ˣ) : ℤ_[l]) ^ D.card - 1‖) → gamK = gam) ∧ (s = 1 → l ≠ 2 → gamK = gam) := by
  intro l _ s Γ hs hs2 hΓ
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hls : ‖((l : ℤ_[l]) ^ s)‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, inv_pow]
  have hlt1 : ‖((l : ℤ_[l]) ^ s)‖ < 1 := by
    rw [hls]; exact zpow_lt_one_of_neg₀ hl1 (by omega)
  have hunit : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
    rw [PadicInt.isUnit_iff, GlobalTheory.Cyc.padicInt_norm_add_eq_of_lt (by rwa [norm_one]), norm_one]
  have hg0 : (hunit.unit : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s := hunit.unit_spec
  have hg0Γ : hunit.unit ∈ Γ := hΓ _ (by rw [hg0, add_sub_cancel_left])

  have hTfin : ((CommGroup.torsion Γ : Subgroup Γ) : Set Γ).Finite := by
    refine (finite_torsion.preimage Subtype.val_injective.injOn).subset ?_
    intro g hg
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion g).1 hg)
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← Subgroup.coe_pow, hgk, Subgroup.coe_one]⟩
  have hD : ∀ g, g ∈ hTfin.toFinset ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1 := by
    intro g
    rw [Set.Finite.mem_toFinset, SetLike.mem_coe, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hDcard : hTfin.toFinset.card = Nat.card (CommGroup.torsion Γ) := by
    rw [← Nat.card_eq_card_finite_toFinset hTfin]; rfl
  have hDpow : ∀ g ∈ CommGroup.torsion Γ, g ^ hTfin.toFinset.card = 1 := by
    intro g hg
    have h1 := congrArg Subtype.val
      (pow_card_eq_one' (G := CommGroup.torsion Γ) (x := ⟨g, hg⟩))
    rw [hDcard]
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hNpos : 0 < hTfin.toFinset.card :=
    Finset.card_pos.2 ⟨1, (hD 1).2 ⟨1, one_pos, one_pow _⟩⟩
  obtain ⟨gmax, hgmax⟩ :=
    exists_max_norm (l := l) (fun g : Γ => ((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1)
  obtain ⟨gamK, hK1, hK2⟩ : ∃ gamK : Γ,
      (∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖((gamK : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖) ∧
      ((∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖(((⟨hunit.unit, hg0Γ⟩ : Γ) : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖) →
        gamK = ⟨hunit.unit, hg0Γ⟩) := by
    by_cases hc : ∀ g : Γ, ‖((g : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ ≤
        ‖(((⟨hunit.unit, hg0Γ⟩ : Γ) : ℤ_[l]ˣ) : ℤ_[l]) ^ hTfin.toFinset.card - 1‖
    · exact ⟨⟨hunit.unit, hg0Γ⟩, hc, fun _ => rfl⟩
    · exact ⟨gmax, hgmax, fun h => absurd h hc⟩
  refine ⟨⟨hunit.unit, hg0Γ⟩, gamK, hTfin.toFinset, ?_, hD, hK1, hK2, ?_⟩
  · show ‖(hunit.unit : ℤ_[l]) - 1‖ = _
    rw [hg0, add_sub_cancel_left, hls]
  · intro hs1 hl2
    subst hs1
    apply hK2

    have hcard : hTfin.toFinset.card < l := by
      have hle : hTfin.toFinset.card ≤ (Finset.univ.erase (0 : ZMod l)).card := by
        refine Finset.card_le_card_of_injOn (fun g : Γ => PadicInt.toZMod ((g : ℤ_[l]ˣ) : ℤ_[l]))
          ?_ ?_
        · intro g _
          simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
            Set.mem_singleton_iff, true_and, Finset.mem_erase, Finset.mem_univ, and_true]
          exact ((g : ℤ_[l]ˣ).isUnit.map PadicInt.toZMod).ne_zero
        · intro g hg h hh hgh
          have hgD := (hD g).1 hg
          have hhD := (hD h).1 hh
          obtain ⟨a, ha, hga⟩ := hgD
          obtain ⟨b, hb, hhb⟩ := hhD
          have hlt : ‖((g : ℤ_[l]ˣ) : ℤ_[l]) - ((h : ℤ_[l]ˣ) : ℤ_[l])‖ < 1 := by
            rw [norm_lt_one_iff_toZMod, map_sub, sub_eq_zero]; exact hgh
          apply Subtype.ext
          refine eq_of_torsion _ _ (isOfFinOrder_iff_pow_eq_one.2 ⟨a, ha, ?_⟩)
            (isOfFinOrder_iff_pow_eq_one.2 ⟨b, hb, ?_⟩) (norm_le_inv_of_lt_one _ hlt)
            (fun h2 => absurd h2 hl2)
          · rw [← Subgroup.coe_pow, hga, Subgroup.coe_one]
          · rw [← Subgroup.coe_pow, hhb, Subgroup.coe_one]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at hle
      have := hlp.two_le
      omega
    have hN : ‖((hTfin.toFinset.card : ℕ) : ℤ_[l])‖ = 1 :=
      padicInt_norm_natCast_eq_one_of_not_dvd _ (Nat.not_dvd_of_pos_of_lt hNpos hcard)
    have hgam1 : ‖(hunit.unit : ℤ_[l]) - 1‖ = (l : ℝ)⁻¹ := by
      rw [hg0, add_sub_cancel_left, pow_one, PadicInt.norm_p]
    have hgam : ‖(hunit.unit : ℤ_[l]) ^ hTfin.toFinset.card - 1‖ = (l : ℝ)⁻¹ := by
      rw [GlobalTheory.Cyc.norm_pow_nat_sub_one _ hNpos.ne' _ hgam1.le (fun h2 => absurd h2 hl2), hgam1, hN,
        mul_one]
    intro g
    show _ ≤ ‖(hunit.unit : ℤ_[l]) ^ hTfin.toFinset.card - 1‖
    rw [hgam]
    obtain ⟨w, hw, hwg⟩ := exists_teich (g : ℤ_[l]ˣ)

    have hwΓ : w ∈ Γ := by
      have hmul : w * (g : ℤ_[l]ˣ)⁻¹ ∈ Γ := by
        apply hΓ
        rw [pow_one, ← PadicInt.norm_lt_one_iff_dvd]
        have e : ((w * (g : ℤ_[l]ˣ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
            ((w : ℤ_[l]) - ((g : ℤ_[l]ˣ) : ℤ_[l])) * (((g : ℤ_[l]ˣ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
          rw [sub_mul, Units.mul_inv, Units.val_mul]
        rw [e, norm_mul, PadicInt.norm_units, mul_one]
        exact hwg
      have := Γ.mul_mem hmul g.2
      rwa [inv_mul_cancel_right] at this
    have hwT : (⟨w, hwΓ⟩ : Γ) ∈ CommGroup.torsion Γ := by
      obtain ⟨k, hk, hwk⟩ := isOfFinOrder_iff_pow_eq_one.1 hw
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hwk)⟩
    have hwN : (w : ℤ_[l]) ^ hTfin.toFinset.card = 1 := by
      have h1 := congrArg (fun x : Γ => ((x : ℤ_[l]ˣ) : ℤ_[l])) (hDpow _ hwT)
      simpa using h1
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ((g : ℤ_[l]ˣ) : ℤ_[l]) (w : ℤ_[l]) hTfin.toFinset.card
    apply norm_le_inv_of_lt_one
    rw [← hwN, hc, norm_mul, norm_sub_rev]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one c)) hwg

end GlobalTheory.PadicUnitSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDual
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.LargeLattice

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L,
      IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ x μ ω h C hC V hV
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  haveI := FourierTest.finite_F_L A
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  let β := FourierTest.beta A (x : A.K)
  have hker : ∀ w y, A.kerL ψ x w y = ψ (β w y) := fun _ _ => rfl
  let e := Module.finBasis F A.L
  let Φ : A.L →ₗ[F] (Fin (Module.finrank F A.L) → F) := LinearMap.pi (fun i => β (e i))
  have hΦ : ∀ y i, Φ y i = β (e i) y := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply FourierTest.beta_sepLeft A hK hL x y
    intro w
    have h0 : β.flip y = 0 := e.ext (fun i => by
      simpa [hΦ] using congrFun hy i)
    rw [FourierTest.beta_symm A hK hL]
    simpa using LinearMap.congr_fun h0 w
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let Φe := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦe : ∀ y, Φe y = Φ y := fun _ => rfl
  have hΦc : Continuous Φ := IsModuleTopology.continuous_of_linearMap Φ
  have hΨc : Continuous Φe.symm :=
    IsModuleTopology.continuous_of_linearMap (Φe.symm : (Fin (Module.finrank F A.L) → F) →ₗ[F] A.L)

  have hV' : Φe.symm ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.L) → F) :=
    hΨc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨ε, hε0, hεV⟩ := Metric.mem_nhds_iff.1 hV'
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm F (1 / ε)
  have ht0 : 0 < ‖t‖ := lt_trans (by positivity) ht
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hΦc.continuousOn
  let Km : ℝ := ∑ i, ‖Φ (e i)‖
  have hKm : ∀ i j, ‖Φ (e i) j‖ ≤ Km := fun i j =>
    (norm_le_pi_norm (Φ (e i)) j).trans
      (Finset.single_le_sum (f := fun i => ‖Φ (e i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  let R : ℝ := max (max b (‖t‖ * Km)) (max ε 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRε : ε ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRb : b ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRt : ‖t‖ * Km ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  let Λ : AddSubgroup A.L :=
    { carrier := {y | ∀ i, ‖Φ y i‖ ≤ R}
      add_mem' := by
        intro a c ha hc i
        simp only [Set.mem_setOf_eq, map_add, Pi.add_apply] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hc i))
      zero_mem' := by intro i; simp [hR0.le]
      neg_mem' := by
        intro a ha i
        simp only [Set.mem_setOf_eq, map_neg, Pi.neg_apply, norm_neg] at *
        exact ha i }
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, ‖Φ y i‖ ≤ R := fun _ => Iff.rfl

  have hperp : ∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, ∀ i, ‖Φ y i‖ < ε := by
    intro y hy i
    have h1 : ‖t * Φ y i‖ ≤ 1 := by
      refine (hcond (t * Φ y i)).1 fun e' he' => ?_
      have hw : (e' * t) • e i ∈ Λ := by
        rw [hmem]; intro j
        rw [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul]
        calc ‖e'‖ * ‖t‖ * ‖Φ (e i) j‖ ≤ 1 * ‖t‖ * Km := by gcongr; exact hKm i j
          _ ≤ R := by rw [one_mul]; exact hRt
      have := hy _ hw
      rw [hker, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      rw [← hΦ] at this
      rwa [← mul_assoc]
    rw [norm_mul] at h1
    have h2 : ‖Φ y i‖ ≤ 1 / ‖t‖ := by rw [le_div_iff₀ ht0]; linarith
    have h3 : 1 / ‖t‖ < ε := by
      rw [div_lt_iff₀ ht0]
      rw [div_lt_iff₀ hε0] at ht
      linarith
    exact lt_of_le_of_lt h2 h3
  refine ⟨Λ, ?_, ?_, ?_, ?_, ?_⟩
  · have : (Λ : Set A.L) = ⋂ i, (fun y => Φ y i) ⁻¹' Metric.closedBall 0 R := by
      ext y; simp [hmem, mem_closedBall_zero_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (IsUltrametricDist.isOpen_closedBall 0 hR0.ne').preimage ((continuous_apply i).comp hΦc)
  · have : (Λ : Set A.L) = Φe.symm '' Metric.closedBall 0 R := by
      ext y
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · intro hy
        refine ⟨Φe y, ?_, by simp⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le, hΦe]; exact hy
      · rintro ⟨z, hz, rfl⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le] at hz
        intro i
        have : Φ (Φe.symm z) = z := by rw [← hΦe]; simp
        rw [this]; exact hz i
    rw [this]
    exact (isCompact_closedBall 0 R).image hΨc
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact ((norm_le_pi_norm (Φ y) i).trans (hb y hy)).trans hRb
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact (hperp y hy i).le.trans hRε
  · intro y hy
    have hb' : Φe y ∈ Metric.ball (0 : Fin (Module.finrank F A.L) → F) ε := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε0, hΦe]; exact hperp y hy
    have := hεV hb'
    simpa using this

end GlobalTheory.JR.WeilQuad.LargeLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInvariantsOfScalarNeOneTwist
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_invariants_of_smul_ne_one : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  intro O _ _ _ _ M _ _ e G _ ρ g a ha hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hb : a - 1 ≠ 0 := sub_ne_zero.2 ha
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hkill : ∀ m : ρ.invariants, ϖ ^ c • (m : M) = 0 := by
    intro m
    have hm : ρ g (m : M) = m := (Representation.mem_invariants ρ (m : M)).1 m.2 g
    have h1 : (a - 1) • (m : M) = 0 := by
      rw [sub_smul, one_smul, ← hg, hm, sub_self]
    rw [hu, mul_smul] at h1
    have h2 := congrArg (fun x : M => ((u⁻¹ : Oˣ) : O) • x) h1
    simp only [smul_zero, smul_smul] at h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  haveI := (lev_pow_card hϖ e c).1
  refine Finite.of_injective (fun m : ρ.invariants => (Lev.mk (m : M) (hkill m) : Lev M (ϖ ^ c))) ?_
  intro x y hxy
  have := congrArg Lev.val hxy
  simp only [Lev.val_mk] at this
  exact Subtype.ext this

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvrStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | exact GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | (intros; apply GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧ ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) → (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) → ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  first | exact @GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | exact GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | (intros; apply GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) = Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧ ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 → ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  first | exact @GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | exact GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | (intros; apply GlobalTheory.Cyc.finrank_Ks_and_chi_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppoStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  first | exact @GlobalTheory.FourKTest.fourK_isTest | exact GlobalTheory.FourKTest.fourK_isTest | (intros; apply GlobalTheory.FourKTest.fourK_isTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizerStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  first | exact @GlobalTheory.KO_divisible_by_uniformiser | exact GlobalTheory.KO_divisible_by_uniformiser | (intros; apply GlobalTheory.KO_divisible_by_uniformiser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizerStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | exact GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | (intros; apply GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZeroStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwistStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h2_bounded_twist : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  first | exact @GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | exact GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | (intros; apply GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic <;> assumption)
end

