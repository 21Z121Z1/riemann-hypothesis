import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockUnitIndicator
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.FourUnit

theorem integral_indicator_char_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (S : Set G) (φ : G → ℂ)
    (hφ : ∀ a b, φ (a + b) = φ a * φ b) (t : G) (hS : ∀ z, t + z ∈ S ↔ z ∈ S) (ht : φ t ≠ 1) :
    ∫ z, S.indicator φ z ∂μ = 0 := by
  have key : ∀ z, S.indicator φ (t + z) = φ t * S.indicator φ z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem ((hS z).2 hz), Set.indicator_of_mem hz, hφ]
    · rw [Set.indicator_of_notMem (fun h => hz ((hS z).1 h)), Set.indicator_of_notMem hz, mul_zero]
  have h := integral_add_left_eq_self (μ := μ) (S.indicator φ) t
  simp_rw [key, integral_const_mul] at h
  have h2 : (φ t - 1) * ∫ z, S.indicator φ z ∂μ = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) ht
  · exact h3

theorem addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem norm_trace_le (hU : Unram F E) (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) (w : E) :
    ‖Algebra.trace F E w‖ ≤ ‖w‖ := by
  haveI := hU.ultraE
  rw [← norm_algebraMap' E, htr]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hU.norm_star]; simp)

theorem integral_ball_char (hU : Unram F E) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (hu : ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) (y : E) :
    ∫ z, (Metric.closedBall (0 : E) 1).indicator (fun z => ψ (Algebra.trace F E (star z * y))) z ∂μ =
      if ‖y‖ ≤ 1 then 1 else 0 := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  split_ifs with hy
  · rw [Set.indicator_congr (g := fun _ => (1 : ℂ)) (fun z hz => ?_)]
    · rw [integral_indicator measurableSet_closedBall, setIntegral_const]
      simp [Measure.real, hvol]
    · apply hψ.1
      refine (norm_trace_le hU htr _).trans ?_
      rw [norm_mul, hU.norm_star]
      exact mul_le_one₀ (mem_closedBall_zero_iff.1 hz) (norm_nonneg _) hy
  · push_neg at hy
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    obtain ⟨yF, hyF⟩ := hU.unram y
    obtain ⟨u, hu1, hu2⟩ := hu
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hyF0 : yF ≠ 0 := by rintro rfl; rw [hyF] at hy; simp at hy; linarith
    have hx₀y : ‖x₀‖ ≤ ‖y‖ := by
      have h1 : ‖yF⁻¹‖ < 1 := by rw [norm_inv, ← hyF]; exact inv_lt_one_of_one_lt₀ hy
      have h2 := hx₀' _ h1
      rw [norm_mul, norm_inv, ← hyF] at h2
      have hpos : 0 < ‖y‖ := by linarith
      rwa [mul_inv_le_iff₀ hpos, one_mul] at h2
    have htu : Algebra.trace F E u ≠ 0 := by intro h; rw [h, norm_zero] at hu2; exact zero_ne_one hu2
    set w : E := (x₀ / Algebra.trace F E u) • u with hw
    have hTw : Algebra.trace F E w = x₀ := by
      rw [hw, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ htu]
    have hnw : ‖w‖ ≤ ‖y‖ := by
      rw [hw, norm_smul, norm_div, hu2, div_one]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans hx₀y
    have hpos : 0 < ‖y‖ := by linarith
    refine integral_indicator_char_eq_zero μ _ _ (fun a b => ?_) (star (w * y⁻¹)) (fun z => ?_) ?_
    · rw [star_add, add_mul, map_add, AddChar.map_add_eq_mul]
    · have ht : ‖star (w * y⁻¹)‖ ≤ 1 := by
        rw [hU.norm_star, norm_mul, norm_inv, mul_inv_le_iff₀ hpos, one_mul]; exact hnw
      simp only [mem_closedBall_zero_iff]
      constructor
      · intro h
        have := IsUltrametricDist.norm_add_le_max (star (w * y⁻¹) + z) (-(star (w * y⁻¹)))
        rw [norm_neg, show star (w * y⁻¹) + z + -star (w * y⁻¹) = z by abel] at this
        exact this.trans (max_le h ht)
      · intro h
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht h)
    · simp only [star_star]
      rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one, hTw]
      exact hx₀

theorem fourU_unitU : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
    (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ htr hu
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  funext X
  simp only [fourU]
  by_cases h0 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1
  · have hint : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) =
        ∏ i, (Metric.closedBall (0 : E) 1).indicator
          (fun z => ψ (Algebra.trace F E (star z * X.2.1 i))) (c i) := by
      intro c
      by_cases hc : ∀ i, ‖c i‖ ≤ 1
      · have e1 : unitU r F E (X.1, c, X.2.2) = 1 := by
          simp only [unitU]; rw [Set.indicator_of_mem (by exact ⟨h0.1, hc, h0.2⟩)]; rfl
        rw [e1, one_mul]
        simp only [dotProduct, Pi.star_apply, map_sum, addChar_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hc i))]
      · push_neg at hc
        obtain ⟨i, hi⟩ := hc
        have e1 : unitU r F E (X.1, c, X.2.2) = 0 := by
          simp only [unitU]
          exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (h.2.1 i)) _
        rw [e1, zero_mul]
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (mem_closedBall_zero_iff.1 h)) _
    simp_rw [hint]
    rw [integral_fintype_prod_eq_prod]
    simp_rw [integral_ball_char hU M.μE M.volE ψ hψ htr hu]
    rw [Finset.prod_boole]
    simp only [unitU, Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_univ, true_implies, Pi.one_apply]
    simp [h0.1, h0.2]
  · have e : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) = 0 := fun c => by
      simp only [unitU]
      exact Set.indicator_of_notMem (fun h => h0 ⟨h.1, h.2.2⟩) _
    simp_rw [e, zero_mul, integral_zero]

end GlobalTheory.JR.FourUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerpEqPerpNb
section
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_nb {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ nb cK J L v ↔ ∃ m ∈ perp cK J L v, ∃ a : O, x = m + a • v := by
  unfold nb
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨m, hm, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨m, hm, a, rfl⟩
  · rintro ⟨m, hm, a, rfl⟩
    exact ⟨m, hm, a • v, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, rfl⟩

theorem conj_mem_range (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {y : K}
    (hy : y ∈ (algebraMap O K).range) : cK y ∈ (algebraMap O K).range := by
  obtain ⟨a, rfl⟩ := hy
  exact ⟨c a, (hcK a).symm⟩

theorem nb_int (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hvv : hf cK J v v ∈ (algebraMap O K).range) {x y : Fin r → K}
    (hx : x ∈ nb cK J L v) (hy : y ∈ nb cK J L v) :
    hf cK J x y ∈ (algebraMap O K).range := by
  obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hx
  obtain ⟨m', hm', a', rfl⟩ := mem_nb.1 hy
  rw [mem_perp] at hm hm'
  have h1 : hf cK J m m' ∈ (algebraMap O K).range := (hSD m).1 hm.1 m' hm'.1
  have h2 : hf cK J m v ∈ (algebraMap O K).range := by
    rw [hf_conj cK hc2 J hJ]; exact conj_mem_range c cK hcK hm.2
  rw [hf_add_left, hf_add_right, hf_add_right, hf_algSmul_right, hf_algSmul_left,
    hf_algSmul_left, hf_algSmul_right, hcK]
  refine add_mem (add_mem h1 (mul_mem ⟨_, rfl⟩ h2)) (add_mem (mul_mem ⟨_, rfl⟩ hm'.2) ?_)
  exact mul_mem ⟨_, rfl⟩ (mul_mem ⟨_, rfl⟩ hvv)

theorem nb_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : IsSD cK J (nb cK J L v) := by
  obtain ⟨hv, hw, hvv⟩ := hstep
  intro x
  refine ⟨fun hx y hy => nb_int c cK hcK hc2 hJ hϖ hSD hvv hx hy, fun hx => ?_⟩
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  have hperp_nb : ∀ m ∈ perp cK J L v, m ∈ nb cK J L v := fun m hm =>
    mem_nb.2 ⟨m, hm, 0, by simp⟩
  have hl0p : ϖ • l0 ∈ perp cK J L v := by
    refine mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩
    rw [hf_algSmul_right]; exact hβ'
  have hxl0 : algebraMap O K ϖ * hf cK J x l0 ∈ (algebraMap O K).range := by
    have := hx _ (hperp_nb _ hl0p)
    rwa [hf_algSmul_right] at this
  obtain ⟨e, he⟩ := exists_ratio hϖ hβ hβ' hxl0
  set b := c.symm e with hb
  have hcb : cK (algebraMap O K b) = algebraMap O K e := by rw [hcK, hb, RingEquiv.apply_symm_apply]
  set x' := x - b • v with hx'
  have hx'l0 : hf cK J x' l0 = 0 := by
    rw [hx', hf_sub_left, hf_algSmul_left, hcb, he, sub_self]
  have hx'm : ∀ m ∈ perp cK J L v, hf cK J x' m ∈ (algebraMap O K).range := by
    intro m hm
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx m (hperp_nb m hm)) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) (mem_perp.1 hm).2)
  have hx'L : x' ∈ L := by
    refine (hSD x').2 fun l hl => ?_
    obtain ⟨a, ha⟩ := exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw hl)
    have hm : l - a • l0 ∈ perp cK J L v := by
      refine mem_perp.2 ⟨L.sub_mem hl (L.smul_mem a hl0), ?_⟩
      rw [hf_sub_right, hf_algSmul_right, ha, sub_self]
      exact zero_mem _
    have : l = (l - a • l0) + a • l0 := by abel
    rw [this, hf_add_right, hf_algSmul_right, hx'l0, mul_zero, add_zero]
    exact hx'm _ hm
  have hx'p : x' ∈ perp cK J L v := by
    refine mem_perp.2 ⟨hx'L, ?_⟩
    rw [hf_conj cK hc2 J hJ]
    apply conj_mem_range c cK hcK
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx v hvnb) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) hvv)
  exact mem_nb.2 ⟨x', hx'p, b, by rw [hx']; abel⟩

theorem perp_eq_perp_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) {l0 : Fin r → K} (hl0 : l0 ∈ L)
    (hβ : hf cK J v l0 ∉ (algebraMap O K).range) :
    perp cK J L v = perp cK J (nb cK J L v) l0 := by
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  ext x
  constructor
  · intro hx
    refine mem_perp.2 ⟨mem_nb.2 ⟨x, hx, 0, by simp⟩, (hSD l0).1 hl0 x (mem_perp.1 hx).1⟩
  · intro hx
    obtain ⟨hxn, hxl⟩ := mem_perp.1 hx
    obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hxn
    have hm' := mem_perp.1 hm
    have h1 : algebraMap O K a * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [hf_add_right, hf_algSmul_right] at hxl
      have := sub_mem hxl ((hSD l0).1 hl0 m hm'.1)
      simpa using this
    have hγ : hf cK J l0 v ∉ (algebraMap O K).range := by
      intro h
      apply hβ
      rw [hf_conj cK hc2 J hJ l0 v]
      exact conj_mem_range c cK hcK h
    have hγ' : algebraMap O K ϖ * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [← hf_algSmul_right]; exact (hSD l0).1 hl0 _ hw
    obtain ⟨e, rfl⟩ := (ratio_mem_iff hϖ hγ hγ' a).1 h1
    refine mem_perp.2 ⟨?_, (hSDn v).1 hvnb _ hxn⟩
    rw [mul_comm ϖ e, mul_smul]
    exact L.add_mem hm'.1 (L.smul_mem e hw)

theorem good_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : Good cK J ϖ N (nb cK J L v) := by
  obtain ⟨hSD, habs, hidx⟩ := hL
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hQ : Nat.card (IsLocalRing.ResidueField O) ≠ 0 := Nat.card_pos.ne'
  have hpL : perp cK J L v ≤ L := fun x hx => (mem_perp.1 hx).1
  have hpn : perp cK J L v ≤ nb cK J L v := fun x hx => mem_nb.2 ⟨x, hx, 0, by simp⟩
  have i1 := perp_relIndex c cK hcK hϖ hSD hv hw
  have hl0n : l0 ∉ nb cK J L v := by
    intro h
    have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
    exact hβ ((hSDn v).1 hvnb l0 h)
  have hwl0 : ϖ • l0 ∈ nb cK J L v := by
    refine hpn (mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩)
    rw [hf_algSmul_right]; exact hβ'
  have i2 := perp_relIndex c cK hcK hϖ hSDn hl0n hwl0
  rw [← perp_eq_perp_nb c cK hcK hc2 hJ hϖ hSD ⟨hv, hw, hvv⟩ hl0 hβ] at i2
  refine ⟨hSDn, ?_, ?_⟩
  · intro x
    obtain ⟨k, hk⟩ := habs x
    refine ⟨k + 1, hpn (mem_perp.2 ⟨?_, ?_⟩)⟩
    · rw [pow_succ', mul_smul]; exact L.smul_mem ϖ hk
    · rw [pow_succ', mul_smul, hf_algSmul_right]
      exact mul_pair_mem c cK hcK hϖ hSD hw hk
  · rw [← idx_eq_of_le hϖ hpn (by rw [i2]; exact hQ), idx_eq_of_le hϖ hpL (by rw [i1]; exact hQ),
      hidx]

end GlobalTheory.HermNbr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheorem
section
noncomputable section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Sat
variable {k : Type} [Field k]

section
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] {l n : ℕ} {R : RingPG k l}

theorem linearIndependent_phi (D : ModPG R n V) (i : ZMod n) {ι : Type} {v : ι → V}
    (hv : LinearIndependent k⸨X⸩ v) : LinearIndependent k⸨X⸩ fun j => D.φ i (v j) := by
  have h1 := hv.linearIndepOn_id
  have h2 := D.linearIndependent_φ i (Module.Basis.extend h1)
  have h3 := h2.comp (fun j : ι => ⟨v j, h1.subset_extend _ ⟨j, rfl⟩⟩)
    (fun a b h => hv.injective (congrArg Subtype.val h))
  convert h3 using 2 with j
  simp [Module.Basis.extend_apply_self]

end

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
  {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem comap_sh (f : W →ₗ[k⸨X⸩] V) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).comap (f.restrictScalars k⟦X⟧) = sh a (N.comap (f.restrictScalars k⟦X⟧)) := by
  ext x
  simp [mem_sh_iff_smul_mem]

theorem isLat_comap (f : W →ₗ[k⸨X⸩] V) (hf : Function.Injective f) {N : Submodule k⟦X⟧ V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.LatticeComap.main f hf hN

theorem exists_lifts (f : W →ₗ[k⸨X⸩] V) {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    ∃ (m : ℕ) (b : Fin m → V), LinearIndependent k⸨X⸩ ((LinearMap.range f).mkQ ∘ b) ∧
      ∀ y ∈ N, ∃ (a : Fin m → k⟦X⟧) (x : W), f x ∈ N ∧ y = ∑ j, a j • b j + f x :=
  _root_.GlobalTheory.AbelianStatement.main f hN

variable [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}

theorem comap_pull (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (hf : Function.Injective f) (hg : Function.Injective g) (hφ : ∀ x, g (D'.φ i x) = D.φ i (f x))
    {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.IndependentSpanDual.comap_pull D D' i f g hf hg hφ hN

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V), (∀ i, Function.Injective (f i)) → (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) → (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) → ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) → let N' := fun i => (N i).comap ((f i).restrictScalars k⟦X⟧); (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    simp only [N']
    rw [← h, ← comap_sh, ← comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · simp only [N']
    rw [← comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx

end GlobalTheory.PhiGam.Sat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeSubOneNormLe
section
namespace GlobalTheory

theorem pow_prime_sub_one_norm_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  intro l _ n _ _ X k hX i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with ht
  have t0 : 0 ≤ t := by positivity
  have tl : t ≤ (l : ℝ)⁻¹ := by
    rw [ht, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have t1 : t ≤ 1 := tl.trans (inv_le_one_of_one_le₀ hl1.le)
  have hrhs : (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = t * (l : ℝ)⁻¹ := by
    rw [ht, show -(((k + 1 : ℕ) : ℤ) + 2) = -((k : ℤ) + 2) + (-1) by push_cast; ring,
      zpow_add₀ hl0, zpow_neg_one]
  rw [hrhs]
  set Y := X - 1 with hY
  have hXY : X = 1 + Y := by rw [hY]; abel
  have hR := GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hX l i j
  have hsplit : (X ^ l - 1) i j = ((1 + Y) ^ l - 1 - ((l : ℕ) : ℚ_[l]) • Y) i j + (((l : ℕ) : ℚ_[l]) • Y) i j := by
    rw [hXY]; simp
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · calc _ ≤ t ^ 2 := hR
      _ = t * t := sq t
      _ ≤ t * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_left tl t0
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p, mul_comm]
    exact mul_le_mul_of_nonneg_right (hX i j) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpaceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  first | exact @GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | exact GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | (intros; apply GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
section
open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]

def ptrB (M : Meas r F E) (ψ : AddChar F ℂ) (f : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b, f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1) ∂(Measure.pi fun _ : Fin r => M.μF)

def rowMap (g : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) : Gl r F :=
  (Y.1, fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 0, Y.2.2.2)

def rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (Y : Gl r F) : ℂ := h (rowMap g Y)

def weil (M : Meas r F E) (ψ : AddChar F ℂ) (g : SpecialLinearGroup (Fin 2) F) (f : Gl r F → ℂ) : Gl r F → ℂ :=
  ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct g (ptrB M ψ f))))

def negB (f : Gl r F → ℂ) (Y : Gl r F) : ℂ := f (Y.1, -Y.2.1, Y.2.2.1, Y.2.2.2)

end GlobalTheory.JR.WeilMix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotientStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_average_abelian_quotient_alt : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  first | exact @GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | exact GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | (intros; apply GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubringStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ) (x : GL (Fin r) K), (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) = Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  first | exact @GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | exact GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | (intros; apply GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRepApply
section
namespace GlobalTheory.JR.WeilProd

def tensorRep {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    G × H → (X × Y → ℂ) → X × Y → ℂ :=
  fun g f p => W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1

theorem tensorRep_apply {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) (g : G × H)
    (f : X × Y → ℂ) (p : X × Y) :
    tensorRep W₁ W₂ g f p = W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1 := rfl

end GlobalTheory.JR.WeilProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusInvMulPowValuationNonnegIffStatement
section
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  first | exact @GlobalTheory.TorusInteg.torus_integral_iff | exact GlobalTheory.TorusInteg.torus_integral_iff | (intros; apply GlobalTheory.TorusInteg.torus_integral_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusSubmoduleMulLeftImageMemSelfDualStableLattiStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices : ∀ (K : UQ) (B : InvAlg K) (x : B.A), ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  first | exact @GlobalTheory.UnitLemma.TorusAction.torus_mem_X | exact GlobalTheory.UnitLemma.TorusAction.torus_mem_X | (intros; apply GlobalTheory.UnitLemma.TorusAction.torus_mem_X <;> assumption)
end

