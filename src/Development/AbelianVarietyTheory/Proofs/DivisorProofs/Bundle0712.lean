import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHermitianTraceFormIntegralStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.RealMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hermitian_trace_form_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E) (𝔠 : FracId (maximalRealSubfield E))
    (mu : E) (c1 : maximalRealSubfield E) (Q : E → E → maximalRealSubfield E) (l : ℕ) (c₀ : 𝔠.elt), c1 ≠ 0 →
    IsCMField.complexConj E mu = -mu →
    (∀ (a : OF E), ∀ x ∈ L, ∀ x' ∈ L, Q (algebraMap (OF E) E a * x) x' = (a : maximalRealSubfield E) * Q x x') →
    (∀ x ∈ L, ∀ x' ∈ L, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (maximalRealSubfield E) (c1 * Q x x')) →
    (∀ x ∈ L, ∀ x' ∈ L, Q x x' ∈ dualLat 𝔠) →
    (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'}) →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (maximalRealSubfield E)), n.Coprime l ∧ n • c = t • c₀) →
    mu ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod L)
      ((((c₀ : maximalRealSubfield E) / (2 * c1) : maximalRealSubfield E) : E) * mu) := by
  first | exact @GlobalTheory.PolGen.genAt_polMod | exact GlobalTheory.PolGen.genAt_polMod | (intros; apply GlobalTheory.PolGen.genAt_polMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdeal
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobRel
theorem coeff_subst_sub_mem : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ] (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) → (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) → ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := GlobalTheory.T.mvPowerSeries_subst_coeff_sub_mem_ideal

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one

theorem coeff_prod_addLeft : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups

theorem coeff_prod_addRight : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3

theorem coeff_evalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero

theorem coeff_evalTwoGroups_first_second_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem degree_sumElim3 {d : ℕ} (a b e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a (Finsupp.sumElim b e)).degree = a.degree + b.degree + e.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_sum_type, add_assoc]

theorem x_hasSubst {R : Type} [CommRing R] {d : ℕ} (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem cocycle_rel_mod : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  intro B O Q _ _ _ _ θ d μ hμ N m c hc hcob n hn a b ha _ hab hab'
  set e := n - (a + b) with he_def
  have he : e ≠ 0 := fun h => hab' (le_antisymm hab (tsub_eq_zero_iff_le.1 h))
  have hbe : b + e = n - a := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  have hn' : a + b + e = n := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  set w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ := Finsupp.sumElim a (Finsupp.sumElim b e) with hw_def
  have hw : w.degree = m := by
    rw [← hn, ← hn', hw_def, degree_sumElim3, map_add, map_add]
  have hX : ∀ (R : Type) [CommRing R] (j : Fin d),
      constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := fun R _ j => by
    simp [x1, x2, x3]
  have hop : ∀ (R : Type) [CommRing R] (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (ν i) = 0) → ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      constantCoeff (op ν u v i) = 0 := fun R _ ν hν u v hu hv i =>
    constantCoeff_subst_eq_zero (x_hasSubst u v hu hv) (fun s => by cases s <;> simp [hu, hv]) (hν i)
  have hmapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      map (algebraMap B Q) (op μ u v i) = op (up Q μ) (fun j => map (algebraMap B Q) (u j))
        (fun j => map (algebraMap B Q) (v j)) i := fun u v hu hv i => by
    simp only [op, at2, up]
    rw [map_subst (x_hasSubst u v hu hv)]
    congr 1
    funext s
    cases s <;> rfl
  have hmX : ∀ j, (map (algebraMap B Q) (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x1 j) ∧
      (map (algebraMap B Q) (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x2 j) ∧
      (map (algebraMap B Q) (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x3 j) := fun j => by
    simp [x1, x2, x3, map_X]

  have hc2 : ∀ s, constantCoeff (Sum.elim (op μ x1 x2) x3 s) = 0 := by
    intro s
    cases s with
    | inl i => exact hop B μ hμ.const _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i
    | inr i => exact (hX B i).2.2
  have hd2 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim (op μ x1 x2) x3 s) = coeff β (Sum.elim (fun i => x1 i + x2 i) x3 s) := by
    intro s β hβ
    cases s with
    | inl i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i β hβ
    | inr i => rfl
  obtain ⟨r2, hr2, h2⟩ := coeff_subst_sub_mem N _ _ hc2 hd2 m c hc w hw
  have hu2 : up Q (Sum.elim (op μ x1 x2) x3) = Sum.elim (op (up Q μ) x1 x2) x3 := by
    funext s
    cases s with
    | inl i =>
      simp only [up, Sum.elim_inl]
      rw [hmapop _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1)]
      simp only [(hmX _).1, (hmX _).2.1]
    | inr i => simp only [up, Sum.elim_inr]; exact (hmX i).2.2
  have hl2 : up Q (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) x3) =
      Sum.elim (fun i => x1 i + x2 i) x3 := by
    funext s
    cases s with
    | inl i => simp only [up, Sum.elim_inl, map_add, (hmX i).1, (hmX i).2.1]
    | inr i => simp only [up, Sum.elim_inr]; exact (hmX i).2.2
  rw [hu2, hl2] at h2
  have hv2 : coeff w (subst (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q)) x3) c) =
      (∏ i, ((a + b) i).choose (a i) : Q) * coeff (Finsupp.sumElim (a + b) e) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => by simp [(hX Q j).1, (hX Q j).2.1]) (fun j => (hX Q j).2.2)),
      finsum_eq_single _ (Finsupp.sumElim (a + b) e)]
    · rw [hw_def, coeff_prod_addLeft, if_pos rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addLeft, if_neg hα, smul_zero]

  have hc3 : ∀ s, constantCoeff (Sum.elim x1 (op μ x2 x3) s) = 0 := by
    intro s
    cases s with
    | inl i => exact (hX B i).1
    | inr i => exact hop B μ hμ.const _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i
  have hd3 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim x1 (op μ x2 x3) s) = coeff β (Sum.elim x1 (fun i => x2 i + x3 i) s) := by
    intro s β hβ
    cases s with
    | inl i => rfl
    | inr i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i β hβ
  obtain ⟨r3, hr3, h3⟩ := coeff_subst_sub_mem N _ _ hc3 hd3 m c hc w hw
  have hu3 : up Q (Sum.elim x1 (op μ x2 x3)) = Sum.elim x1 (op (up Q μ) x2 x3) := by
    funext s
    cases s with
    | inl i => simp only [up, Sum.elim_inl]; exact (hmX i).1
    | inr i =>
      simp only [up, Sum.elim_inr]
      rw [hmapop _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2)]
      simp only [(hmX _).2.1, (hmX _).2.2]
  have hl3 : up Q (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      Sum.elim x1 (fun i => x2 i + x3 i) := by
    funext s
    cases s with
    | inl i => simp only [up, Sum.elim_inl]; exact (hmX i).1
    | inr i => simp only [up, Sum.elim_inr, map_add, (hmX i).2.1, (hmX i).2.2]
  rw [hu3, hl3] at h3
  have hv3 : coeff w (subst (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q))) c) =
      (∏ i, ((b + e) i).choose (b i) : Q) * coeff (Finsupp.sumElim a (b + e)) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => (hX Q j).1) (fun j => by simp [(hX Q j).2.1, (hX Q j).2.2])),
      finsum_eq_single _ (Finsupp.sumElim a (b + e))]
    · rw [hw_def, coeff_prod_addRight, if_pos rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addRight, if_neg hα, smul_zero]

  obtain ⟨k, hk, hk'⟩ := hcob w
  have hsplit : coeff w (cob2 (up Q μ) c) = coeff w (at2 c x2 x3) -
      coeff w (subst (Sum.elim (op (up Q μ) x1 x2) x3) c) +
      coeff w (subst (Sum.elim x1 (op (up Q μ) x2 x3)) c) - coeff w (at2 c x1 x2) := by
    simp only [cob2, map_sub, map_add]; rfl
  rw [hsplit, hw_def, coeff_evalTwoGroups_second_third_eq_zero c a b e ha, coeff_evalTwoGroups_first_second_eq_zero c a b e he, ← hw_def] at hk'
  rw [hbe] at hv3
  refine ⟨-k - r2 + r3, N.add_mem (N.sub_mem (N.neg_mem hk) hr2) hr3, ?_⟩
  rw [map_add, map_sub, map_neg, ← hk', ← h2, ← h3, hv2, hv3]
  ring

end GlobalTheory.CobRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModP
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem cob2_cob1_lift_mem_intBy_and_swap_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ →
    ∀ f ∈ quasiInt p k (Fin d),
      cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧
      swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈
        intBy p k _ p := by
  intro p _ k _ _ _ d μ hμ f hf
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  obtain ⟨hcc1, hcc2, -⟩ := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL f
  have hred := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have hr := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)

  have hX3 : ∀ (j : Fin d ⊕ (Fin d ⊕ Fin d)),
      constantCoeff (X j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)) = 0 :=
    fun j => constantCoeff_X j
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff (op (fun i => Katz.lift p (μ i)) a b i) = 0 := by
    intro a b ha hb i
    exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty a b ha hb).2.2.2.1 _).trans (hL i)
  refine ⟨?_, ?_⟩
  · rw [hcc1]
    have hA := hop x1 _ hx1 (hop x2 x3 hx2 hx3)
    have hB := hop _ x3 (hop x1 x2 hx1 hx2) hx3
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) _ _ (op μ x1 (op μ x2 x3)) f
      hA hB (fun i => (hred.2.2.1 i).1) (fun i => ?_) hf
    rw [← hμ.assoc]
    exact (hred.2.2.1 i).2
  · rw [hcc2]
    have hXs : ∀ (j : Fin d ⊕ Fin d),
        constantCoeff (X j : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
      fun j => constantCoeff_X j
    have hS : ∀ i, constantCoeff (swap (Katz.lift p (μ i))) = 0 := by
      intro i
      exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty _ _ (fun j => hXs _) (fun j => hXs _)).2.2.2.1 _).trans
        (hL i)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ Fin d) _ _ μ f hS hL (fun i => ?_)
      (fun i => (hr.2.2.1 (μ i))) hf
    have := (hred.1 _ _ (hr.2.2.1 (μ i))).2
    rwa [hμ.comm i] at this

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegree
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries TensorProduct GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup WithConv

namespace GlobalTheory.EvMul

theorem coeff_subst_eq_zero_of_degree {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) {N : ℕ}
    {f : MvPowerSeries σ R} (hf : ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0)
    (β : τ →₀ ℕ) (hβ : β.degree < N) : coeff β (subst a f) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree < N
  · rw [hf α h, zero_smul]
  · rw [coeff_of_lt_order (f := α.prod fun s e => a s ^ e) (d := β) ?_, smul_zero]
    refine lt_of_lt_of_le (b := ((α.degree : ℕ) : ℕ∞)) (by exact_mod_cast (by omega : β.degree < α.degree)) ?_
    rw [Finsupp.prod]
    refine le_trans ?_ (le_order_prod _ _)
    show ((∑ i ∈ α.support, α i : ℕ) : ℕ∞) ≤ _
    push_cast
    exact Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun l => (X l : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = at2 (μ i) (nmul μ k) (fun l => X l) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    rw [e, at2]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ i)

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

theorem mulBy_succ_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (k : ℕ) (a : A) :
    PDiv.mulBy O A (k + 1) a = Algebra.TensorProduct.lmul' O
      (Algebra.TensorProduct.map (PDiv.mulBy O A k : A →ₐ[O] A) (AlgHom.id O A) (Coalgebra.comul a)) := by
  rw [PDiv.mulBy, pow_succ]
  rfl

theorem mulBy_zero_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (a : A) :
    PDiv.mulBy O A 0 a = algebraMap O A (Coalgebra.counit a) := by
  rw [PDiv.mulBy, pow_zero]
  rfl

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]

theorem pow_dvd_map {A B : Type} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (φ : A →ₐ[O] B) {m : ℕ} {a : A} (h : (p : A) ^ m ∣ a) : (p : B) ^ m ∣ φ a := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨φ y, by rw [map_mul, map_pow, map_natCast]⟩

theorem cont_subst {σ τ : Type} [Finite τ] {A : Type} [CommRing A] [Algebra O A]
    (E : MvPowerSeries σ O →ₐ[O] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    {a : τ → MvPowerSeries σ O} (ha : ∀ i, constantCoeff (a i) = 0) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : A) ^ m ∣ E.comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha)) f := by
  intro m
  obtain ⟨N, hN⟩ := hE m
  exact ⟨N, fun f hf => by
    rw [AlgHom.comp_apply, substAlgHom_apply]
    exact hN _ (coeff_subst_eq_zero_of_degree ha hf)⟩

variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_of_gen (n k : ℕ)
    (hk : ∀ i, c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i))
    (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  have ha := constantCoeff_nmul c.isLaw.const k
  have gens : ∀ i, ((c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha))) (X i) =
      ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) (X i) := by
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X, (c.isEval n).1, hk]
    rfl
  have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : G.A n) ^ m ∣ ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) f := by
    intro m
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    exact ⟨N, fun f hf => by
      rw [AlgHom.comp_apply]
      exact pow_dvd_map (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (hN f hf)⟩
  have e := GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext p O (Fin d) (G.A n) _ _ gens (cont_subst (c.ev n) (c.isEval n).2 ha) cont'
  have := DFunLike.congr_fun e h
  rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply] at this
  exact this

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]
variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_nmul (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  induction k generalizing i with
  | zero =>
    rw [mulBy_zero_apply, c.aug, map_zero]
    exact map_zero _
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun l => (X l : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    set Θ := (c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero hs)) with hΘ
    set Λ := (Algebra.TensorProduct.lmul' O).comp ((Algebra.TensorProduct.map
      (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (AlgHom.id O (G.A n))).comp (c.ev₂ n)) with hΛ
    have gens : ∀ j, Θ (X j) = Λ (X j) := by
      rintro (j | j)
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one]
        exact ih j
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul]
        exact (c.isEval n).1 j
    have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        (p : G.A n) ^ m ∣ Λ f := by
      intro m
      obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
      exact ⟨N, fun f hf => by
        rw [hΛ, AlgHom.comp_apply, AlgHom.comp_apply]
        exact pow_dvd_map _ (pow_dvd_map _ (hN f hf))⟩
    have e : Θ = Λ := GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext p O (Fin d ⊕ Fin d) (G.A n) Θ Λ gens
      (cont_subst (c.ev n) (c.isEval n).2 hs) cont'
    have e1 : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun l => X l) (c.μ i) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    have e2 := DFunLike.congr_fun e (c.μ i)
    rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply,
      c.comul] at e2
    rw [e1, e2, mulBy_succ_apply]

theorem ev_subst_nmul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n k : ℕ) (h : MvPowerSeries (Fin d) O),
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  intro p _ O _ _ G d c n k h
  exact ev_subst_of_gen c n k (ev_nmul c n k) h

end GlobalTheory.EvMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyClass_pullback_reduction_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  first | exact @GlobalTheory.AbCoh.red_preimage_pairs | exact GlobalTheory.AbCoh.red_preimage_pairs | (intros; apply GlobalTheory.AbCoh.red_preimage_pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_affine_limit
  | exact GlobalTheory.EtC.contCone_of_affine_limit
  | (intros; apply GlobalTheory.EtC.contCone_of_affine_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapLinear
section
set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem Close.comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W' →+* C) (ψ : Hol W →+* Hol W') (M : Fin g → Fin g' → ℂ), (∀ a f, dw a (ψ f) = ∑ b, M b a • ψ (dw b f)) → Close J ρ₁ ρ₂ → Close J (ρ₁.comp ψ) (ρ₂.comp ψ) := by
  intro I I' _ _ g g' W W' C _ J ρ₁ ρ₂ ψ M hψ h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail σ τ _ s ih =>
    obtain ⟨n, h1, h2, h3⟩ := s
    refine Relation.ReflTransGen.tail ih
      ⟨fun b ↦ ∑ a, σ (algebraMap ℂ (Hol W') (M b a)) * n a,
        fun b ↦ J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a), fun b c ↦ ?_, fun f ↦ ?_⟩
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun a' _ ↦ ?_
      calc σ (algebraMap ℂ (Hol W') (M b a)) * n a * (σ (algebraMap ℂ (Hol W') (M c a')) * n a')
          = σ (algebraMap ℂ (Hol W') (M b a)) * σ (algebraMap ℂ (Hol W') (M c a')) * (n a * n a') := by ring
        _ = 0 := by rw [h2, mul_zero]
    · simp only [RingHom.comp_apply]
      rw [h3 (ψ f)]
      congr 1
      simp_rw [hψ, map_sum, Algebra.smul_def, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
      ring

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSectionStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHermitianForm_unitaryChartSection : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ (τ : X.Ψ) (u v : Fin r → ℂ), hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  first | exact @GlobalTheory.SUChartSection.hermC_secM | exact GlobalTheory.SUChartSection.hermC_secM | (intros; apply GlobalTheory.SUChartSection.hermC_secM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComulChartSubSubstMemPSmulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comul_chart_sub_subst_mem_p_smul : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n, Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  first | exact @GlobalTheory.comul_ev_sub_ev₂_subst_mem | exact GlobalTheory.comul_ev_sub_ev₂_subst_mem | (intros; apply GlobalTheory.comul_ev_sub_ev₂_subst_mem <;> assumption)
end

