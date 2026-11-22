import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHermitianTraceFormIntegral
section
open NumberField GlobalTheory.CMVal GlobalTheory.RealMult

namespace GlobalTheory.PolGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_zero_of_trace {F : Type} [Field F] [NumberField F] (D : F)
    (h : ∀ a : 𝓞 F, Algebra.trace ℚ F ((a : F) * D) = 0) : D = 0 := by
  by_contra hD
  have halg : IsAlgebraic ℤ D⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ F ((m • D⁻¹) * D) = 0 := h ⟨m • D⁻¹, hint⟩
  have e : (m • D⁻¹) * D = algebraMap ℚ F (m : ℚ) := by
    rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hD]; simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have h2 : (Module.finrank ℚ F : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h3 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  exact mul_ne_zero h2 h3 h1

omit [IsCMField E] in

theorem trace_coe_mul (k : maximalRealSubfield E) (w : E) :
    Algebra.trace ℚ E ((k : E) * w) =
      Algebra.trace ℚ (maximalRealSubfield E) (k * Algebra.trace (maximalRealSubfield E) E w) := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  rw [← smul_eq_mul k, ← map_smul]
  rfl

theorem genAt_polMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E) (𝔠 : FracId (maximalRealSubfield E))
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
  intro E _ _ _ L 𝔠 mu c1 Q l c₀ h1 h2 h3 h4 h5 h6 h7
  have hL : ∀ (a : OF E), ∀ x ∈ L, algebraMap (OF E) E a * x ∈ L := fun a x hx => by
    rw [← Algebra.smul_def]; exact L.smul_mem a hx
  have hcoe : ∀ a : OF E, algebraMap (OF E) E a = ((a : maximalRealSubfield E) : E) := fun a => rfl
  have hc0 : (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) ≠ 0 :=
    𝔠.ne_zero
  have hd0 : dualLat 𝔠 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ hc0
  have key : ∀ x ∈ L, ∀ x' ∈ L, Algebra.trace (maximalRealSubfield E) E (mu * x * IsCMField.complexConj E x') =
      2 * c1 * Q x x' := by
    intro x hx x' hx'
    rw [← sub_eq_zero]
    apply eq_zero_of_trace
    intro a
    have h := h4 _ (hL a x hx) x' hx'
    rw [h3 a x hx x' hx'] at h
    have e : mu * (algebraMap (OF E) E a * x) * IsCMField.complexConj E x' =
        ((a : maximalRealSubfield E) : E) * (mu * x * IsCMField.complexConj E x') := by
      rw [hcoe]; ring
    rw [e, trace_coe_mul] at h
    have e2 : (a : maximalRealSubfield E) * (2 * c1 * Q x x') =
        c1 * (a * Q x x') + c1 * (a * Q x x') := by ring
    rw [mul_sub, map_sub, h, e2, map_add]; ring
  have key2 : ∀ (k : maximalRealSubfield E), ∀ x ∈ L, ∀ x' ∈ L,
      Algebra.trace ℚ E ((k : E) * mu * x * IsCMField.complexConj E x') =
        Algebra.trace ℚ (maximalRealSubfield E) (k * (2 * c1 * Q x x')) := by
    intro k x hx x' hx'
    rw [← key x hx x' hx', ← trace_coe_mul]
    congr 1; ring
  have h2c : (2 * c1 : maximalRealSubfield E) ≠ 0 := mul_ne_zero two_ne_zero h1
  have hmu : mu ≠ 0 := by
    rintro rfl
    apply hd0
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h := h6 t ht
    have hle : Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, x', hx', rfl⟩
      have := key x hx x' hx'
      rw [zero_mul, zero_mul, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left h2c
    exact hle h
  have hfix : ∀ k : maximalRealSubfield E, IsCMField.complexConj E (k : E) = k := fun k =>
    (IsCMField.complexConj E).commutes k
  refine ⟨hmu, ⟨?_, ?_⟩, ?_⟩
  · show IsCMField.complexConj E _ = _
    rw [map_mul, hfix, h2]; ring
  · intro x hx x' hx'
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hc0).1 (h5 x hx x' hx') c₀ c₀.2
    refine ⟨n, ?_⟩
    refine (key2 _ x hx x' hx').trans ?_
    rw [Algebra.traceForm_apply] at hn
    have e : (c₀ : maximalRealSubfield E) / (2 * c1) * (2 * c1 * Q x x') = Q x x' * c₀ := by
      field_simp
    rw [e, ← hn]; simp
  · rintro ν ⟨hν1, hν2⟩
    have hs : IsCMField.complexConj E (ν / mu) = ν / mu := by
      have hν1' : IsCMField.complexConj E ν = -ν := hν1
      rw [map_div₀, hν1', h2, neg_div_neg_eq]
    let s : maximalRealSubfield E := ⟨ν / mu, (IsCMField.complexConj_eq_self_iff E _).1 hs⟩
    have hνs : ν = (s : E) * mu := by
      show ν = ν / mu * mu
      field_simp
    have hmem : 2 * c1 * s ∈ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) := by
      rw [← FractionalIdeal.dual_dual ℤ ℚ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E))]
      refine (FractionalIdeal.mem_dual hd0).2 ?_
      intro t ht
      have h : ∀ a : OF E, Algebra.trace ℚ (maximalRealSubfield E) (2 * c1 * s * (a * t)) ∈ (algebraMap ℤ ℚ).range := by
        have h := h6 t ht
        clear ht
        induction h using Submodule.span_induction with
        | mem t ht =>
          obtain ⟨x, hx, x', hx', rfl⟩ := ht
          intro a
          obtain ⟨n, hn⟩ := hν2 _ (hL a x hx) x' hx'
          refine ⟨n, ?_⟩
          rw [hνs] at hn
          have h := (key2 s _ (hL a x hx) x' hx').symm.trans hn
          rw [h3 a x hx x' hx'] at h
          have e : 2 * c1 * s * (a * Q x x') = s * (2 * c1 * (a * Q x x')) := by ring
          rw [e, h]; simp
        | zero => intro a; simp
        | add t u _ _ ht hu =>
          intro a
          rw [mul_add, mul_add, map_add]
          exact add_mem (ht a) (hu a)
        | smul b t _ ht =>
          intro a
          have e : (a : maximalRealSubfield E) * b • t = ((a * b : OF E) : maximalRealSubfield E) * t := by
            rw [Algebra.smul_def, ← mul_assoc]
            congr 1
          rw [e]; exact ht _
      have := h 1
      rw [Algebra.traceForm_apply]
      simpa using this
    obtain ⟨n, t, hn, hnt⟩ := h7 ⟨2 * c1 * s, hmem⟩
    refine ⟨n, hn, t, ?_⟩
    have e : (n : maximalRealSubfield E) * (2 * c1 * s) = (t : maximalRealSubfield E) * c₀ := by
      have := congrArg Subtype.val hnt
      simpa [nsmul_eq_mul, Algebra.smul_def] using this
    have e2 : (n : maximalRealSubfield E) * s = (t : maximalRealSubfield E) * (c₀ / (2 * c1)) := by
      rw [mul_div_assoc', ← e]; field_simp
    have e3 := congrArg (fun z : maximalRealSubfield E => (z : E)) e2
    simp only [Subfield.coe_mul, SubringClass.coe_natCast] at e3
    rw [hcoe, hνs, ← mul_assoc, ← mul_assoc, e3]

end GlobalTheory.PolGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFinsuppProdConstFreeEqZeroOfDegreeLtStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt : ∀ (R : Type) [CommRing R] (σ τ : Type) (u : τ → MvPowerSeries σ R), (∀ j, constantCoeff (u j) = 0) → ∀ (α : τ →₀ ℕ) (β : σ →₀ ℕ), β.degree < α.degree → coeff β (α.prod fun j e => u j ^ e) = 0 := by
  first | exact @GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt | exact GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt | (intros; apply GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOneStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := by
  first | exact @GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | exact GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | (intros; apply GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPLogarithmsEqInvFrobeniusMatrixStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  first | exact @GlobalTheory.FrobCoef.coef_logs_inv_frob | exact GlobalTheory.FrobCoef.coef_logs_inv_frob | (intros; apply GlobalTheory.FrobCoef.coef_logs_inv_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | exact GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | (intros; apply GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroupsStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  first | exact @GlobalTheory.BinomLeft.coeff_prod_pow_add | exact GlobalTheory.BinomLeft.coeff_prod_pow_add | (intros; apply GlobalTheory.BinomLeft.coeff_prod_pow_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroupsStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3 : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := by
  first | exact @GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | exact GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups | (intros; apply GlobalTheory.BinomRight.coeff_prod_pow_second_add_third_threeGroups <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLtStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_eq_zero_of_degree_lt' : ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R) (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) → (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) → ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  first | exact @GlobalTheory.coeff_subst_eq_zero_of_degree_lt | exact GlobalTheory.coeff_subst_eq_zero_of_degree_lt | (intros; apply GlobalTheory.coeff_subst_eq_zero_of_degree_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmoduleStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  first | exact @GlobalTheory.SubstSub.coeff_subst_up_mem | exact GlobalTheory.SubstSub.coeff_subst_up_mem | (intros; apply GlobalTheory.SubstSub.coeff_subst_up_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariablesStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_restrict_sum_variables : ∀ {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ] (g : MvPowerSeries (ι ⊕ κ) R), (∀ α : ι →₀ ℕ, coeff α (subst (Sum.elim (fun i => (X i : MvPowerSeries ι R)) (fun _ => 0)) g) = coeff (α.mapDomain Sum.inl) g) ∧ (∀ α : κ →₀ ℕ, coeff α (subst (Sum.elim (fun _ => 0) (fun i => (X i : MvPowerSeries κ R))) g) = coeff (α.mapDomain Sum.inr) g) := by
  first | exact @GlobalTheory.coeff_subst_restrict_sum | exact GlobalTheory.coeff_subst_restrict_sum | (intros; apply GlobalTheory.coeff_subst_restrict_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroupsStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  first | exact @GlobalTheory.SwapCoeff.coeff_swap | exact GlobalTheory.SwapCoeff.coeff_swap | (intros; apply GlobalTheory.SwapCoeff.coeff_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  first
  | exact @GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | exact GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | (intros; apply GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist <;> assumption)
end

