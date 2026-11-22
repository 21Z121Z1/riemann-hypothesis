import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitProperOfInvertibleKrylovColumns
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OrbProper

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem continuous_bm : Continuous (fun X : Hn r F E => Bm X.toGl) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((((continuous_subtype_val.comp continuous_fst).pow (j : ℕ))).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_actU :
    Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU q.1 q.2) := by
  haveI := ImgSec.continuousStar (E := E) F
  have hg : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact ((hg.mul hA).mul hg.star).subtype_mk _
  · exact hg.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))
  · exact continuous_snd.comp (continuous_snd.comp continuous_snd)

theorem continuousOn_inv {X : Type} [TopologicalSpace X] {Ω : Set X} {h : X → Matrix (Fin r) (Fin r) E}
    (hh : ContinuousOn h Ω) (hu : ∀ a ∈ Ω, IsUnit (h a).det) : ContinuousOn (fun a => (h a)⁻¹) Ω := by
  have : (fun a => (h a)⁻¹) = fun a => ((h a).det)⁻¹ • (h a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  refine ContinuousOn.smul (f := fun a => ((h a).det)⁻¹) (g := fun a => (h a).adjugate) ?_ ?_
  · exact (continuous_id.matrix_det.comp_continuousOn hh).inv₀ fun a ha => (hu a ha).ne_zero
  · exact continuous_id.matrix_adjugate.comp_continuousOn hh

theorem isCompact_orbit (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E)
    (h : Inv r F → Matrix (Fin r) (Fin r) E) (hΩ : IsCompact Ω) (hs : ContinuousOn s Ω) (hhc : ContinuousOn h Ω)
    (hb : ∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) (C : Set (Hn r F E)) (hC : IsCompact C) :
    IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
  haveI := ImgSec.continuousStar (E := E) F
  set Φ : Hn r F E × Inv r F → Matrix (Fin r) (Fin r) E := fun q => Bm q.1.toGl * (h q.2)⁻¹ with hΦ
  have hΦc : ContinuousOn Φ (C ×ˢ Ω) := by
    refine (continuous_bm.comp continuous_fst).continuousOn.mul ?_
    exact (continuousOn_inv hhc fun a ha => (hb a ha).1).comp continuous_snd.continuousOn
      (fun q hq => hq.2)
  have hM : IsCompact (Φ '' (C ×ˢ Ω)) := (hC.prod hΩ).image_of_continuousOn hΦc
  have hU : IsClosed ((Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E))) := isClosed_unitary
  have hK : IsCompact (((↑) : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    (hU.isClosedEmbedding_subtypeVal).isCompact_preimage hM
  have hcl : IsClosed {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
    have hf : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2))
        (Set.univ ×ˢ Ω) := by
      have h1 : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => (p.1, s p.2)) (Set.univ ×ˢ Ω) :=
        continuous_fst.continuousOn.prodMk (hs.comp continuous_snd.continuousOn (fun q hq => hq.2))
      have h2 := (continuous_actU (F := F) (E := E) (r := r)).comp_continuousOn h1
      exact h2
    have hC2 : IsClosed C := hC.isClosed
    have hO2 : IsClosed (Set.univ ×ˢ Ω : Set (Matrix.unitaryGroup (Fin r) E × Inv r F)) := isClosed_univ.prod hΩ.isClosed
    have h3 := hf.preimage_isClosed_of_isClosed hO2 hC2
    have heq : {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} =
        (Set.univ ×ˢ Ω) ∩ (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2)) ⁻¹' C := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage]
    rw [heq]; exact h3
  refine (hK.prod hΩ).of_isClosed_subset hcl ?_
  rintro ⟨g, a⟩ ⟨ha, hC'⟩
  refine ⟨⟨(actU g (s a), a), ⟨hC', ha⟩, ?_⟩, ha⟩
  simp only [hΦ]
  rw [ImgSec.bm_actU, (hb a ha).2, Matrix.mul_nonsing_inv_cancel_right _ _ (hb a ha).1]

end GlobalTheory.JR.OrbProper

theorem GlobalTheory.JR.orbit_proper_of_columns : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} :=
  fun _ _ _ _ _ _ _ r Ω s h hΩ hs hh hb C hC => GlobalTheory.JR.OrbProper.isCompact_orbit r Ω s h hΩ hs hh hb C hC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedInvolutionExtMapsIntegersToIntegers
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0 := by simpa using he
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem map_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (x : K.O) :
    ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
  have hφ : φ (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  have hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x)) := by
    rw [hU.2.2.1]; exact val_nonneg_of_int K x
  exact IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts : ∀ (K : UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u → ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧ (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧ (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧ ∀ x : K.E, val K.O (K.c x) = val K.O x := by
  first | exact @GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | exact GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | (intros; apply GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStar
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  intro F E _ _ _ _ hU y
  classical
  have hfr : Module.finrank F E = 2 := hU.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut E)) (fun x => hU.star_fix x)
  have hσ : ∀ z, σ z = star z := fun z => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    obtain ⟨z, hz⟩ := hU.star_ne
    apply hz
    rw [← hσ, ← h]; rfl
  have hle : Nat.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hfr]
    exact (Nat.card_le_card_of_injective _ AlgEquiv.coe_algHom_injective).trans (card_algHom_le_finrank F E E)
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    refine le_antisymm hle ?_
    have : Fintype.card (E ≃ₐ[F] E) ≥ 2 := by
      have h2 : (({1, σ} : Finset (E ≃ₐ[F] E))).card = 2 := Finset.card_pair hne
      rw [← h2]; exact Finset.card_le_univ _
    rwa [Nat.card_eq_fintype_card]
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfr])
  rw [trace_eq_sum_automorphisms]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} := by
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  rw [huniv, Finset.sum_pair hne]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishAtHodgeTateCocharacter
section
open MvPolynomial

namespace GlobalTheory.HTCPoly

theorem prod_zpow_eq {ι G : Type} [CommGroup G] (u : G) (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, u ^ a i = u ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]

def wt (k : n → ℤ) (m : (n × n) →₀ ℕ) : ℤ := ∑ i : n × n, (m i : ℤ) * k i.2

theorem unit_prod (k : n → ℤ) (u : Cˣ) (m : (n × n) →₀ ℕ) :
    ∏ i : n × n, ((u ^ k i.2 : Cˣ) : C) ^ (m i) = ((u ^ wt k m : Cˣ) : C) := by
  have h : ∏ i : n × n, (u ^ k i.2) ^ (m i) = u ^ wt k m := by
    rw [wt, ← prod_zpow_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [← h, Units.coe_prod]
  simp [Units.val_pow_eq_pow_val]

theorem eval_eq_sum {σ : Type} [Fintype σ] (x : σ → C) (p : MvPolynomial σ C)
    (s : Finset (σ →₀ ℕ)) (hs : p.support ⊆ s) :
    eval x p = ∑ m ∈ s, coeff m p * ∏ i, x i ^ m i := by
  rw [eval_eq']
  refine Finset.sum_subset hs fun m _ hm => ?_
  have : coeff m p = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [this, zero_mul]

theorem eval_mul_diag (k : n → ℤ) (u : Cˣ) (y : Matrix n n C) (p : MvPolynomial (n × n) C)
    (s : Finset ((n × n) →₀ ℕ)) (hs : p.support ⊆ s) :
    eval (fun ij => (y * Matrix.diagonal (fun j => ((u ^ k j : Cˣ) : C))) ij.1 ij.2) p
      = ∑ m ∈ s, ((u ^ wt k m : Cˣ) : C) * coeff m p * ∏ i : n × n, y i.1 i.2 ^ m i := by
  rw [eval_eq_sum _ _ s hs]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [Matrix.mul_diagonal, mul_pow, Finset.prod_mul_distrib, unit_prod]
  ring

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

def vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C) :
    Submodule C (((n × n) →₀ ℕ) →₀ C) where
  carrier := {φ | ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (a + b) : MvPolynomial (n × n) C) =
      AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b by simp, map_add, ha γ, hb γ, add_zero]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro c a ha γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (c • a) : MvPolynomial (n × n) C) =
      c • AddMonoidAlgebra.ofCoeff a by simp, smul_eval, ha γ, mul_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly
variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]
variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

theorem mem_vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C)
    (φ : ((n × n) →₀ ℕ) →₀ C) :
    φ ∈ vanJ ρ P ↔ ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0 := Iff.rfl

theorem vanJ_stable (χ : Γ →* Cˣ) (ρ : Γ →* Matrix.GeneralLinearGroup n C)
    (hfix : ∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j)
    (P : Matrix n n C) (k : n → ℤ)
    (hP : ∀ g : Γ, (ρ g : Matrix n n C) * P.map (fun a => g • a) =
      P * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) :
    ∀ g : Γ, ∀ φ ∈ vanJ ρ P, ∃ ψ ∈ vanJ ρ P,
      ∀ m, ψ m = ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) := by
  intro g φ hφ
  refine ⟨Finsupp.onFinset φ.support (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) ?_, ?_,
    fun m => Finsupp.onFinset_apply⟩
  · intro m hm
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hm
    rw [h0, smul_zero, mul_zero]
  · rw [mem_vanJ] at hφ ⊢
    intro γ
    set σg := MulSemiringAction.toRingHom Γ C g
    set p : MvPolynomial (n × n) C := AddMonoidAlgebra.ofCoeff φ
    have hfix' : (ρ (γ * g) : Matrix n n C).map σg = ρ (γ * g) := by
      ext i j
      exact hfix g (γ * g) i j
    have key : (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C)) =
        ((ρ (γ * g) : Matrix n n C) * P).map σg := by
      calc (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))
          = (ρ γ : Matrix n n C) * (P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))) :=
            Matrix.mul_assoc _ _ _
        _ = (ρ γ : Matrix n n C) * ((ρ g : Matrix n n C) * P.map (fun a => g • a)) := by rw [hP g]
        _ = ((ρ (γ * g) : Matrix n n C) * P).map σg := by
            rw [Matrix.map_mul, hfix', map_mul, Units.val_mul, Matrix.mul_assoc]
            rfl
    have e1 : eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
        (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset φ.support
          (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) (by
            intro m hm
            rw [Finsupp.mem_support_iff]
            intro h0
            apply hm
            rw [h0, smul_zero, mul_zero])) : MvPolynomial (n × n) C)
        = ∑ m ∈ φ.support, ((χ g ^ wt k m : Cˣ) : C) * coeff m (map σg p) *
            ∏ i : n × n, ((ρ γ : Matrix n n C) * P) i.1 i.2 ^ m i := by
      refine (eval_eq_sum _ _ φ.support ?_).trans ?_
      · intro m hm
        rw [MvPolynomial.mem_support_iff] at hm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply hm
        show ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) = 0
        rw [h0, smul_zero, mul_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_map]
      rfl
    rw [e1, ← eval_mul_diag k (χ g) _ (map σg p) φ.support (MvPolynomial.support_map_subset _ _), key]
    have h2 := eval₂_comp_left σg (RingHom.id C)
      (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
    rw [RingHom.comp_id] at h2
    rw [eval_map]
    calc eval₂ σg (fun ij : n × n => (((ρ (γ * g) : Matrix n n C) * P).map σg) ij.1 ij.2) p
        = σg (eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p) :=
          h2.symm
      _ = 0 := by
          rw [show eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
            = eval (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p from rfl, hφ (γ * g),
            map_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly

theorem vanish_at_cocharacter : ∀ {C Γ n : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] [Fintype n] [DecidableEq n] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (ρ : Γ →* Matrix.GeneralLinearGroup n C), (∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j) → ∀ (P : Matrix.GeneralLinearGroup n C) (k : n → ℤ), (∀ g : Γ, (ρ g : Matrix n n C) * (P : Matrix n n C).map (fun a => g • a) = (P : Matrix n n C) * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) → ∀ f : MvPolynomial (n × n) C, (∀ γ : Γ, MvPolynomial.eval (fun ij => (ρ γ : Matrix n n C) ij.1 ij.2) f = 0) → ∀ t : Cˣ, MvPolynomial.eval (fun ij => ((P : Matrix n n C) * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)) * ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C)) ij.1 ij.2) f = 0 := by
  intro C Γ n _ _ _ _ _ χ hT ρ hfix P k hP f hf t
  set Pm : Matrix n n C := (P : Matrix n n C) with hPm
  set Qm : Matrix n n C := ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C) with hQm
  have hPQ : Pm * Qm = 1 := by
    rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let q : n × n → MvPolynomial (n × n) C := fun ij => ∑ l, X (ij.1, l) * MvPolynomial.C (Qm l ij.2)
  have hφ : ∀ y : Matrix n n C, eval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      eval (fun ij : n × n => (y * Qm) ij.1 ij.2) f := by
    intro y
    show aeval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      aeval (fun ij : n × n => (y * Qm) ij.1 ij.2) f
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun F : n × n → C => aeval F f) (funext fun ij => ?_)
    simp [q, Matrix.mul_apply]
  set p : MvPolynomial (n × n) C := aeval q f with hp
  have hpJ : AddMonoidAlgebra.coeff p ∈ vanJ ρ Pm := by
    rw [mem_vanJ]
    intro γ
    show eval _ p = 0
    rw [hφ, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    exact hf γ
  have hgr := GlobalTheory.T.filter_weight_mem_of_tate_graded_stable χ hT (wt k) (vanJ ρ Pm) (vanJ_stable χ ρ hfix Pm k hP) _ hpJ
  have hzero : ∀ d : ℤ, eval (fun ij : n × n => Pm ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter (fun m => wt k m = d)) :
        MvPolynomial (n × n) C) = 0 := by
    intro d
    have h1 := (mem_vanJ ρ Pm _).mp (hgr d) 1
    rwa [map_one, Units.val_one, Matrix.one_mul] at h1
  rw [← hφ (Pm * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)))]
  rw [eval_mul_diag k t Pm p p.support subset_rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (t := p.support.image (wt k)) (g := wt k)
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← mul_zero ((t ^ d : Cˣ) : C), ← hzero d,
    eval_eq_sum _ _ (p.support.filter (fun m => wt k m = d)) ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have hc : coeff m (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter
        (fun m => wt k m = d)) : MvPolynomial (n × n) C) = coeff m p :=
      Finsupp.filter_apply_pos _ _ hm.2
    rw [hc, hm.2]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at hm
    rw [Finset.mem_filter, MvPolynomial.mem_support_iff]
    by_contra hne
    apply hm
    show (Finsupp.filter (fun m => wt k m = d) (AddMonoidAlgebra.coeff p)) m = 0
    by_cases hw : wt k m = d
    · rw [Finsupp.filter_apply_pos (fun m => wt k m = d) _ hw]
      by_contra h
      exact hne ⟨h, hw⟩
    · exact Finsupp.filter_apply_neg _ _ hw

end GlobalTheory.HTCPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def cc (A : Et F E) (e : A.L) (p : A.K × A.K) : A.L :=
  algebraMap A.K A.L p.1 * e + algebraMap A.K A.L p.2 * (1 - e)

def ci (A : Et F E) (e : A.L) (y : A.L) : A.K × A.K :=
  (Algebra.trace A.K A.L (y * e), Algebra.trace A.K A.L (y * (1 - e)))

def kx (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (u b : A.K) : ℂ := A.psiK ψ (x * u * b)

def pt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  fourB ν (kx A ψ x) (fun b => Φ (p.1, b)) p.2

def rg (A : Et F E) (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  Φ (p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 0 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 0,
    p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 1 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 1)

def wHyp (A : Et F E) (e : A.L) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K)
    (g : SpecialLinearGroup (Fin 2) A.K) (φ : A.L → ℂ) (y : A.L) : ℂ :=
  pt A ν ψ x (pt A ν ψ x (pt A ν ψ x (rg A g (pt A ν ψ x (fun p => φ (cc A e p)))))) (ci A e y)

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionEisensteinPowIntegral
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.WDivE

theorem coeff_vanish_mul {K : Type} [CommRing K] {F G : K⟦X⟧} {a b : ℕ}
    (hF : ∀ k, a < k → coeff k F = 0) (hG : ∀ k, b < k → coeff k G = 0) (k : ℕ) (hk : a + b < k) :
    coeff k (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : a < p.1
  · rw [hF _ h, zero_mul]
  · rw [hG _ (by omega), mul_zero]

theorem eq_sum_of_vanish {K : Type} [CommRing K] {P : K⟦X⟧} {N : ℕ}
    (hP : ∀ k, N ≤ k → coeff k P = 0) : P = ∑ k : Fin N, C (coeff (k : ℕ) P) * X ^ (k : ℕ) := by
  ext m
  rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m < N
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [hP m (by omega), Finset.sum_eq_zero]
    intro b _; rw [if_neg]; omega

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [CompleteSpace K] [NeZero e] in
theorem quotE_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : quotE l e f ∈ A O K := fun n => by
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)

theorem div_E_step {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e * g :=
  ⟨f - E K l e * quotE l e f, quotE l e f,
    sub_mem hf (mul_mem (E_mem l e _) (quotE_mem_A l e hf)),
    fun k hk => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact coeff_sub_E_mul_quotE l e (A_le_Rpi l e hf) m,
    quotE_mem_A l e hf, by ring⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem coeff_E_pow_vanish (n : ℕ) : ∀ k, e * n < k → coeff k (E K l e ^ n) = 0 := by
  induction n with
  | zero => intro k hk; simp [coeff_one]; omega
  | succ n ih =>
    intro k hk
    rw [pow_succ]
    refine coeff_vanish_mul ih (b := e) (fun j hj => ?_) k (by rw [Nat.mul_succ] at hk; exact hk)
    rw [E, map_add, coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem div_E_pow (n : ℕ) {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e * n ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e ^ n * g := by
  induction n with
  | zero => exact ⟨0, f, zero_mem _, fun _ _ => by simp, hf, by simp⟩
  | succ n ih =>
    obtain ⟨P, g, hP, hPv, hg, rfl⟩ := ih
    obtain ⟨Q, h, hQ, hQv, hh, rfl⟩ := div_E_step l e hg
    refine ⟨P + E K l e ^ n * Q, h, add_mem hP (mul_mem (pow_mem (E_mem l e _) n) hQ),
      fun k hk => ?_, hh, by ring⟩
    have he := NeZero.pos e
    rw [map_add, hPv k (by rw [Nat.mul_succ] at hk; omega), zero_add]
    exact coeff_vanish_mul (coeff_E_pow_vanish l e n) (b := e - 1)
      (fun j hj => hQv j (by omega)) k (by rw [Nat.mul_succ] at hk; omega)

end GlobalTheory.WDivE

theorem GlobalTheory.weierstrassDiv_E_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  intro O K _ _ _ _ _ _ l e _ _ _ n f hf
  obtain ⟨P, g, hP, hPv, hg, rfl⟩ := GlobalTheory.WDivE.div_E_pow l e n hf
  choose c hc using fun k : Fin (e * n) => (IsUnitBall.mem_range_iff (O := O) (coeff (k : ℕ) P)).2 (hP k)
  refine ⟨c, g, hg, ?_⟩
  simp only [hc]
  rw [← GlobalTheory.WDivE.eq_sum_of_vanish hPv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeylNumeratorLaplace
section
open Polynomial

namespace GlobalTheory

theorem weylNumerator_laplace : ∀ (a b : ℕ) (α : Fin a → ℂˣ) (β : Fin b → ℂˣ) (l : Fin (a + b) → ℤ), (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α β i : ℂˣ) ^ l j : ℂˣ) : ℂ)).det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * (Matrix.of fun i k : Fin a => ((α i ^ l (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det * (Matrix.of fun i k : Fin b => ((β i ^ l (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det := by
  intro a b α β l
  rw [Formalism.ResultantValuation.laplaceExpansionRows ℂ a b]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [Nat.add_comm (a * (a - 1) / 2)]
  congr 2
  · congr 1
    ext i k
    simp [Matrix.submatrix]
  · congr 1
    ext i k
    simp [Matrix.submatrix]

end GlobalTheory
end

