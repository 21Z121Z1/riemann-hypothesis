import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstEqAddOfCob1EqZero
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieZero

theorem eq_zero_of_pow_dvd {O : Type} [CommRing O] {p : O} [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {p}) ‹_› x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (h n)

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun k => X k) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    have hb : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j)
        = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    rw [nmul_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hb) hb (hμ i)

theorem subst_eq_add_of_cob1_eq_zero {E : Type} [CommRing E] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) E)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) (hf : cob1 μ f = 0)
    {τ : Type} (b : Fin d ⊕ Fin d → MvPowerSeries τ E) (hb : HasSubst b) :
    subst (fun i => subst b (μ i)) f = subst (fun i => b (Sum.inl i)) f + subst (fun i => b (Sum.inr i)) f := by
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have h := congrArg (subst b) hf
  unfold cob1 inL inR at h
  rw [subst_sub hb, subst_sub hb, subst_comp_subst_apply hμs hb,
    subst_comp_subst_apply hL hb, subst_comp_subst_apply hR hb, ← coe_substAlgHom hb, map_zero,
    coe_substAlgHom hb] at h
  simp only [subst_X hb] at h
  rw [← sub_eq_zero, ← h, sub_sub]

theorem subst_nmul_of_cob1_eq_zero {O E : Type} [CommRing O] [CommRing E] [Algebra O E]
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E μ) f = 0) (m : ℕ) :
    subst (up E (nmul μ m)) f = (m : E) • f := by
  have hμ' : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hμ i]
  induction m with
  | zero =>
    have h0 : up E (nmul μ 0) = (0 : Fin d → MvPowerSeries (Fin d) E) := by
      funext i; simp [up, nmul]
    rw [h0, Nat.cast_zero, zero_smul]
    have h := subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E)
      HasSubst.zero
    have h1 : (fun i => subst (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (up E μ i)) = 0 := by
      funext i; exact subst_zero_of_constantCoeff_zero (hμ' i)
    rw [h1] at h
    have h2 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inl i)) = 0 := rfl
    have h3 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inr i)) = 0 := rfl
    rw [h2, h3] at h
    linear_combination -h
  | succ m ih =>
    have hc : ∀ j, constantCoeff (Sum.elim (nmul μ m) (fun k => (X k : MvPowerSeries (Fin d) O)) j)
        = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ m j
      · simp
    have hc' : ∀ j, constantCoeff (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp [up, constantCoeff_map, constantCoeff_nmul μ hμ m j]
      · simp
    have hs : up E (nmul μ (m + 1)) = fun i => subst (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E))) (up E μ i) := by
      funext i
      simp only [up, nmul_succ, op, at2]
      rw [map_subst (hasSubst_of_constantCoeff_zero hc)]
      congr 1
      funext j
      rcases j with j | j <;> simp [up]
    rw [hs, subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf _ (hasSubst_of_constantCoeff_zero hc')]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [ih, show (subst (fun k => (X k : MvPowerSeries (Fin d) E)) f) = f from
      congrFun (subst_self (R := E) (σ := Fin d)) f]
    push_cast
    rw [add_smul, one_smul]

theorem lie_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), c.IsLie f l →
    (In (⊤ : Ideal O) f → constantCoeff f = 0 → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ O E _ _ _ hF G d c f l hl
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  unfold Chart.IsLie at hl
  have key : (∀ n, ∃ s : MvPowerSeries (Fin d) O, MvPowerSeries.map (algebraMap O E) s =
      defect c.μ (p ^ n) f ∧ ∃ z, c.ev n s = (p : O) ^ n • z) → l = 0 := by
    intro H
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    refine eq_zero_of_pow_dvd (p := (p : O)) _ fun n => ?_
    obtain ⟨s, hs, z, hz⟩ := H n
    obtain ⟨φ, hφ⟩ := (T.dvd_of_forall_invariantDifferential_dvd p O G n 1 0 (fun _ _ _ => one_dvd _)).2 w
    have h1 := hl.2 n w φ s hφ hs
    have h2 : (p : O) ^ n ∣ φ (c.ev n s) := by
      rw [hz]
      simp
    simpa using dvd_add h1 h2
  refine ⟨fun hIn hc0 => key fun n => ?_, fun hcob => key fun n => ?_⟩
  · choose g hg using hIn
    let s0 : MvPowerSeries (Fin d) O := fun α => g α
    have hs0 : MvPowerSeries.map (algebraMap O E) s0 = f := by
      ext α
      rw [coeff_map, (hg α).2]
      rfl
    have hc : constantCoeff s0 = 0 := by
      apply hF.inj
      rw [map_zero, ← constantCoeff_map, hs0, hc0]
    have hsub : HasSubst (nmul c.μ (p ^ n)) :=
      hasSubst_of_constantCoeff_zero (constantCoeff_nmul c.μ c.isLaw.const _)
    refine ⟨(p ^ n) • s0 - subst (nmul c.μ (p ^ n)) s0, ?_, c.ev n s0, ?_⟩
    · rw [map_sub, map_nsmul, map_subst hsub, hs0]
      unfold defect
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    · rw [map_sub, map_nsmul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).1 s0, hc, map_zero, sub_zero,
        ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  · refine ⟨0, ?_, 0, ?_⟩
    · unfold defect
      rw [subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hcob, sub_self, map_zero]
    · simp

end GlobalTheory.LieZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoordsNonunit
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TangentIndep

theorem subst_nmul_eq (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := _root_.GlobalTheory.QLog.subst_nmul_eq R d μ hμ g n

theorem up_nmul_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up S (nmul μ n) = nmul (up S μ) n := _root_.GlobalTheory.QLog.up_nmul R S d μ hμ n

theorem map_at2_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := _root_.GlobalTheory.QLog.map_algebraMap_powerSeriesEvalTwoGroups R S d τ t u v hu hv

theorem constantCoeff_subst_eq (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries σ R) :
    constantCoeff (subst a g) = constantCoeff g := _root_.GlobalTheory.constantCoeff_subst_of_constantCoeff_zero R σ τ a ha g

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (ht : ∀ α, coeff α t ∈ I) (α : τ →₀ ℕ) : coeff α (at2 t u v) ∈ I := _root_.GlobalTheory.IdealAt2.coeff_powerSeriesEvalTwoGroups_mem_ideal R d τ I t u v hu hv ht α

theorem ev_mem_smul_add (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) (hh : ∀ α, coeff α h ∈ I) :
    ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n, c.ev n h = a + (p : G.A n) * b := _root_.GlobalTheory.Chart.ev_mem_ideal_smul_add_p p O G d c n I h hh

theorem ev_subst_nmul (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n k : ℕ) (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := _root_.GlobalTheory.EvMul.ev_subst_nmul p O G d c n k h

theorem repr_mem_maximalIdeal (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M))
    (l : Module.Dual O M) (hl : ∀ w, l w ∈ IsLocalRing.maximalIdeal O) (j : Fin k) :
    lb.repr l j ∈ IsLocalRing.maximalIdeal O := _root_.GlobalTheory.dualBasis_coord_mem_maximalIdeal O M k lb l hl j

theorem nmul_const (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]; rw [Function.iterate_succ_apply']
    rw [h, op, at2, constantCoeff_subst_eq R _ _ _ (fun x => by cases x with | inl a => exact ih a | inr a => simp), hμ]

theorem powerSeriesEvalTwoGroups_add (R : Type) [CommRing R] (d : ℕ) (τ : Type) (a b : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (a + b) u v = at2 a u v + at2 b u v := by
  unfold at2
  exact subst_add (hasSubst_of_constantCoeff_zero fun x => by cases x with | inl i => exact hu i | inr i => exact hv i) a b

theorem constantCoeff_formalGroupLawCoboundaryOne (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) :
    constantCoeff (cob1 μ g) = - constantCoeff g := by
  simp only [cob1, inL, inR, map_sub]
  rw [constantCoeff_subst_eq R _ _ _ hμ, constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _), constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _)]
  ring

theorem QL_comb (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) E) (a : O) (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) :
    QL μ ⊤ (f + algebraMap O E a • g) := by
  have hμE : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by simp [up, hμ]
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · simp [hf.1, hg.1]
  · obtain ⟨x, -, hx⟩ := hf.2.1 i
    obtain ⟨y, -, hy⟩ := hg.2.1 i
    refine ⟨x + a * y, trivial, ?_⟩
    simp only [lin] at hx hy ⊢
    rw [map_add, coeff_smul, hx, hy, map_add, map_mul]
  · obtain ⟨x, -, hx⟩ := hf.2.2 α
    obtain ⟨y, -, hy⟩ := hg.2.2 α
    refine ⟨x + a * y, trivial, ?_⟩
    rw [formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add, coeff_smul, hx, hy, map_add, map_mul]

theorem tangent_coords_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  intro p _ K _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQL hLie hlog b s hH j
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o := fun o => IsLocalRing.mem_maximalIdeal o
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := (hmem _).2 Fact.out
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  let f := comb (Sum.elim 0 b) e
  let l : G.dual.Lie := ∑ j, b j • lb j
  have lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' →
      QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
    fun f g l l' a hf hg => (_root_.GlobalTheory.LieLin.main p K v O hv G d c E hF f g l l' a hf hg).1
  have h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
    have := lin _ _ _ _ (-1) (hLie j) (hLie j) (hQL _) (hQL _)
    simpa using this
  have hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simpa using h00⟩
      simpa using QL_comb O E d c.μ hμ _ _ (-1) (hQL (Sum.inr j)) (hQL (Sum.inr j))
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]
      exact ⟨QL_comb O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩
  have hf_eq : f = ∑ i, algebraMap O E (b i) • e (Sum.inr i) := by
    simp [f, comb, Fintype.sum_sum_type]
  have hfl : c.IsLie f l := by rw [hf_eq]; exact (hsum Finset.univ).2

  have hμE : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by simp [up, hμ]
  choose t ht using hH
  let T : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => t α
  have hT : ∀ α, coeff α T = t α := fun α => rfl
  have hcob : cob1 (up E c.μ) f = map (algebraMap O E) (cob1 c.μ s + T) := by
    ext α
    have h := (ht α).2
    rw [map_sub, sub_eq_iff_eq_add] at h
    rw [map_add, map_add, h]
    simp only [coeff_map, hT]
    ring
  have hf0 : constantCoeff f = algebraMap O E (constantCoeff s - t 0) := by
    have h := (ht 0).2
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_formalGroupLawCoboundaryOne E d _ hμE, constantCoeff_map,
      constantCoeff_formalGroupLawCoboundaryOne O d _ hμ] at h
    rw [map_sub, ← h, map_neg]; ring
  have hnc := nmul_const O d c.μ hμ
  let s' : MvPowerSeries (Fin d) O := -C (constantCoeff s - t 0) -
    ∑ k ∈ Finset.range p, at2 (cob1 c.μ s + T) (nmul c.μ k) (fun i => X i)
  have hX : up E (fun i : Fin d => (X i : MvPowerSeries (Fin d) O)) = fun i => X i := by
    funext i; simp [up, map_X]
  have hs' : map (algebraMap O E) s' = defect c.μ (p ^ 1) f := by
    rw [defect, pow_one, up_nmul_eq O E d c.μ hμ, subst_nmul_eq E d _ hμE f p, hcob, hf0]
    simp only [s', map_sub, map_neg, map_sum, map_C]
    rw [Finset.sum_congr rfl (fun k _ => map_at2_eq O E d (Fin d) _ _ _ (hnc k) (fun i => constantCoeff_X i))]
    simp only [hX, up_nmul_eq O E d c.μ hμ]
    abel
  have hs'2 : s' = C (t 0) + (p : O) • s - subst (nmul c.μ p) s -
      ∑ k ∈ Finset.range p, at2 T (nmul c.μ k) (fun i => X i) := by
    rw [subst_nmul_eq O d c.μ hμ s p]
    simp only [s']
    rw [Finset.sum_congr rfl (fun k _ => powerSeriesEvalTwoGroups_add O d (Fin d) _ _ _ _ (hnc k) (fun i => constantCoeff_X i)),
      Finset.sum_add_distrib, map_sub]
    abel
  have key : ∀ w : G.dual.omega, l w ∈ IsLocalRing.maximalIdeal O := by
    intro w
    obtain ⟨φ₀, hφ₀⟩ := AugCot.d_surjective _ (w.1 1)
    set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef
    have hφd : PDiv.dUnit O φ = w.1 1 := by
      rw [hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact hφ₀
    have hφ1 : φ 1 = 0 := by
      rw [hφdef]
      simp [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]

    have hL := hfl.2 1 w φ s' hφd hs'
    have hA : ∀ r : O, φ (algebraMap O (G.A 1) r) = 0 := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ1, smul_zero]
    have hev : φ (c.ev 1 s') ∈ IsLocalRing.maximalIdeal O := by
      have h1 := G.mulBy_pow_self 1 (c.ev 1 s)
      rw [pow_one] at h1
      have hC : c.ev 1 (C (t 0)) = algebraMap O _ (t 0) := (c.ev 1).commutes (t 0)
      rw [hs'2]
      simp only [map_sub, map_add, map_smul, map_sum, ev_subst_nmul p O G d c 1 p s, h1, hC]
      have hA' : ∀ r : O, φ.ofConv (algebraMap O (G.A 1) r) = 0 := hA
      rw [hA', hA', zero_add, sub_zero, smul_eq_mul]
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hpm) (Ideal.sum_mem _ fun k _ => ?_)
      obtain ⟨a, ha, b', hb'⟩ := ev_mem_smul_add p O G d c 1 (IsLocalRing.maximalIdeal O) _
        (coeff_powerSeriesEvalTwoGroups_mem_ideal O d (Fin d) _ T _ _ (hnc k) (fun i => constantCoeff_X i) (fun α => (hmem _).2 (ht α).1))
      rw [hb', map_add]
      refine Ideal.add_mem _ ?_ ?_
      · have hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤
            Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O) :=
          Submodule.smul_le.2 fun r hr x _ => by
            rw [Submodule.mem_comap, map_smul, smul_eq_mul]
            exact Ideal.mul_mem_right _ _ hr
        exact hle ha
      · rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
        exact Ideal.mul_mem_right _ _ hpm
    obtain ⟨q, hq⟩ := hL
    have : l w = (p : O) ^ 1 * q + φ (c.ev 1 s') := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hev
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p K v O hv G.dual
  have h6 := repr_mem_maximalIdeal O G.dual.omega k lb l key j
  have hrep : lb.repr l j = b j := by
    have : l = lb.equivFun.symm b := by rw [Module.Basis.equivFun_symm_apply]
    rw [← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [hrep] at h6
  exact (hmem _).1 h6

end GlobalTheory.TangentIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_shear : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {g : ℕ} (h : (I → ℂ) × (Fin g → ℂ) → ℂ) (τ : (I → ℂ) → Fin g → ℂ) (w : Fin g → ℂ), AnalyticAt ℂ τ 0 → AnalyticAt ℂ h (0, w + τ 0) → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (z, w + τ z)) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun a ↦ GlobalTheory.PeriodFamily.taylor N t (fun z ↦ τ z a) - algebraMap ℂ D (τ 0 a)) (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) := by
  intro I _ _ D _ _ N t ht g h τ w hτ hh
  have hτa : ∀ a, AnalyticAt ℂ (fun z ↦ τ z a) 0 := fun a ↦ analyticAt_pi_iff.1 hτ a
  have hco : ∀ {J : Type} [Fintype J] (j : J) (x : J → ℂ), AnalyticAt ℂ (fun z : J → ℂ ↦ z j) x :=
    fun j x ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) j).analyticAt x
  have hΦ : AnalyticAt ℂ (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 := by
    refine analyticAt_pi_iff.2 ?_
    rintro (i | a)
    · exact hco i 0
    · exact (hτa a).sub analyticAt_const
  have hΦ0 : (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 = 0 := by
    funext k
    rcases k with i | a <;> simp
  have hH : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) 0 := by
    have hin : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
        ((fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)) : (I → ℂ) × (Fin g → ℂ))) 0 := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ hco _ 0) ?_
      refine analyticAt_pi_iff.2 fun a ↦ ?_
      exact (analyticAt_const (v := (w + τ 0) a)).add (hco (Sum.inr a) 0)
    refine AnalyticAt.comp_of_eq hh hin ?_
    ext <;> simp
  have key := GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt N t ht _ _ hΦ hΦ0 hH
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have e1 : (fun z : I → ℂ ↦ h (z, w + τ z)) = fun z : I → ℂ ↦
      (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)))
        (Sum.elim z (fun a ↦ τ z a - τ 0 a)) := by
    funext z
    congr 1
    ext <;> simp
  rw [e1, key]
  congr 1
  funext k
  rcases k with i | a
  · exact (GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero N t ht).1 i
  · have := hadd (fun z ↦ τ z a) (fun _ ↦ - τ 0 a) (hτa a) analyticAt_const
    rw [hconst, map_neg] at this
    simpa [sub_eq_add_neg] using this

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoCubeMulDerivWeierstrassPNegTwo
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem tendsto_cube_mul_derivWeierstrassP (L : PeriodPair) :
    Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  have hw : ContinuousAt (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 := by
    have := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
    fun_prop
  have h1 : Filter.Tendsto (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) (𝓝[≠] 0)
      (𝓝 (-2)) := by
    have := hw.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  have h := L.derivWeierstrassPExcept_sub 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [← h]
  field_simp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionWeierstrassPMemValuationSubring
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.TorsMemVal

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

theorem main : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  intro L β u V N hβ hβi hu hN z w hz hw hNz hNw
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have huΩ : V.valuation u = V.valuation Ω := by
    rw [← hΩ, map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have h := GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0
  exact ⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2),
    mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩

end GlobalTheory.CMModel.TorsMemVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPAddSubWeierstrassPSubStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_sub_sq_mul_add_sub_eq_neg_deriv_mul : ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z - w ∉ L.lattice → z + w ∉ L.lattice → (L.weierstrassP z - L.weierstrassP w) ^ 2 * (L.weierstrassP (z + w) - L.weierstrassP (z - w)) = -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by
  first | exact @GlobalTheory.weierstrassP_add_sub_weierstrassP_sub | exact GlobalTheory.weierstrassP_add_sub_weierstrassP_sub | (intros; apply GlobalTheory.weierstrassP_add_sub_weierstrassP_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSqStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq : ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice → L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 - 2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  first | exact @GlobalTheory.weierstrassP_two_mul_mul_sq | exact GlobalTheory.weierstrassP_two_mul_mul_sq | (intros; apply GlobalTheory.weierstrassP_two_mul_mul_sq <;> assumption)
end

