import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogEqSumLinearCoefficientsFormExplicit
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

open GlobalTheory.PDiv

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

theorem exists_eq_add_single {α : Fin d →₀ ℕ} (h : α ≠ 0) :
    ∃ (i : Fin d) (β : Fin d →₀ ℕ), α = β + Finsupp.single i 1 ∧ α.degree = β.degree + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hle : Finsupp.single i 1 ≤ α := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  refine ⟨i, α - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  conv_lhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

variable (c : Chart G d)

theorem counit_ev_monomial (n : ℕ) {β : Fin d →₀ ℕ} (hβ : β ≠ 0) (a : O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n (monomial β a)) = 0 := by
  obtain ⟨i, γ, rfl, -⟩ := exists_eq_add_single hβ
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, map_mul]
  change _ * Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, mul_zero]

theorem dUnit_ev_monomial (n : ℕ) {α : Fin d →₀ ℕ} (hα : 2 ≤ α.degree) (a : O) :
    dUnit O (c.ev n (monomial α a)) = 0 := by
  have h0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single h0
  have hβ : β ≠ 0 := by
    have hb : β.degree ≠ 0 := by omega
    exact fun h => hb (by rw [h]; simp)
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, dUnit, AugCot.d_mul,
    c.counit_ev_monomial n hβ]
  change _ • _ + Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) • _ = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, zero_smul, zero_smul, add_zero]

theorem dUnit_ev_of_high (n N : ℕ) (hN : ∀ f : MvPowerSeries (Fin d) O,
    (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → (p : G.A n) ^ n ∣ c.ev n f)
    (f : MvPowerSeries (Fin d) O) (hf : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) :
    dUnit O (c.ev n f) = 0 := by
  obtain ⟨b, hb⟩ := hN f hf
  rw [hb, dUnit, AugCot.d_mul]
  have h1 : ((p : G.A n) ^ n) = algebraMap O (G.A n) ((p : O) ^ n) := by simp
  rw [h1, AugCot.d_algebraMap, smul_zero, add_zero, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact G.pow_smul_cot n _

theorem dUnit_ev_of_two (n : ℕ) (f : MvPowerSeries (Fin d) O)
    (hf : ∀ α : Fin d →₀ ℕ, α.degree ≤ 1 → coeff α f = 0) : dUnit O (c.ev n f) = 0 := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  classical
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) f with hP
  have hsplit : f = (P : MvPowerSeries (Fin d) O) + (f - P) := by ring
  rw [hsplit, map_add, dUnit, map_add, ← dUnit, ← dUnit]
  rw [c.dUnit_ev_of_high n N hN (f - P) fun α hα => ?_, add_zero]
  · rw [MvPolynomial.as_sum P]
    have : ((∑ v ∈ P.support, MvPolynomial.monomial v (MvPolynomial.coeff v P) :
        MvPolynomial (Fin d) O) : MvPowerSeries (Fin d) O) =
        ∑ v ∈ P.support, monomial v (MvPolynomial.coeff v P) := by
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
    rw [this, map_sum, dUnit, map_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv' : MvPolynomial.coeff v P ≠ 0 := MvPolynomial.mem_support_iff.1 hv
    have h2 : 2 ≤ v.degree := by
      by_contra hc
      apply hv'
      rw [hP, coeff_trunc']
      split_ifs
      · exact hf v (by omega)
      · rfl
    exact c.dUnit_ev_monomial n h2 _
  · rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro j
    exact ((Finsupp.le_degree j α).trans hα.le)

theorem dlog_eq_sum_lin [Fact p.Prime] (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O)
    (h1 : constantCoeff u = 1) (hu : ∀ n, c.ev n u = charElem χ n) :
    dlog G χ = ∑ i, lin u i • c.form i := by
  classical
  apply Subtype.ext
  funext n
  rw [Submodule.coe_sum, Finset.sum_apply, dlog_val, ← hu n]
  simp only [Submodule.coe_smul, Pi.smul_apply]
  set g : MvPowerSeries (Fin d) O := ∑ i, lin u i • X i with hg
  have hsplit : u = 1 + g + (u - 1 - g) := by ring
  have hev : c.ev n g = ∑ i, lin u i • c.x n i := by
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, (c.isEval n).1 i]
  have e1 : dUnit O (c.ev n u) = dUnit O (c.ev n 1) + dUnit O (c.ev n g) +
      dUnit O (c.ev n (u - 1 - g)) := by
    conv_lhs => rw [hsplit]
    simp only [PDiv.dUnit, map_add]
  rw [e1, c.dUnit_ev_of_two n (u - 1 - g) ?_, add_zero, map_one, hev]
  · simp only [PDiv.dUnit, AugCot.d_one, zero_add, map_sum, map_smul]
    rfl
  intro α hα
  have hcg : ∀ i, coeff (Finsupp.single i 1) g = lin u i := fun i => by
    rw [hg, map_sum]
    simp only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1'
  · rw [(Finsupp.degree_eq_zero_iff α).1 h0]
    have hg0 : coeff 0 g = 0 := by
      rw [hg, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_X, if_neg, smul_zero]
      intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this
    rw [map_sub, map_sub, hg0, coeff_zero_eq_constantCoeff_apply, h1,
      coeff_zero_eq_constantCoeff_apply, map_one]
    ring
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h1'
    obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single hne
    have hβ : β = 0 := (Finsupp.degree_eq_zero_iff β).1 (by omega)
    subst hβ
    rw [zero_add, map_sub, map_sub, hcg, coeff_one, if_neg, sub_zero]
    · exact sub_self _
    · intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem dlog_eq_sum_lin' : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i :=
  fun _ _ _ _ _ _ _ _ c χ u h1 hu => c.dlog_eq_sum_lin χ u h1 hu

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_eq_smul_of_forall_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) →
      ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  intro O M _ _ _ a ha l hl
  have cancel : ∀ x y : O, a * x = a * y → x = y := by
    intro x y hxy
    have := ha (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  let c : M → O := fun w => Classical.choose (hl w)
  have hc : ∀ w, l w = a * c w := fun w => Classical.choose_spec (hl w)
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply cancel
    rw [mul_add, ← hc, ← hc, ← hc, map_add]
  · intro r x
    apply cancel
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hc, map_smul, hc, smul_eq_mul]
    ring
  · ext w
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    exact hc w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualQuotientFormEqEval
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_quotient_form_eq_eval :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
      [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I),
      ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  intro O M _ _ _ _ _ I u
  obtain ⟨v, hv⟩ := Module.projective_lifting_property (Submodule.mkQ I) u
    (Submodule.mkQ_surjective I)
  refine ⟨(Module.evalEquiv O M).symm v, fun φ => ?_⟩
  have h1 : φ ((Module.evalEquiv O M).symm v) = v φ := by
    have := congrArg (fun w : Module.Dual O (Module.Dual O M) => w φ)
      ((Module.evalEquiv O M).apply_symm_apply v)
    simpa using this
  rw [h1, ← hv]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphismStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_schur_endomorphism : GlobalTheory.LeviCut.NablaSchur := by
  first | exact @GlobalTheory.LeviCut.nablaSchur | exact GlobalTheory.LeviCut.nablaSchur | (intros; apply GlobalTheory.LeviCut.nablaSchur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdSubOfDUnitEq
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CotDualLin

theorem dvd_counit (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t) :
    q ∣ Coalgebra.counit (R := O) a := by
  have h1 := CartierDual.mul_apply (R := O) (C := A) 1 1 a
  rw [one_mul, h] at h1
  simp only [map_add, map_smul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, Bialgebra.counit_one] at h1
  exact ⟨-(CartierDual.pair O A A (1 ⊗ₜ 1) t), by rw [smul_eq_mul] at h1; linear_combination -h1⟩

theorem dvd_of_mem_sq (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t)
    (χ : CartierDual O A) (hχ : χ ∈ RingHom.ker (Bialgebra.counitAlgHom O (CartierDual O A)) ^ 2) :
    q ∣ χ a := by
  rw [pow_two] at hχ
  refine Submodule.mul_induction_on hχ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx1 : x 1 = 0 := hx
    have hy1 : y 1 = 0 := hy
    rw [CartierDual.mul_apply, h]
    simp only [map_add, map_smul, CartierDual.pair_tmul_tmul, hx1, hy1, mul_zero, zero_mul, zero_add, smul_eq_mul]
    exact dvd_mul_right _ _
  · have e : (x + y) a = x a + y a := rfl
    rw [e]; exact dvd_add hx hy

theorem dvd_sub_of_dUnit_eq : ∀ (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A),
    Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t →
    ∀ φ ψ : CartierDual O A, PDiv.dUnit O φ = PDiv.dUnit O ψ → q ∣ φ a - ψ a := by
  intro O A _ _ _ _ _ _ a q t h φ ψ hd
  have h0 : PDiv.dUnit O (φ - ψ) = 0 := by rw [PDiv.dUnit, map_sub]; exact sub_eq_zero.2 hd
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff] at h0
  have h2 := dvd_of_mem_sq O A a q t h _ h0
  set c := Bialgebra.counitAlgHom O (CartierDual O A) (φ - ψ)
  have h3 : (algebraMap O (CartierDual O A) c) a = c * Coalgebra.counit (R := O) a := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  have e : (φ - ψ - algebraMap O (CartierDual O A) c) a = φ a - ψ a - (algebraMap O (CartierDual O A) c) a := rfl
  rw [e, h3] at h2
  have h4 := dvd_mul_of_dvd_right (dvd_counit O A a q t h) c
  have := dvd_add h2 h4
  rwa [sub_add_cancel] at this

end GlobalTheory.CotDualLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem effCartier_comap_of_isIso_restrict : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  intro Y Y' s I U hiso hE
  have h1 : FinalTheorems.EffCartier ((I.comap s).comap (s ⁻¹ᵁ U).ι) :=
    effCartier_comap_of_isOpenImmersion' _ _ hE
  have h2 := effCartier_comap_of_isOpenImmersion' _ (inv (s ∣_ U)) h1
  have key : inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι ≫ s = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, key] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_unique_quotAut {O M G : Type*} [Ring O] [AddCommGroup M] [Module O M] [Group G]
    (W : Submodule O M) (act : O → G → G) (L L' : M → G)
    (hadd : ∀ a b, L (a + b) = L a * L b) (hadd' : ∀ a b, L' (a + b) = L' a * L' b)
    (hsm : ∀ (c : O) a, L (c • a) = act c (L a)) (hsm' : ∀ (c : O) a, L' (c • a) = act c (L' a))
    (hker : ∀ a, L a = 1 ↔ a ∈ W) (hker' : ∀ a, L' a = 1 ↔ a ∈ W)
    (hsurj : ∀ a, ∃ b, L b = L' a) (hsurj' : ∀ a, ∃ b, L' b = L a) :
    ∃! g : (M ⧸ W) ≃ₗ[O] (M ⧸ W),
      ∀ y, L (Function.surjInv (Submodule.mkQ_surjective W) (g (W.mkQ y))) = L' y := by
  have key : ∀ {L : M → G}, (∀ a b, L (a + b) = L a * L b) → (∀ a, L a = 1 ↔ a ∈ W) →
      ∀ a b, L a = L b ↔ W.mkQ a = W.mkQ b := by
    intro L hadd hker a b
    have h : L a = L (a - b) * L b := by rw [← hadd, sub_add_cancel]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, h]
    constructor
    · intro e
      exact mul_right_cancel (e.trans (_root_.one_mul _).symm)
    · intro e
      rw [e, _root_.one_mul]
  have eq := key hadd hker
  choose z hz using hsurj
  let f₀ : M →ₗ[O] M ⧸ W :=
    { toFun := fun y => W.mkQ (z y)
      map_add' := fun a b => by
        rw [← map_add, ← eq, hadd, hz, hz, hz, hadd']
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← LinearMap.map_smul, ← eq, hsm, hz, hz, hsm'] }
  have hf₀ : W ≤ LinearMap.ker f₀ := by
    intro y hy
    rw [LinearMap.mem_ker]
    show W.mkQ (z y) = 0
    rw [← map_zero W.mkQ, ← eq, hz, (hker' y).2 hy, (hker 0).2 W.zero_mem]
  let f := W.liftQ f₀ hf₀
  have hf : ∀ y, f (W.mkQ y) = W.mkQ (z y) := fun y => rfl
  have bij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨y, rfl⟩ := W.mkQ_surjective q
      rw [hf, ← map_zero W.mkQ, ← eq, hz, (hker 0).2 W.zero_mem, hker'] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hq
    · intro q
      obtain ⟨a, rfl⟩ := W.mkQ_surjective q
      obtain ⟨y, hy⟩ := hsurj' a
      exact ⟨W.mkQ y, by rw [hf, ← eq, hz, hy]⟩
  refine ⟨LinearEquiv.ofBijective f bij, ?_, ?_⟩
  · intro y
    rw [← hz y, eq, Function.surjInv_eq (Submodule.mkQ_surjective W)]
    rfl
  · intro g hg
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := W.mkQ_surjective q
    rw [LinearEquiv.ofBijective_apply, hf, ← Function.surjInv_eq (Submodule.mkQ_surjective W) (g (W.mkQ y)),
      ← eq, hg y, hz]

theorem etLev_rel_existsUnique (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)) :
    IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  intro hl hl'
  obtain ⟨hinj, hsur⟩ := hl.2.2.2 k (𝟙 _)
  obtain ⟨hinj', hsur'⟩ := hl'.2.2.2 k (𝟙 _)
  have canc : ∀ u v : Over.mk x ⟶ o.A,
      (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ u =
        (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ v → u = v := by
    intro u v h
    ext
    have := congrArg CommaMorphism.left h
    simpa using this
  have killed : ∀ (l₁ : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l₁ → ∀ a, ∀ c ∈ w0 ^ r,
      ((Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ l₁ a) ≫
        o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro l₁ h₁ a c hc
    rw [Category.assoc, ← h₁.2.1, h₁.2.2.1 _ (Submodule.subset_span ⟨c, hc, a, rfl⟩), comp_one]
  exact exists_unique_quotAut (wSub D w0 r) (fun c g => g ≫ o.act.act c) l l' hl.1 hl'.1 hl.2.1 hl'.2.1
    (fun a => ⟨fun h => hinj a (by rw [h, comp_one]), fun h => hl.2.2.1 a h⟩)
    (fun a => ⟨fun h => hinj' a (by rw [h, comp_one]), fun h => hl'.2.2.1 a h⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur _ (killed l' hl' a)
      exact ⟨y, canc _ _ hy⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur' _ (killed l hl a)
      exact ⟨y, canc _ _ hy⟩)

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.RingContH.main
  | exact GlobalTheory.EtC.RingContH.main
  | (intros; apply GlobalTheory.EtC.RingContH.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  first | (exact @GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (exact GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (intros; apply GlobalTheory.etale_isFinite_of_comp_etale_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorph
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_isLocalHomeomorph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → IsLocalHomeomorph (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE
  apply IsLocalHomeomorph.mk
  intro y
  set i := A.pick y
  set e := A.chart i
  set S : Set (V n) := e.target ∩ e.symm ⁻¹' U with hSdef
  have hS : IsOpen S := e.isOpen_inter_preimage_symm hE.isOpen
  have hyU : (y : Y) ∈ U := y.2
  have hys : (y : Y) ∈ e.source := A.mem_pick y
  have hxS : e y ∈ S := ⟨e.map_source hys, by simp [e.left_inv hys, hyU]⟩
  have hd : DifferentiableOn ℂ (z ∘ e.symm) S := hE.holo i
  have hcd : ContDiffOn ℂ ∞ (z ∘ e.symm) S :=
    contDiffOn_piLp' 2 (fun k => contDiffOn_of_differentiableOn n _ S hS
      ((differentiableOn_piLp 2).1 hd k))
  have hca : ContDiffAt ℂ ∞ (z ∘ e.symm) (e y) := hcd.contDiffAt (hS.mem_nhds hxS)
  have hst := hca.hasStrictFDerivAt (by simp)
  have hdet : (fderiv ℂ (z ∘ e.symm) (e y)).det ≠ 0 := hE.det_ne i y hyU hys
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero ((fderiv ℂ (z ∘ e.symm) (e y)) : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hL : ((L : V n →L[ℂ] V n)) = fderiv ℂ (z ∘ e.symm) (e y) := by
    ext v; rfl
  have hst' : HasStrictFDerivAt (z ∘ e.symm) (L : V n →L[ℂ] V n) (e y) := hL ▸ hst
  let h := hst'.toOpenPartialHomeomorph (z ∘ e.symm)
  let P := e.trans (h.restrOpen S hS)
  have hyP : (y : Y) ∈ P.source := by
    simp only [P, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hys, hst'.mem_toOpenPartialHomeomorph_source, hxS⟩
  have hPz : ∀ w ∈ P.source, P w = z w := by
    intro w hw
    have hw1 : w ∈ e.source := by
      simp only [P, OpenPartialHomeomorph.trans_source] at hw; exact hw.1
    have hh : ∀ v, h v = (z ∘ e.symm) v := fun v => by
      simp only [h, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    change (h.restrOpen S hS) (e w) = z w
    change h (e w) = z w
    rw [hh, Function.comp_apply, e.left_inv hw1]
  have hne : Nonempty (⟨U, hE.isOpen⟩ : TopologicalSpace.Opens Y) := ⟨y⟩
  let Q := P.subtypeRestr hne
  refine ⟨Q, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hyP
  · intro w hw
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hw
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    exact (hPz w hw).symm

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  intro p _ D R _ b N S s o w0 r T T' l f h
  obtain ⟨hadd, hlin, hker, hgeo⟩ := h
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ?_⟩
  · simp only [hadd, MonObj.comp_mul]
  · simp only [hlin, Category.assoc]
  · simp only [hker x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hgeo k (x ≫ f.left)
    let e : Over.mk (x ≫ T'.hom) ≅ Over.mk ((x ≫ f.left) ≫ T.hom) :=
      Over.isoMk (Iso.refl _) (by simp [Over.w f])
    have hfac : (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ f =
        e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) := by
      ext; simp [e]
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h1 : e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) ≫ l y = 1 := by
        rw [← Category.assoc, ← hfac, Category.assoc]; exact hy
      have h2 := congrArg (fun z => e.inv ≫ z) h1
      simpa [MonObj.comp_one] using h2
    · obtain ⟨y, hy⟩ := hsurj (e.inv ≫ g) (fun c hc => by
        exact (Category.assoc _ _ _).trans (by rw [hg c hc, MonObj.comp_one]))
      refine ⟨y, ?_⟩
      rw [← Category.assoc, hfac, Category.assoc, hy, Iso.hom_inv_id_assoc]

end GlobalTheory.UPel.HT.EtLev
end

