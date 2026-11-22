import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValResultantCharpolyShiftedUnitAdjoinRoot
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.UnitLemma.ShiftRes

def shiftPoly {F : Type} [Field F] (t s : F) (p : F[X]) : F[X] :=
  C (t ^ p.natDegree)⁻¹ * p.comp (C t * X + C s)

theorem natDegree_lin {F : Type} [Field F] (t s : F) (ht : t ≠ 0) : (C t * X + C s).natDegree = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X t ht]

theorem natDegree_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) :
    (shiftPoly t s p).natDegree = p.natDegree := by
  unfold shiftPoly
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ht)), natDegree_comp, natDegree_lin t s ht, mul_one]

theorem monic_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Monic) :
    (shiftPoly t s p).Monic := by
  unfold shiftPoly Monic
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [natDegree_lin t s ht]; exact one_ne_zero),
    hp.leadingCoeff, one_mul]
  have : (C t * X + C s).leadingCoeff = t := by
    rw [leadingCoeff, natDegree_lin t s ht]; simp
  rw [this, inv_mul_cancel₀ (pow_ne_zero _ ht)]

theorem map_shiftPoly {F L : Type} [Field F] [Field L] (φ : F →+* L) (t s : F) (p : F[X]) :
    (shiftPoly t s p).map φ = shiftPoly (φ t) (φ s) (p.map φ) := by
  unfold shiftPoly
  rw [Polynomial.map_mul, map_C, Polynomial.map_comp, natDegree_map]
  simp

theorem shiftPoly_mul {F : Type} [Field F] (t s : F) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    shiftPoly t s (p * q) = shiftPoly t s p * shiftPoly t s q := by
  unfold shiftPoly
  rw [hp.natDegree_mul hq, mul_comp, pow_add, mul_inv, C_mul]
  ring

theorem shiftPoly_eq_prod {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p : L[X]) (hp : p.Monic) :
    shiftPoly t s p = ((p.roots.map fun α => (α - s) / t).map fun a => X - C a).prod := by
  have hsp := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = p.natDegree := hsp.natDegree_eq_card_roots.symm
  unfold shiftPoly
  conv_lhs => arg 2; rw [hsp.eq_prod_roots_of_monic hp]
  rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  have key : ∀ α : L, (X - C α).comp (C t * X + C s) = C t * (X - C ((α - s) / t)) := by
    intro α
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ ht, C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard, ← C_pow, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (pow_ne_zero _ ht), C_1, one_mul]

theorem resultant_shiftPoly_alg {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p q : L[X])
    (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  have hcp : Multiset.card p.roots = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hcq : Multiset.card q.roots = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  rw [resultant_eq_prod_roots_sub _ _ (monic_shiftPoly t s ht p hp) (monic_shiftPoly t s ht q hq)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _), resultant_eq_prod_roots_sub p q hp hq (IsAlgClosed.splits p)
    (IsAlgClosed.splits q), shiftPoly_eq_prod t s ht p hp, shiftPoly_eq_prod t s ht q hq,
    roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C, Multiset.prod_map_product_eq_prod_prod,
    Multiset.prod_map_product_eq_prod_prod]
  simp only [Multiset.map_map, Function.comp_def]
  have key : ∀ α β : L, (α - s) / t - (β - s) / t = t⁻¹ * (α - β) := by
    intro α β; field_simp; ring
  simp only [key]
  simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcq]
  rw [hcp, ← pow_mul, inv_pow, mul_comm q.natDegree p.natDegree]

theorem resultant_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  let φ := algebraMap F (AlgebraicClosure F)
  apply φ.injective
  have e1 : φ (resultant (shiftPoly t s p) (shiftPoly t s q)) =
      resultant ((shiftPoly t s p).map φ) ((shiftPoly t s q).map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  have e2 : φ (resultant p q) = resultant (p.map φ) (q.map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  rw [e1, map_mul, e2, map_shiftPoly, map_shiftPoly,
    resultant_shiftPoly_alg _ _ ((_root_.map_ne_zero φ).2 ht) _ _ (hp.map φ) (hq.map φ), natDegree_map, natDegree_map,
    map_inv₀, map_pow]

theorem separable_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Separable) :
    (shiftPoly t s p).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (C t * X + C s))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (C t * X + C s)) (C t) :=
    ⟨0, C t⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ ht, C_1]⟩
  have h3 : derivative (p.comp (C t * X + C s)) = (derivative p).comp (C t * X + C s) * C t := by
    rw [derivative_comp, derivative_add, derivative_C_mul_X, derivative_C, add_zero, mul_comm]
  have hc : (p.comp (C t * X + C s)).Separable := by
    show IsCoprime _ _
    rw [h3]
    exact h1.mul_right h2
  unfold shiftPoly
  have hu : IsUnit (C (t ^ p.natDegree)⁻¹ : F[X]) := isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  show IsCoprime _ _
  rw [derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hc

theorem charpoly_eq_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] (x : A)
    (hx : Algebra.adjoin F ({x} : Set A) = ⊤) (p : F[X]) (hp : p.Monic) (hpx : aeval x p = 0)
    (hd : p.natDegree = Module.finrank F A) : (LinearMap.mulLeft F x).charpoly = p := by
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have hCH : aeval x (LinearMap.mulLeft F x).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F x)
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul F A) x (LinearMap.mulLeft F x).charpoly
    have h3 : (Algebra.lmul F A) (aeval x (LinearMap.mulLeft F x).charpoly) = 0 := by rw [← h2]; exact h
    simpa using congrArg (fun f => f 1) h3
  have hcd : (LinearMap.mulLeft F x).charpoly.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree _
  have hle : Module.finrank F A ≤ (minpoly F x).natDegree := by
    let pb := AdjoinRoot.powerBasis' hmon
    haveI : Module.Finite F (AdjoinRoot (minpoly F x)) := pb.finite
    let f := AdjoinRoot.liftAlgHom (minpoly F x) (Algebra.ofId F A) x
      (by rw [← minpoly.aeval F x, aeval_def]; rfl)
    have hs : Function.Surjective f := by
      intro y
      have hy : y ∈ Algebra.adjoin F ({x} : Set A) := hx ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨r, rfl⟩ := hy
      exact ⟨AdjoinRoot.mk _ r, by rw [AdjoinRoot.liftAlgHom_mk]; rfl⟩
    have h1 := LinearMap.finrank_range_le f.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, pb.finrank, AdjoinRoot.powerBasis'_dim] at h1
    exact h1
  have h1 : p = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon hp (minpoly.dvd F x hpx) (by omega)
  have h2 : (LinearMap.mulLeft F x).charpoly = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon (LinearMap.charpoly_monic _) (minpoly.dvd F x hCH) (by omega)
  rw [h2, h1]

theorem val_inv_pow_mul {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    val K.O ((x ^ n)⁻¹ * y) = val K.O y - n * val K.O x := by
  unfold val
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E ((x ^ n)⁻¹) ≠ 0 := by simp [hx]
  have h2 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E y ≠ 0 := by simp [hy]
  rw [map_mul, WithZero.log_mul h1 h2, map_inv₀, map_pow, WithZero.log_inv, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem val_resultant_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (k : ℕ) (t : K.O), t ≠ 0 → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (B₁.P * B₂.P).Separable ∧ GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) - ((k * a * b : ℕ) : ℤ) := by
  intro E _ _ _ w K e hval k t ht hk a b Q₁ Q₂ B₁ B₂ hm₁ hm₂ ha hb hsep hadj₁ hQ₁ hf₁ hadj₂ hQ₂ hf₂
  set t' : K.E := algebraMap K.O K.E t with ht'def
  have ht' : t' ≠ 0 := by
    rw [ht'def]; exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ht
  have hP : ∀ (B : InvAlg K) (Q : (w.adicCompletion E)[X]), Q.Monic →
      Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ →
      aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 →
      Module.finrank K.E B.A = Q.natDegree → B.P = shiftPoly t' 1 (Q.map e.symm.toRingHom) := by
    intro B Q hQm hadj hQ hfin
    have hd : (Q.map e.symm.toRingHom).natDegree = Q.natDegree := natDegree_map _
    have hu : aeval B.g (C t' * X + C 1) = 1 + algebraMap K.O B.A t * B.g := by
      rw [map_add, map_mul, aeval_C, aeval_X, aeval_C, map_one, ht'def, ← IsScalarTower.algebraMap_apply]
      ring
    unfold InvAlg.P
    apply charpoly_eq_of_adjoin
    · rw [eq_top_iff, ← hadj]
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff, ← hu]
      exact aeval_mem_adjoin_singleton _ _
    · exact monic_shiftPoly t' 1 ht' _ (hQm.map _)
    · unfold shiftPoly
      rw [map_mul, aeval_C, aeval_comp, hu, hQ, mul_zero]
    · rw [natDegree_shiftPoly t' 1 ht', hd, hfin]
  have e₁ := hP B₁ Q₁ hm₁ hadj₁ hQ₁ hf₁
  have e₂ := hP B₂ Q₂ hm₂ hadj₂ hQ₂ hf₂
  have hm₁' : (Q₁.map e.symm.toRingHom).Monic := hm₁.map _
  have hm₂' : (Q₂.map e.symm.toRingHom).Monic := hm₂.map _
  refine ⟨?_, ?_⟩
  · rw [e₁, e₂, ← shiftPoly_mul t' 1 _ _ hm₁' hm₂', ← Polynomial.map_mul]
    exact separable_shiftPoly t' 1 ht' _ hsep.map
  · rw [e₁, e₂, resultant_shiftPoly t' 1 ht' _ _ hm₁' hm₂']
    have hR : resultant (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) = e.symm (resultant Q₁ Q₂) := by
      rw [resultant_map_map, natDegree_map, natDegree_map]; rfl
    have hR0 : resultant Q₁ Q₂ ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
    rw [hR, natDegree_map, natDegree_map, val_inv_pow_mul ht' ((_root_.map_ne_zero _).2 hR0), hval, RingEquiv.apply_symm_apply, hk, ha, hb]
    push_cast; ring

end GlobalTheory.UnitLemma.ShiftRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOne
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

theorem algHom_eq_subst {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : constantCoeff (f X) = 0) (a : O⟦X⟧) : f a = a.subst (f X) := by
  have hs : HasSubst (f X) := HasSubst.of_constantCoeff_zero' hf
  have e : f = substAlgHom hs :=
    GlobalTheory.CycFr.algHom_ext_X f (substAlgHom hs) (X_dvd_iff.2 hf) (by rw [coe_substAlgHom, subst_X hs])
  conv_lhs => rw [e]
  rw [coe_substAlgHom]

theorem mem_mu_of_isOfFinOrder {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]ˣ)
    (hx : IsOfFinOrder x) : (x : ℤ_[l]) ∈ mu l := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  rw [mu, Polynomial.mem_nthRootsFinset hl]
  have h := GlobalTheory.TorsionCard.eq_one_of_red h2 (x ^ (l - 1)) hx.pow
    (by rw [map_pow, ZMod.units_pow_card_sub_one_eq_one])
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isUnit_sub_one_padicInt {l : ℕ} [Fact l.Prime] : IsUnit (((l - 1 : ℕ) : ℤ_[l])) := by
  have h1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have e : ((l - 1 : ℕ) : ℤ_[l]) = -(1 - (l : ℤ_[l])) := by
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [e, IsUnit.neg_iff]
  exact isUnit_one_sub_self_of_mem_nonunits _ (PadicInt.irreducible_p (p := l)).not_isUnit

section Situation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n)

theorem wach_φ₀_X : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, P.PD_p K]

theorem wach_φ₀_eq (a : (↥(OL LL))⟦X⟧) : W.φ₀ a = phi l ↥(OL LL) a := by
  have hc : constantCoeff (W.φ₀ X) = 0 := by rw [wach_φ₀_X]; simp
  rw [algHom_eq_subst W.φ₀ hc a, wach_φ₀_X]; rfl

theorem wach_q₀_eq : W.q₀ = q l ↥(OL LL) := by
  have e1 := W.q₀_def
  rw [P.PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e1
  exact mul_left_cancel₀ X_ne_zero e1

theorem wach_γ₀_eq (g : W.Gam) (z : ℤ_[l]) (hz : (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) z)
    (a : (↥(OL LL))⟦X⟧) : W.γ₀ g a = act l ↥(OL LL) z a := by
  have e := GlobalTheory.CycFr.eq_act_of_comm W.φ₀ (W.γ₀ g) z (wach_φ₀_X W) (W.γ₀_comm g) (W.γ₀_X g).1
    (by rw [(W.γ₀_X g).2, hz])
  rw [e, GlobalTheory.CycFr.act_apply]; rfl

theorem wach_χΓ_onto (hK : K.1 ≤ MaximalUnramifiedExtension l) (z : ℤ_[l]ˣ) :
    ∃ g : W.Gam, (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) := by
  obtain ⟨σ, hσ, hσz⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K hK z
  refine ⟨W.resΓ ⟨σ, hσ⟩, Subtype.val_injective ?_⟩
  have e := W.χΓ_res ⟨σ, hσ⟩
  rw [P.PD_χ K ⟨σ, hσ⟩] at e
  change algebraMap ↥(OL LL) ↥LL.1 _ = algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) _)
  rw [e]
  change algebraMap ℚ_[l] ↥LL.1 (P.χQ σ : ℚ_[l]) = _
  rw [hσz]; rfl

theorem wach_torsion_mem_mu (h2 : l ≠ 2) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    ∃ d ∈ mu l, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 hδ
  refine ⟨(χ δ : ℤ_[l]), mem_mu_of_isOfFinOrder h2 _ ?_, (hχ δ).symm⟩
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← map_pow, hδk, map_one]⟩

theorem wach_mu_mem_torsion (hK : K.1 ≤ MaximalUnramifiedExtension l) (d : ℤ_[l]) (hd : d ∈ mu l) :
    ∃ δ ∈ W.DelF, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hd1 : d ^ (l - 1) = 1 := (Polynomial.mem_nthRootsFinset hl (1 : ℤ_[l])).1 hd
  have hu : IsUnit d := IsUnit.of_pow_eq_one hd1 hl.ne'
  obtain ⟨g, hg⟩ := wach_χΓ_onto W hK hu.unit
  rw [hu.unit_spec] at hg
  refine ⟨g, (W.DelF_def g).2 ⟨l - 1, hl, W.χΓ_inj ?_⟩, hg⟩
  apply Units.ext
  rw [map_pow, Units.val_pow_eq_pow_val, hg, ← map_pow, hd1, map_one, map_one, Units.val_one]

theorem wach_invariants (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) (a : (↥(OL LL))⟦X⟧) :
    (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ↔ ∃ y, inc l ↥(OL LL) y = a := by
  have R := fixed_relation_holds l ↥(OL LL) h2 a
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := R.1 (fun d hd => by
      obtain ⟨δ, hδ, hδd⟩ := wach_mu_mem_torsion W hK d hd
      rw [← wach_γ₀_eq W δ d hδd a, ha δ hδ])
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩ δ hδ
    obtain ⟨d, hd, hδd⟩ := wach_torsion_mem_mu W h2 δ hδ
    rw [wach_γ₀_eq W δ d hδd]
    exact R.2 ⟨y, hy.symm⟩ d hd

theorem wach_card_isUnit (h2 : l ≠ 2) (hK : K.1 ≤ Ks K 1) : IsUnit (W.DelF.card : ↥(OL LL)) := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W h2 hK
  have hu := (isUnit_sub_one_padicInt (l := l)).map (algebraMap ℤ_[l] ↥(OL LL))
  rw [map_natCast, ← hc, Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end Situation

theorem ringFacts_of_caseA {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) : RingFacts (H.W K 1 LL hA.2.2) :=
  ⟨wach_φ₀_eq _, wach_q₀_eq _, wach_γ₀_eq _, wach_χΓ_onto _ hA.1, wach_invariants _ hA.1 hA.2.1,
    wach_card_isUnit _ hA.2.1 hA.2.2.2.2.1⟩

end GlobalTheory.WachPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
private lemma exists_coheight_one_generalization_not_unitAt {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} {f : X.functionField} (hf : f ≠ 0)
    (hreg : _root_.GlobalTheory.Cartier.RegAt z f) (hnu : ¬ _root_.GlobalTheory.Cartier.UnitAt z f) :
    ∃ w : X, w ⤳ z ∧ Order.coheight w = 1 ∧ ¬ _root_.GlobalTheory.Cartier.UnitAt w f := by
  obtain ⟨U, hzU, a, rfl⟩ := hreg.exists_fnOf
  obtain ⟨V, hV, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have hV' : IsAffineOpen V := hV
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hzV⟩
  rw [← _root_.GlobalTheory.Cartier.fnOf_resG hVU hgV a] at hf hnu ⊢
  generalize _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hVU a = b at hf hnu ⊢
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hmem : ∀ q : PrimeSpectrum Γ(X, V), hV'.fromSpec q ∈ V := fun q => by
    have : hV'.fromSpec q ∈ Set.range hV'.fromSpec := Set.mem_range_self q
    rwa [hV'.range_fromSpec] at this
  have key : ∀ q : PrimeSpectrum Γ(X, V),
      _root_.GlobalTheory.Cartier.UnitAt (hV'.fromSpec q) (_root_.GlobalTheory.Cartier.fnOf V hgV b) ↔
        b ∉ q.asIdeal := by
    intro q
    rw [_root_.GlobalTheory.Cartier.unitAt_fnOf_iff (hmem q) hgV b]
    have : hV'.fromSpec q ∈ X.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b := by
      rw [← hV'.fromSpec_preimage_basicOpen]; rfl
    rw [this, PrimeSpectrum.mem_basicOpen]
  set p := hV'.primeIdealOf ⟨z, hzV⟩
  have hpz : hV'.fromSpec p = z := hV'.fromSpec_primeIdealOf ⟨z, hzV⟩
  have hbp : b ∈ p.asIdeal := by
    by_contra h
    exact hnu (hpz ▸ (key p).mpr h)
  obtain ⟨P, hPmin, hPp⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hbp)
  haveI hPprime : P.IsPrime := hPmin.1.1
  set q : PrimeSpectrum Γ(X, V) := ⟨P, hPprime⟩
  have hbP : b ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  refine ⟨hV'.fromSpec q, ?_, ?_, fun h => (key q).mp h hbP⟩
  · rw [← hpz]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hPp).map hV'.fromSpec.continuous
  · letI := X.presheaf.algebra_section_stalk ⟨hV'.fromSpec q, hmem q⟩
    haveI hloc := hV'.isLocalization_stalk' q (hmem q)
    have hdim : ringKrullDim (X.presheaf.stalk (hV'.fromSpec q)) = (P.height : WithBot ℕ∞) :=
      @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q.asIdeal q.2 _ _ _ hloc
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    haveI : (Ideal.span {b}).IsPrincipal := ⟨⟨b, rfl⟩⟩
    have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
    have hne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff]
      intro hmin
      have hbot : P ≤ ⊥ := hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
      have hb0 : b = 0 := (Submodule.eq_bot_iff _).mp (le_bot_iff.mp hbot) b hbP
      exact hf (by rw [hb0, map_zero])
    have h1 : P.height = 1 := le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)
    rw [h1] at hdim
    exact_mod_cast hdim

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in

theorem _root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (D₀ : _root_.GlobalTheory.Cartier.CartierDiv X) (m : ℕ) (z : X),
    D₀.Eff → 0 < m →
      (_root_.GlobalTheory.PairStep.Off (_root_.GlobalTheory.Discrepancy.qWeil D₀ m) z ↔
        z ∉ D₀.supp) := by
  intro X _ _ D m z hD hm
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  obtain ⟨U, hzU, hU⟩ := hg.exists_nhds
  have hgen : ∀ w : X, w ⤳ z → D.IsEqn w g := fun w hwz =>
    hU w (hwz.mem_open U.isOpen hzU)
  unfold _root_.GlobalTheory.PairStep.Off _root_.GlobalTheory.Discrepancy.qWeil
  simp only [div_eq_zero_iff, hm', or_false, Int.cast_eq_zero]
  rw [hg.mem_supp_iff, not_not]
  constructor
  · intro h
    by_contra hnu
    have hreg := (_root_.GlobalTheory.Cartier.CartierDiv.eff_iff.mp hD) z g hg
    obtain ⟨w, hwz, hw1, hwnu⟩ := exists_coheight_one_generalization_not_unitAt (Units.ne_zero g) hreg hnu
    have hmult := h w hwz
    rw [(hgen w hwz).mult_eq] at hmult
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.Discrepancy.regAt_of_specializes hwz hreg
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact Units.ne_zero g (by rw [← ha, map_zero])
    rw [← ha, _root_.GlobalTheory.Cartier.ord_algebraMap hw1 ha0] at hmult
    have hdim : ringKrullDim (X.presheaf.stalk w) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, hw1]; rfl
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := by
      rw [Ring.krullDimLE_iff, hdim]
      exact_mod_cast le_rfl
    have hfin := isFiniteLength_quotient_span_singleton (X.presheaf.stalk w)
      (mem_nonZeroDivisors_of_ne_zero ha0)
    have htop := Module.length_ne_top_iff.mpr hfin
    have hzero : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a}) ≠ 0 := by
      rw [Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
        Ideal.span_singleton_eq_top]
      exact fun hunit => hwnu ⟨a, hunit, ha⟩
    have : (Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a})).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]
      tauto
    exact this (by exact_mod_cast hmult)
  · intro hunit w hwz
    rw [(hgen w hwz).mult_eq]
    obtain ⟨V, hzV, hV⟩ := hunit.exists_nhds
    exact (hV w (hwz.mem_open V.isOpen hzV)).ord_eq_zero

end GlobalTheory.PairStep
end

