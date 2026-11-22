import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
section
noncomputable section

open TensorProduct

namespace GlobalTheory

section AdicAux

variable {S : Type*} [CommRing S] (a : S)

theorem mem_span_singleton_pow_smul_top_iff_exists {N : Type*} [AddCommGroup N] [Module S N] (n : ℕ)
    (x : N) : x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule S N) ↔ ∃ y : N, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

theorem isAdicComplete_fin_pi [IsAdicComplete (Ideal.span {a}) S] (k : ℕ) :
    IsAdicComplete (Ideal.span {a}) (Fin k → S) where
  haus' x hx := funext fun i => by
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) S) (x i) fun n => ?_
    have h := hx n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨y i, by simpa using congrFun hy i⟩
  prec' f hf := by
    have key : ∀ i, ∃ L : S, ∀ n,
        f n i ≡ L [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule S S)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {a}) S) fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
        obtain ⟨y, hy⟩ := h
        exact ⟨y i, by simpa using congrFun hy i⟩
    choose L hL using key
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists]
    have h := fun i => (mem_span_singleton_pow_smul_top_iff_exists a n _).1 (SModEq.sub_mem.1 (hL i n))
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩

theorem isAdicComplete_of_retraction {N F : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup F] [Module S F] [IsAdicComplete (Ideal.span {a}) F] (i : N →ₗ[S] F)
    (r : F →ₗ[S] N) (h : r ∘ₗ i = LinearMap.id) : IsAdicComplete (Ideal.span {a}) N where
  haus' x hx := by
    have h1 : i x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) F) (i x) fun n => by
      have h2 := hx n
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
      obtain ⟨y, hy⟩ := h2
      rw [sub_zero] at hy ⊢
      exact ⟨i y, by rw [hy, map_smul]⟩
    have h3 := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h1, map_zero, LinearMap.id_apply] at h3
    exact h3.symm
  prec' f hf := by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun n => i (f n))
      (inferInstance : IsPrecomplete (Ideal.span {a}) F) fun {m n} hmn => by
        have h2 := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
        obtain ⟨y, hy⟩ := h2
        exact ⟨i y, by rw [← map_sub, hy, map_smul]⟩
    refine ⟨r L, fun n => ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
    obtain ⟨y, hy⟩ := h2
    refine ⟨r y, ?_⟩
    have h3 := LinearMap.congr_fun h (f n)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h3
    rw [← map_smul, ← hy, map_sub, h3]

theorem isAdicComplete_of_finite_projective [IsAdicComplete (Ideal.span {a}) S] (N : Type*)
    [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Projective S N] :
    IsAdicComplete (Ideal.span {a}) N := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  haveI := isAdicComplete_fin_pi a k
  exact isAdicComplete_of_retraction a s f hs

end AdicAux

namespace PDivGroup

open PDiv Coalgebra Bialgebra

variable {p : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : PDivGroup p R)

def cotBase (n : ℕ) : Cot R (G.A n) →ₗ[R] Cot R' ((G.baseChange R').A n) :=
  AugCot.mapBase (ε := counitAlgHom R (G.A n)) (ε' := counitAlgHom R' (R' ⊗[R] G.A n))
    (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] R' ⊗[R] G.A n)
    (fun a => (toBaseChange R R' (G.A n)).counit_map a)

theorem cotBase_isBaseChange (n : ℕ) : IsBaseChange R' (G.cotBase (R' := R') n) :=
  AugCot.isBaseChange_mapBase _ _ (TensorProduct.isBaseChange R (G.A n) R')

theorem toBase_cot_eq (n : ℕ) (v : Cot R (G.A n)) :
    ((G.toBase R').app n).cot v = G.cotBase n v := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ v
  have h1 := SemiBialgHom.cot_d ((G.toBase R').app n) a
  have h2 := AugCot.mapBase_d (ε := counitAlgHom R (G.A n))
    (ε' := counitAlgHom R' (R' ⊗[R] G.A n))
    (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] R' ⊗[R] G.A n)
    (fun a => (toBaseChange R R' (G.A n)).counit_map a) a
  exact h1.trans h2.symm

variable {M : Type} [AddCommGroup M] [Module R M] (c : M →ₗ[R] G.omega)

def omegaToBaseChangeOmega : M →ₗ[R] (G.baseChange R').omega where
  toFun w := (G.toBase R').omega (c w)
  map_add' v w := by rw [map_add, map_add]
  map_smul' r w := by
    rw [map_smul, map_smulₛₗ, RingHom.id_apply, algebraMap_smul]

def omegaBCMap : R' ⊗[R] M →ₗ[R'] (G.baseChange R').omega :=
  LinearMap.liftBaseChange R' (G.omegaToBaseChangeOmega c)

theorem omegaBCMap_level (n : ℕ) (x : R' ⊗[R] M) :
    (G.omegaBCMap c x).1 n =
      (G.cotBase_isBaseChange n).equiv (((G.omegaLevel n).comp c).baseChange R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, ← hx, ← hy]; rfl
  | tmul r w =>
    rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, omegaBCMap,
      LinearMap.liftBaseChange_tmul]
    change r • ((G.toBase R').app n).cot ((c w).1 n) = _
    rw [toBase_cot_eq]
    rfl

end PDivGroup

end GlobalTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddi
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Polynomial IntermediateField

namespace GlobalTheory.LadicDenom

theorem norm_natCast_padicComplex (l : ℕ) [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_ratCast_padicComplex (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = ‖(q : ℚ_[l])‖ := by
  have h : (q : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_padicComplex, Padic.norm_p]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem not_dvd_den_of_norm_le_one (l : ℕ) [hl : Fact l.Prime] (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have hnum : ‖(q.num : ℚ_[l])‖ = 1 := by
    have hc : l.Coprime q.num.natAbs := (Nat.Prime.coprime_iff_not_dvd hl.out).2 fun hn =>
      hl.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced hn hd)
    rcases Int.natAbs_eq q.num with e | e
    · rw [e, Int.cast_natCast]; exact Padic.norm_natCast_eq_one_iff.2 hc
    · rw [e, Int.cast_neg, Int.cast_natCast, norm_neg]; exact Padic.norm_natCast_eq_one_iff.2 hc
  have hden : ‖(q.den : ℚ_[l])‖ < 1 := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · exact_mod_cast Padic.norm_int_le_one (q.den : ℤ)
    · have := Padic.norm_natCast_eq_one_iff.1 e
      exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hd)
  have e : (q : ℚ_[l]) * (q.den : ℚ_[l]) = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have e2 := congrArg norm e
  rw [norm_mul, hnum] at e2
  have : ‖(q : ℚ_[l])‖ * ‖(q.den : ℚ_[l])‖ < 1 :=
    (mul_le_of_le_one_left (norm_nonneg _) h).trans_lt hden
  exact this.ne e2

set_option synthInstance.maxHeartbeats 400000 in

theorem norm_root_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (β : ℂ_[l]) (hβ : β ∈ (minpoly ℚ α).aroots ℂ_[l]) :
    ‖β‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let φ := (algHomAdjoinIntegralEquiv ℚ hα).symm ⟨β, hβ⟩
  letI : Algebra ℚ⟮α⟯ ℂ_[l] := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ⟮α⟯ (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let ψ : algebraicClosure ℚ ℂ →ₐ[ℚ⟮α⟯] ℂ_[l] := IsAlgClosed.lift
  have e : ψ α = β := by
    have h1 := ψ.commutes (AdjoinSimple.gen ℚ α)
    rw [AdjoinSimple.algebraMap_gen] at h1
    rw [h1]
    exact algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hα ⟨β, hβ⟩
  rw [← e]
  exact h ψ.toRingHom

theorem coeff_norm_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (i : ℕ) :
    ‖(((minpoly ℚ α).coeff i : ℚ) : ℂ_[l])‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set P := (minpoly ℚ α).map (algebraMap ℚ ℂ_[l]) with hP
  let S := (NormedField.valuation (K := ℂ_[l])).integer
  have memS : ∀ z : ℂ_[l], z ∈ S ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  have hmon : P.Monic := (minpoly.monic hα).map _
  have hroots : ∀ β ∈ P.roots, β ∈ S := fun β hβ => (memS β).2 (norm_root_le_one l α h β hβ)
  have hc : (((minpoly ℚ α).coeff i : ℚ) : ℂ_[l]) = P.coeff i := by
    rw [hP, coeff_map, eq_ratCast]
  rw [hc, ← memS]
  by_cases hi : i ≤ P.natDegree
  · rw [coeff_eq_esymm_roots_of_card IsAlgClosed.card_roots_eq_natDegree hi, hmon.leadingCoeff, one_mul]
    refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
    unfold Multiset.esymm
    refine S.multiset_sum_mem _ fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hz
    exact S.multiset_prod_mem _ fun w hw => hroots w (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hw)
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact S.zero_mem

theorem intAt_of_forall_norm_le_one (l : ℕ) [hl : Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) : IntAt l (α : ℂ) := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set p := minpoly ℚ α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hden : ∀ i, ¬ l ∣ (p.coeff i).den := fun i =>
    not_dvd_den_of_norm_le_one l _ (by rw [← norm_ratCast_padicComplex]; exact coeff_norm_le_one l α h i)
  set D : ℕ := ∏ i ∈ Finset.range p.natDegree, (p.coeff i).den with hD
  have hDc : D.Coprime l := Nat.Coprime.prod_left fun i _ =>
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 (hden i)).symm
  refine ⟨D, hDc, ?_⟩
  set q := p.scaleRoots (D : ℚ) with hq
  have hql : q ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hq, coeff_scaleRoots]
    rcases lt_trichotomy n p.natDegree with hn | hn | hn
    · obtain ⟨e, he⟩ : (p.coeff n).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hn)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - n = k + 1 := ⟨p.natDegree - n - 1, by omega⟩
      have h1 : p.coeff n * ((p.coeff n).den : ℚ) = (p.coeff n).num := Rat.mul_den_eq_num _
      refine ⟨(p.coeff n).num * e * D ^ k, ?_⟩
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [hk, pow_succ, ← h1]
      have h2 : (D : ℚ) = (p.coeff n).den * e := by exact_mod_cast he
      rw [h2]
      ring
    · refine ⟨1, ?_⟩
      rw [hn, hmon.coeff_natDegree, Nat.sub_self, pow_zero, mul_one, map_one]
    · refine ⟨0, ?_⟩
      rw [coeff_eq_zero_of_natDegree_lt hn, zero_mul, map_zero]
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_scaleRoots]; exact hmon
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hql hqm
  have hroot : aeval ((D : algebraicClosure ℚ ℂ) * α) q = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (D : ℚ)) (minpoly.aeval ℚ α)
    simpa using this
  have hint : IsIntegral ℤ ((D : algebraicClosure ℚ ℂ) * α) := by
    refine ⟨Q, hQm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, algebraMap_int_eq, hQ]
    exact hroot
  have := map_isIntegral_int (algebraicClosure ℚ ℂ).val.toRingHom hint
  simpa using this

theorem valGe_iff_forall_sz (l : ℕ) [hl : Fact l.Prime] (r : ℝ) (x : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  constructor
  · intro hv lam
    obtain ⟨N, hN, hi⟩ := hv ⌈r⌉ 1 one_pos (by simpa using Int.le_ceil r)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hN
      exact hl.out.one_lt.ne' hN
    have hmem : x ∈ algebraicClosure ℚ ℂ := by
      have h1 : (N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1) ∈ algebraicClosure ℚ ℂ :=
        mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic
      have h2 : ((N : ℂ) * (l : ℂ) ^ ⌈r⌉) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hN0) (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      have h3 : x = ((N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1)) * ((N : ℂ) * (l : ℂ) ^ ⌈r⌉)⁻¹ := by
        rw [pow_one, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ h2, one_mul]
      rw [h3]
      exact mul_mem h1 (inv_mem (mul_mem (IntermediateField.natCast_mem _ _) (zpow_mem (IntermediateField.natCast_mem _ _) _)))
    refine ⟨hmem, ?_⟩
    set t := ‖lam ⟨x, hmem⟩‖ with ht
    have key : ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → t ^ n ≤ (l : ℝ) ^ m := by
      intro m n hn hmn
      obtain ⟨N, hN, hi⟩ := hv m n hn hmn
      set β : algebraicClosure ℚ ℂ := (N : algebraicClosure ℚ ℂ) * ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)
      have hiβ : IsIntegral ℤ β := by
        refine (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) Subtype.val_injective).1 ?_
        have e : ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) β = (N : ℂ) * ((l : ℂ) ^ m * x ^ n) :=
          Complex.ext rfl rfl
        rw [e]; exact hi
      have h1 := norm_le_one_of_isIntegral (map_isIntegral_int lam hiβ)
      simp only [β, map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow] at h1
      rw [norm_natCast_padicComplex, Padic.norm_natCast_eq_one_iff.2 hN.symm, norm_prime_padicComplex, one_mul,
        inv_zpow', zpow_neg, inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one] at h1
      exact h1
    by_contra hgt
    rw [not_le] at hgt
    have htp : 0 < t := (Real.rpow_pos_of_pos hl0 r).trans hgt
    have hr : r < Real.logb l t := (Real.lt_logb_iff_rpow_lt hl1 htp).2 hgt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
    have hq3 : (l : ℝ) ^ (q : ℝ) < t := (Real.lt_logb_iff_rpow_lt hl1 htp).1 hq2
    have hqe : (q : ℝ) = (q.num : ℝ) / (q.den : ℕ) := by exact_mod_cast (Rat.num_div_den q).symm
    have hk := key q.num q.den q.den_pos (by rw [← hqe]; exact hq1.le)
    have h4 : ((l : ℝ) ^ (q : ℝ)) ^ q.den < t ^ q.den :=
      pow_lt_pow_left₀ hq3 (Real.rpow_nonneg hl0.le _) q.den_pos.ne'
    have h5 : ((l : ℝ) ^ (q : ℝ)) ^ q.den = (l : ℝ) ^ q.num := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, hqe,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.2 q.den_pos.ne')]
    rw [h5] at h4
    exact absurd hk (not_le.2 h4)
  · intro h
    let lam₀ : algebraicClosure ℚ ℂ →+* ℂ_[l] := (IsAlgClosed.lift : algebraicClosure ℚ ℂ →ₐ[ℚ] ℂ_[l]).toRingHom
    obtain ⟨hmem, -⟩ := h lam₀
    intro m n hn hmn
    have hmn' : r * n ≤ m := by rwa [le_div_iff₀ (Nat.cast_pos.2 hn)] at hmn
    have hb : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l],
        ‖lam ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)‖ ≤ 1 := by
      intro lam
      obtain ⟨h', hle⟩ := h lam
      rw [map_mul, map_zpow₀, map_pow, map_natCast, norm_mul, norm_zpow, norm_pow, norm_prime_padicComplex,
        inv_zpow', zpow_neg]
      have h2 : ‖lam ⟨x, hmem⟩‖ ^ n ≤ (l : ℝ) ^ m := by
        calc ‖lam ⟨x, hmem⟩‖ ^ n ≤ ((l : ℝ) ^ r) ^ n := pow_le_pow_left₀ (norm_nonneg _) hle n
          _ = (l : ℝ) ^ (r * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
          _ ≤ (l : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hl1.le hmn'
          _ = (l : ℝ) ^ m := Real.rpow_intCast _ _
      rw [inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one]
      exact h2
    have := intAt_of_forall_norm_le_one l _ hb
    have e : (((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n : algebraicClosure ℚ ℂ) : ℂ) = (l : ℂ) ^ m * x ^ n :=
      Complex.ext rfl rfl
    rwa [e] at this

end GlobalTheory.LadicDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem isAlgebraic_of_isIntegral_natCast_mul (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (h : IsIntegral ℤ ((n : ℂ) * z)) : IsAlgebraic ℚ z := by
  have h1 : IsIntegral ℚ ((n : ℂ) * z) := h.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ ℂ ((n : ℚ)⁻¹)) := isIntegral_algebraMap
  have h3 := h2.mul h1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have : algebraMap ℚ ℂ ((n : ℚ)⁻¹) * ((n : ℂ) * z) = z := by
    rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  rw [this] at h3
  exact h3.isAlgebraic

theorem qAll_isAlgebraic_torsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N),
    QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧
      (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  intro N _ x
  have hN : N ≠ 0 := NeZero.ne N
  have hx : N • x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  have hc := fun k => GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N x k (Nat.pos_of_ne_zero hN) hx
  refine ⟨⟨cP N x, GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N x, fun k => ?_⟩, ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => ?_⟩,
    fun h0 => ⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x h0, fun k => ?_⟩⟩
  · refine isAlgebraic_of_isIntegral_natCast_mul (12 * N ^ 2) (by positivity) _ ?_
    have := (hc k).2.2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 3) (by positivity) _ ?_
    have := (hc k).2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 2) (by positivity) _ ?_
    have := (hc k).1
    push_cast
    exact this

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSurjectiveNilpotentKer
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem res_eq_app_comp {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) :
    res i U = i.app (upOpen i U) ≫
      Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rfl

theorem res_surjective_nilpotent_ker : ∀ {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i], (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom)) → ∀ U : Y₀.Opens, IsAffineOpen (GlobalTheory.FerrandPush.upOpen i U) → Function.Surjective (GlobalTheory.FerrandPush.res i U).hom ∧ IsNilpotent (RingHom.ker (GlobalTheory.FerrandPush.res i U).hom) := by
  intro Y₀ Y₁ i _ _ hnil U hU
  have e := res_eq_app_comp i U
  set g := Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op with hg
  haveI : IsIso g := by rw [hg]; infer_instance
  have hgb : Function.Bijective g.hom :=
    ConcreteCategory.bijective_of_isIso g
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [CommRingCat.hom_comp]
    exact hgb.2.comp (i.app_surjective _ hU)
  · rw [CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hgb.1]
    exact hnil _ hU

end GlobalTheory.FerrandPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (exact GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (intros; apply GlobalTheory.EtC.SmallEtaleCech.hyp_coAug <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  first | exact @GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | exact GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | (intros; apply GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  first
  | exact @GlobalTheory.EtC.TwPairUniq.main
  | exact GlobalTheory.EtC.TwPairUniq.main
  | (intros; apply GlobalTheory.EtC.TwPairUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecompositionStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition : ∀ (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt) (y : N.X), h ^ m = N.io y → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S) → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S) → ∀ a b : N.X, ∃ w : Oˣ, (w : O) ∈ S ∧ N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  first | exact @GlobalTheory.theta_term_smul_add | exact GlobalTheory.theta_term_smul_add | (intros; apply GlobalTheory.theta_term_smul_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltUntiltDividesPowStatement
section
open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_untilt_divides_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) → ∀ (pflat f : PreTilt R p), PreTilt.untilt pflat = (p : R) → (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c) → Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R) → ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → (f ^ p - 1) ^ (p - 1) ∣ c := by
  first | exact @GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated | exact GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated | (intros; apply GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeOmActKronBlockDiagonalLeStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_omAct_kron_blockDiagonal_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  first | exact @GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le | exact GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le | (intros; apply GlobalTheory.FockBlockDeg.totalDegree_omAct_kron_le <;> assumption)
end

