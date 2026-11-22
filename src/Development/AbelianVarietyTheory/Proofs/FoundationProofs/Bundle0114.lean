import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0098
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevelStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ), (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) → ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧ (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧ ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  first | exact @GlobalTheory.FamOfLevel.exists_family | exact GlobalTheory.FamOfLevel.exists_family | (intros; apply GlobalTheory.FamOfLevel.exists_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.NTr

theorem zt_prim {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p n : ℕ) (hp : 0 < p) :
    IsPrimitiveRoot (zt ε p n) (p ^ n) := by
  have h := GlobalTheory.Glue.KTExp.map_eOm ε (1 / (p : ℚ) ^ n)
  have hn : p ^ n ≠ 0 := pow_ne_zero _ hp.ne'
  have hc := Complex.isPrimitiveRoot_exp (p ^ n) hn
  have e : Complex.exp (2 * Real.pi * Complex.I * (((1 / (p : ℚ) ^ n : ℚ)) : ℂ)) = Complex.exp (2 * Real.pi * Complex.I / ((p ^ n : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [e] at h
  unfold zt
  rw [← h] at hc
  exact (IsPrimitiveRoot.map_iff_of_injective ε.injective).mp hc

theorem zt_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p L m : ℕ) (hp : 0 < p) (hm : m ≤ L) :
    zt ε p L ^ (p ^ (L - m)) = zt ε p m := by
  apply ε.injective
  unfold zt
  rw [map_pow, GlobalTheory.Glue.KTExp.map_eOm, GlobalTheory.Glue.KTExp.map_eOm, ← Complex.exp_nat_mul]
  congr 1
  have hpL : (p : ℂ) ^ L = (p : ℂ) ^ (L - m) * (p : ℂ) ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  rw [hpL]
  field_simp

theorem exists_algEquiv_primitiveRoot_pow_of_isAlgClosed {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃+* Ω, σ ζ = ζ ^ k := by
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral hn).tower_top
  have hk' : IsPrimitiveRoot (ζ ^ k) n := hζ.pow_of_coprime k hk
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζ hn).symm
  have hroot : ζ ^ k ∈ (minpoly ℚ ζ).aroots Ω := by
    rw [Polynomial.mem_aroots, hmin]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff).2 hk'
  let φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ ^ k, hroot⟩
  let ψ : Ω →ₐ[ℚ] Ω := φ.liftNormal Ω
  refine ⟨(AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ)).toRingEquiv, ?_⟩
  have h1 := φ.liftNormal_commutes Ω (IntermediateField.AdjoinSimple.gen ℚ ζ)
  rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen] at h1
  simpa [ψ] using h1

theorem exists_aut {Ω : Type} [Field Ω] [iA : Algebra ℚ Ω] [iC : IsAlgClosure ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ k := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have e : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have i1 : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI i2 : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by convert i1 using 2; exact e.symm
  obtain ⟨σ, hσ⟩ := exists_algEquiv_primitiveRoot_pow_of_isAlgClosed (Ω := Ω) ζ n hn hζ k hk
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), hσ⟩
  rw [eq_ratCast]
  exact map_ratCast σ x

open Classical in
theorem sum_reindex (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L) {M : Type} [AddCommMonoid M] (g : ℕ → M) :
    ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), g (a : ZMod (p ^ L)).val
      = ∑ k ∈ Finset.range (p ^ (L - m)), g (1 + p ^ m * k) := by
  have hp : p.Prime := hpf.out
  have hp1 : 1 < p := hp.one_lt
  have hpm : 1 < p ^ m := Nat.one_lt_pow (by omega) hp1
  have hN : p ^ m * p ^ (L - m) = p ^ L := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have cop : ∀ k : ℕ, Nat.Coprime (1 + p ^ m * k) (p ^ L) := by
    intro k
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h2 : p ∣ p ^ m * k := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) k
    exact hp.not_dvd_one ((Nat.dvd_add_left h2).mp h)
  have hlt : ∀ k < p ^ (L - m), 1 + p ^ m * k < p ^ L := by
    intro k hk
    have : p ^ m * (k + 1) ≤ p ^ m * p ^ (L - m) := Nat.mul_le_mul_left _ hk
    rw [hN] at this
    nlinarith
  have hval : ∀ k < p ^ (L - m), ((ZMod.unitOfCoprime (1 + p ^ m * k) (cop k) : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)).val = 1 + p ^ m * k := by
    intro k hk
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt k hk)]
  symm
  refine Finset.sum_bij (fun k _ => ZMod.unitOfCoprime (1 + p ^ m * k) (cop k)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval k hk]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  · intro k hk k' hk' h
    rw [Finset.mem_range] at hk hk'
    have := congrArg (fun u : (ZMod (p ^ L))ˣ => (u : ZMod (p ^ L)).val) h
    rw [hval k hk, hval k' hk'] at this
    have h3 : p ^ m * k = p ^ m * k' := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hv : (b : ZMod (p ^ L)).val % p ^ m = 1 := by
      have := hb; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hpm]
    have hvl : (b : ZMod (p ^ L)).val < p ^ L := ZMod.val_lt _
    have hdm := Nat.div_add_mod ((b : ZMod (p ^ L)).val) (p ^ m)
    rw [hv] at hdm
    set k := (b : ZMod (p ^ L)).val / p ^ m
    have hk : k < p ^ (L - m) := by
      by_contra hc
      push_neg at hc
      have : p ^ m * p ^ (L - m) ≤ p ^ m * k := Nat.mul_le_mul_left _ hc
      rw [hN] at this
      omega
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    have : 1 + p ^ m * k = (b : ZMod (p ^ L)).val := by omega
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    rw [hval k (Finset.mem_range.mp hk)]

open Classical in
theorem trace_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  by_cases hd : p ^ (L - m) ∣ i
  · obtain ⟨j, hj⟩ := hd
    refine ⟨(ζ ^ p ^ (L - m)) ^ j, Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i = 1 := by rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    have h2 : ζ ^ i = (ζ ^ p ^ (L - m)) ^ j := by rw [hj, pow_mul]
    rw [h1, h2]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in
theorem trace_closure {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact trace_pow p L m hm1 hm ζ hζ τ hτ i
  | zero => exact ⟨0, Subring.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z1, h1, e1⟩ := hx
    obtain ⟨z2, h2, e2⟩ := hy
    exact ⟨z1 + z2, Subring.add_mem _ h1 h2, by simp only [map_add, Finset.sum_add_distrib, e1, e2]; ring⟩
  | neg x _ hx =>
    obtain ⟨z1, h1, e1⟩ := hx
    exact ⟨-z1, Subring.neg_mem _ h1, by simp only [map_neg, Finset.sum_neg_distrib, e1]; ring⟩

open Classical in

theorem normTrace_exists_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  intro Ω _ _ _ ε p hpf L m hm1 hm F hF
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := zt_prim ε p L hp.pos
  have hpow := zt_pow ε p L m hp.pos hm
  have hcop : ∀ a : (ZMod (p ^ L))ˣ, ((a : ZMod (p ^ L)).val).Coprime (p ^ L) := fun a => ZMod.val_coe_unit_coprime a
  choose τ hτ using fun a : (ZMod (p ^ L))ˣ => exists_aut (zt ε p L) (p ^ L) (pow_pos hp.pos _) hζ _ (hcop a)
  obtain ⟨D, hD, hDF⟩ := hF
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨z, hz, hT⟩ := trace_closure p L m hm1 hm (zt ε p L) hζ τ hτ _ hDF
  rw [hpow] at hz
  simp only [map_mul, map_natCast, ← Finset.mul_sum] at hT
  have hsum : ∀ σ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, σ a (zt ε p L) = zt ε p L ^ (a : ZMod (p ^ L)).val) →
      ∀ a, σ a F = τ a F := by
    intro σ hσ a
    have hagree : Set.EqOn ((σ a : Ω ≃+* Ω) : Ω →+* Ω) ((τ a : Ω ≃+* Ω) : Ω →+* Ω) (Subring.closure {zt ε p L}) := by
      apply RingHom.eqOn_set_closure
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      show σ a (zt ε p L) = τ a (zt ε p L)
      rw [hσ, hτ]
    have h2 : σ a ((D : Ω) * F) = τ a ((D : Ω) * F) := hagree hDF
    rw [map_mul, map_mul, map_natCast, map_natCast] at h2
    exact mul_left_cancel₀ hD0 h2
  have hE : (p : Ω) ^ (L - m) * (z / D) = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a F := by
    rw [← mul_div_assoc, ← hT, mul_div_cancel_left₀ _ hD0]
  refine ⟨z / D, ⟨τ, hτ, hE⟩, ⟨D, hD, ?_⟩, ?_⟩
  · have : (D : Ω) * (z / D) = z := by field_simp
    rw [this]; exact hz
  · rintro F'' ⟨σ, hσ, hF''⟩
    rw [Finset.sum_congr rfl (fun a _ => hsum σ hσ a), ← hE] at hF''
    exact mul_left_cancel₀ hpN hF''

end GlobalTheory.NTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClassStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eval_eq_kummer_class : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  first | exact @GlobalTheory.KZ.ES.exists_un_eval_eq_cls | exact GlobalTheory.KZ.ES.exists_un_eval_eq_cls | (intros; apply GlobalTheory.KZ.ES.exists_un_eval_eq_cls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  first | exact @GlobalTheory.FNRoots.main | exact GlobalTheory.FNRoots.main | (intros; apply GlobalTheory.FNRoots.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaPowers

theorem finiteIndex_stabilizer (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (x : Ω) :
    (MulAction.stabilizer (G ℚ Ω) x).FiniteIndex := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hsub : MulAction.orbit (G ℚ Ω) x ⊆ (minpoly ℚ x).rootSet Ω := by
    rintro _ ⟨σ, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[ℚ] Ω) x (minpoly ℚ x)
    rw [minpoly.aeval, map_zero] at e
    exact e
  have hfin : (MulAction.orbit (G ℚ Ω) x).Finite := ((minpoly ℚ x).rootSet_finite Ω).subset hsub
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact ((Set.ncard_pos hfin).mpr ⟨x, MulAction.mem_orbit_self x⟩).ne'

theorem cycMod_Ine_surjective (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) :
    Function.Surjective ((cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype) := by
  intro u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hs : Function.Surjective (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) :=
    ZMod.ringHom_surjective _
  haveI := IsLocalHom.of_surjective _ hs
  obtain ⟨v, hv⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hs this u
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
  refine ⟨⟨σ, hσ⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [cycMod, MonoidHom.comp_apply, hσv]
  exact hv

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
    ∀ F : Finset Ω, ∃ D : ℕ, 1 ≤ D ∧ ∀ (n : ℕ) (u : (ZMod (l ^ n))ˣ),
      ∃ s ∈ Ine (F := ℚ) A, (∀ x ∈ F, s x = x) ∧ cycMod ℚ Ω l n s = u ^ D := by
  intro l _ Ω _ _ _ A hA F
  let Fix : Subgroup (G ℚ Ω) := ⨅ x : F, MulAction.stabilizer (G ℚ Ω) (x : Ω)
  haveI : Fix.FiniteIndex :=
    Subgroup.finiteIndex_iInf fun x => finiteIndex_stabilizer Ω (x : Ω)
  let H : Subgroup (Ine (F := ℚ) A) := Fix.subgroupOf (Ine (F := ℚ) A)
  have hH0 : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨H.index, Nat.one_le_iff_ne_zero.mpr hH0, fun n u => ?_⟩
  set f := (cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype with hf
  have hsurj := cycMod_Ine_surjective l Ω A hA n
  have hdvd : (H.map f).index ∣ H.index := Subgroup.index_map_dvd H hsurj
  haveI : (H.map f).Normal := Subgroup.normal_of_comm _
  have hmem : u ^ H.index ∈ H.map f := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ u) _
  obtain ⟨h, hh, hfh⟩ := hmem
  refine ⟨h, h.2, fun x hx => ?_, hfh⟩
  have hfix : (h : G ℚ Ω) ∈ Fix := hh
  have := (Subgroup.mem_iInf.mp hfix) ⟨x, hx⟩
  exact this

end GlobalTheory.InertiaPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTower
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

def IsPowModP {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) (p : ℕ)
    (x : A) : Prop :=
  ∃ y ∈ S, ∃ z ∈ S, x = y ^ p + (p : A) * z

section Closure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {p : ℕ}

theorem isPthPowerModP_add (hp : p.Prime) {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x + x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨y, hy⟩ : S) ⟨y', hy'⟩
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  refine ⟨y + y', S.add_mem hy hy', z + z' - y * y' * r, ?_, ?_⟩
  · exact S.sub_mem (S.add_mem hz hz') (S.mul_mem (S.mul_mem hy hy') r.2)
  · rw [hr']; ring

theorem isPthPowerModP_mul {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x * x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  refine ⟨y * y', S.mul_mem hy hy', z * y' ^ p + y ^ p * z' + (p : A) * z * z', ?_, ?_⟩
  · refine S.add_mem (S.add_mem (S.mul_mem hz (S.pow_mem hy' _))
      (S.mul_mem (S.pow_mem hy _) hz')) (S.mul_mem (S.mul_mem ?_ hz) hz')
    exact S.natCast_mem p
  · ring

theorem isPthPowerModP_pow {y : A} (hy : y ∈ S) : IsPowModP S p (y ^ p) :=
  ⟨y, hy, 0, S.zero_mem, by ring⟩

theorem isPthPowerModP_zero (hp : p.Prime) : IsPowModP S p 0 :=
  ⟨0, S.zero_mem, 0, S.zero_mem, by rw [zero_pow hp.ne_zero]; ring⟩

theorem isPthPowerModP_add_p_mul {x h : A} (hx : IsPowModP S p x) (hh : h ∈ S) :
    IsPowModP S p (x + (p : A) * h) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hy, z + h, S.add_mem hz hh, by ring⟩

end Closure

theorem frob_surj_adjoin_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  intro p hp Ω _ _ T x hx
  set S := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) with hS
  have hpp : p.Prime := hp.out
  have hζ : ∀ n, T.ζ n ∈ S := fun n => Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hq : ∀ n, T.qq n ∈ S := fun n => Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  suffices IsPowModP S p x from this
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [← T.ζpow n]; exact isPthPowerModP_pow S (hζ _)
    · rw [← T.qpow n]; exact isPthPowerModP_pow S (hq _)
  | algebraMap r =>
    obtain ⟨g, h, rfl⟩ := GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p p r
    rw [map_add, map_sum, map_mul, map_natCast]
    refine isPthPowerModP_add_p_mul S ?_ ?_
    · refine Finset.sum_induction _ (IsPowModP S p) (fun a b ha hb => isPthPowerModP_add S hpp ha hb)
        (isPthPowerModP_zero S hpp) ?_
      intro j _
      have e : algebraMap (O0 p) Ω (qO p ^ (j : ℕ) * g j ^ p) =
          (T.qq 1 ^ (j : ℕ) * algebraMap (O0 p) Ω (g j)) ^ p := by
        rw [map_mul, map_pow, map_pow, ← T.q0, ← T.qpow 0, mul_pow, ← pow_mul, ← pow_mul, mul_comm p]
      rw [e]
      exact isPthPowerModP_pow S (S.mul_mem (S.pow_mem (hq 1) _) (S.algebraMap_mem _))
    · exact S.algebraMap_mem _
  | add x y _ _ hx hy => exact isPthPowerModP_add S hpp hx hy
  | mul x y _ _ hx hy => exact isPthPowerModP_mul S hx hy

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlaneStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  first | exact @GlobalTheory.KZ.gam_free | exact GlobalTheory.KZ.gam_free | (intros; apply GlobalTheory.KZ.gam_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaOneGammaZeroHomogeneousCocyclesFiniteStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  first | exact @GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | exact GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | (intros; apply GlobalTheory.KZ.BettiB.module_finite_z1_padicInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGaussStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_valuationSubring_unique_away_finset : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  first | exact @GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss | exact GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss | (intros; apply GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationExtensionUniqueBertiniNoether
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.T.exists_monic_irreducible_integral_primitive_element t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have conv : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) :=
    fun W h => ⟨h.1, fun P hP ⟨i, h0, hv, hinv⟩ => h.2 P hP ⟨i, hv, h0, hinv⟩⟩
  have key : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.T.valuationSubring_le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ (conv W₁ h₁) (conv W₂ h₂) (key W₁ (conv W₁ h₁)))
    (GlobalTheory.T.valuationSubring_le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ (conv W₂ h₂) (conv W₁ h₁) (key W₂ (conv W₂ h₂)))

end GlobalTheory.BertiniNoether
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruenceStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRat_conj_principal_congruence : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n), ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  first | exact @GlobalTheory.FN.exists_conj_principal_congruence | exact GlobalTheory.FN.exists_conj_principal_congruence | (intros; apply GlobalTheory.FN.exists_conj_principal_congruence <;> assumption)
end

