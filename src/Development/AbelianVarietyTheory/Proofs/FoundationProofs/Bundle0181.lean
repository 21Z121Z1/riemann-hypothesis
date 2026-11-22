import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishes
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.LamZero

theorem map_slP {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (Q : MvPolynomial (Fin 2) R) : MvPolynomial.map f (slP m Q) = slP m (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_coef_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (Q : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (c • Q) = f c • MvPolynomial.map f Q := by
  simp [MvPolynomial.smul_eq_C_mul]

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

theorem eq_zero_of_sum {k : ℕ} {v : Fin k → E} (hv : LinearIndependent ℤ_[l] v)
    (Q : Fin k → MvPolynomial (Fin 2) ℤ_[l])
    (h : ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) = 0) (a : Fin k) : Q a = 0 := by
  ext m
  have h1 := congrArg (MvPolynomial.coeff m) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
    smul_eq_mul] at h1
  have := Fintype.linearIndependent_iff.1 hv (fun a => MvPolynomial.coeff m (Q a)) (by
    simpa [Algebra.smul_def, mul_comm] using h1)
  simpa using this a

theorem exists_basis (hinj : Function.Injective (algebraMap ℤ_[l] E)) (S : Finset E) :
    ∃ (k : ℕ) (v : Fin k → E) (r : E → Fin k → ℤ_[l]), LinearIndependent ℤ_[l] v ∧
      ∀ x ∈ S, x = ∑ a, r x a • v a := by
  classical
  let L := Submodule.span ℤ_[l] (S : Set E)
  haveI : Module.Finite ℤ_[l] L := Module.Finite.span_finset _ _
  haveI : NoZeroSMulDivisors ℤ_[l] E := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h⟩
  haveI : Module.Free ℤ_[l] L := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] L
  refine ⟨_, fun a => (b a : E), fun x => if h : x ∈ L then b.repr ⟨x, h⟩ else 0, ?_, ?_⟩
  · exact b.linearIndependent.map' L.subtype (by simp)
  · intro x hx
    have hxL : x ∈ L := Submodule.subset_span hx
    have h2 : ((∑ i, (b.repr ⟨x, hxL⟩) i • b i : L) : E) = x := congrArg Subtype.val (b.sum_repr _)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    simp only [dif_pos hxL]
    exact h2.symm

theorem poly_decomp {k : ℕ} (v : Fin k → E) (r : E → Fin k → ℤ_[l]) (P : MvPolynomial (Fin 2) E)
    (hr : ∀ m ∈ P.support, P.coeff m = ∑ a, r (P.coeff m) a • v a) :
    ∃ Q : Fin k → MvPolynomial (Fin 2) ℤ_[l], P = ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (Q a) := by
  classical
  refine ⟨fun a => ∑ m ∈ P.support, MvPolynomial.monomial m (r (P.coeff m) a), ?_⟩
  ext n
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_monomial,
    smul_eq_mul, map_sum]
  by_cases hn : n ∈ P.support
  · simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_pos hn]
    refine (hr n hn).trans ?_
    simp [Algebra.smul_def, mul_comm]
  · rw [MvPolynomial.notMem_support_iff.1 hn]
    simp only [apply_ite (algebraMap ℤ_[l] E), map_zero, Finset.sum_ite_eq', if_neg hn, mul_zero,
      Finset.sum_const_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]

theorem sum_reorg {n k : ℕ} (f : Fin n → E) (v : Fin k → E) (c : Fin n → Fin k → ℤ_[l])
    (hf : ∀ i, f i = ∑ a, c i a • v a) (F : Fin n → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (∑ i, c i a • F i) =
      ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i) := by
  simp only [map_sum, map_coef_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf i, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Algebra.smul_def]
  exact mul_comm _ _

theorem sum_slP {k : ℕ} (v : Fin k → E) (m : Matrix (Fin 2) (Fin 2) ℤ) (A B : Fin k → MvPolynomial (Fin 2) ℤ_[l]) :
    ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (slP m (A a) - B a) =
      slP m (∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (A a)) -
        ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (B a) := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, RingHom.map_sub, map_slP, smul_sub]

theorem tmul_sum_zero {M : Type} [AddCommGroup M] [Module ℤ_[l] M] {n k : ℕ} (f : Fin n → E) (v : Fin k → E)
    (c : Fin n → Fin k → ℤ_[l]) (hf : ∀ i, f i = ∑ a, c i a • v a) (b : Fin n → M)
    (hb : ∀ a, ∑ i, c i a • b i = 0) : ∑ i, f i ⊗ₜ[ℤ_[l]] b i = 0 := by
  have : ∀ i, f i ⊗ₜ[ℤ_[l]] b i = ∑ a, v a ⊗ₜ[ℤ_[l]] (c i a • b i) := by
    intro i
    rw [hf i, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← TensorProduct.tmul_sum, hb a, TensorProduct.tmul_zero]

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3.LamZero

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem rel_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n : ℕ} (b : Fin n → X.Fn l)
    (F : Fin n → ℂ → MvPolynomial (Fin 2) ℤ_[l]) (hR : ∀ j, Rel X l (b j) (F j)) (c : Fin n → ℤ_[l]) :
    Rel X l (∑ j, c j • b j) (∑ j, c j • F j) := by
  obtain ⟨hadd, hzero, hsmul, -, -⟩ := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have : ∀ s : Finset (Fin n), Rel X l (∑ j ∈ s, c j • b j) (∑ j ∈ s, c j • F j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact hadd _ _ _ _ (hsmul _ _ _ (hR j)) ih
  exact this Finset.univ

end GlobalTheory.KZ.H3.LamZero

namespace GlobalTheory.KZ.H3

open LamZero in

theorem lam_fst_eq_zero_of_triv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  intro Ω _ _ ε X l _ E _ _ hinj w Γ M₀ hM₀ hΓ p hp hT
  classical
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hp
  choose b F hRel hg using fun i => (g i).2
  obtain ⟨ψ, P, hψ, hP⟩ := hT
  obtain ⟨k, v, r, hv, hr⟩ := exists_basis hinj (Finset.univ.image f ∪ P.support.image (fun m => P.coeff m))
  have hf : ∀ i, f i = ∑ a, r (f i) a • v a := fun i =>
    hr _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  obtain ⟨Q, hQ⟩ := poly_decomp v r P (fun m hm =>
    hr _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)))
  let c : Fin n → Fin k → ℤ_[l] := fun i a => r (f i) a
  let G : Fin k → ℂ → MvPolynomial (Fin 2) ℤ_[l] := fun a z => ∑ i, c i a • F i z
  have hp1 : p.1 = ∑ i, f i ⊗ₜ[ℤ_[l]] b i := by
    rw [← hfg]
    simp [Prod.fst_sum, hg, TensorProduct.smul_tmul']
  have hp2 : ∀ z, p.2 z = ∑ i, f i • MvPolynomial.map (algebraMap ℤ_[l] E) (F i z) := by
    intro z
    rw [← hfg]
    simp [Prod.snd_sum, Finset.sum_apply, hg]
  have hkey : ∀ z, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a z) = p.2 z := fun z =>
    (sum_reorg f v c hf (fun i => F i z)).trans (hp2 z).symm
  have e1 : ∀ y, ∑ a, v a • MvPolynomial.map (algebraMap ℤ_[l] E) (G a y - Q a) = p.2 y - P := by
    intro y
    simp only [RingHom.map_sub, smul_sub, Finset.sum_sub_distrib, hkey, ← hQ]
  have hGT : ∀ a, (fun z => G a z) ∈ Triv ℤ_[l] w Γ := by
    intro a
    refine ⟨fun z => G a z - Q a, Q a, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have hγz : mob (ofSL γ) z ∈ Hs := GlobalTheory.KZ.MobLaws.mob_mem _ hz
    have h0 := eq_zero_of_sum hv (fun a => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (G a (mob (ofSL γ) z) - Q a) -
      (G a z - Q a)) (by
        rw [sum_slP, e1, e1, hP _ hγz, hP _ hz, add_sub_cancel_right, add_sub_cancel_right, hψ γ hγ z hz, sub_self]) a
    exact sub_eq_zero.1 h0
  have hb : ∀ a, ∑ i, c i a • b i = 0 := by
    intro a
    have hR := rel_sum X l b F hRel (fun i => c i a)
    have hG : (∑ i, c i a • F i) = fun z => G a z := by
      funext z; simp [G, Finset.sum_apply]
    rw [hG] at hR
    exact GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero Ω ε X l w Γ M₀ hM₀ hΓ _ _ hR (hGT a)
  rw [hp1]
  exact tmul_sum_zero f v c hf b hb

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycle
section
open GlobalTheory.NeedB Polynomial

noncomputable section

open IntermediateField

namespace GlobalTheory.Hilbert90CupCoboundary

theorem isLocallyConstant_eval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (τ : Ω) : IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g τ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮τ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral τ)
  have hopen : IsOpen ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfτ : (g⁻¹ * g') τ = τ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' τ
        (IntermediateField.mem_adjoin_simple_self K τ)
    have e : g' = g * (g⁻¹ * g') := by group
    show g' τ = g τ
    rw [e, AlgEquiv.mul_apply, hfτ]

theorem zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN0 hζ hfix c v hv hcoc
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let u : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => v g ^ N
  have hu_lc : IsLocallyConstant u := hv.comp (fun x : Ωˣ => x ^ N)
  have hu_coc : ∀ g h, ((u (g * h) : Ωˣ) : Ω) = u g * g (u h) := by
    intro g h
    simp only [u, Units.val_pow_eq_pow_val, map_pow]
    rw [← mul_pow, hcoc g h, mul_pow, ← pow_mul, mul_comm (c g h).val N, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle K Ω u hu_lc hu_coc
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (t : Ω) hN0
  have ht0 : (t : Ω) ≠ 0 := t.ne_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne'] at hτ
    exact ht0 hτ.symm
  have hgτ0 : ∀ g : Ω ≃ₐ[K] Ω, g τ ≠ 0 := fun g => (map_ne_zero g).2 hτ0
  let w : (Ω ≃ₐ[K] Ω) → Ω := fun g => (v g : Ω) * τ / g τ
  have hw_lc : IsLocallyConstant w :=
    (hv.comp (fun x : Ωˣ => (x : Ω))).comp₂ (isLocallyConstant_eval (K := K) τ) (fun a b => a * τ / b)
  have hw_pow : ∀ g, w g ^ N = 1 := by
    intro g
    have h1 : (v g : Ω) ^ N = g t / t := by rw [← Units.val_pow_eq_pow_val]; exact ht g
    have h2 : (g τ) ^ N = g t := by rw [← map_pow, hτ]
    have h3 : g (t : Ω) ≠ 0 := (map_ne_zero g).2 ht0
    simp only [w]
    rw [div_pow, mul_pow, h1, h2, hτ]
    field_simp
  have hw_coc : ∀ g h, w g * g (w h) = ζ ^ (c g h).val * w (g * h) := by
    intro g h
    have hghτ : g (h τ) ≠ 0 := (map_ne_zero g).2 (hgτ0 h)
    have hg := hgτ0 g
    have e1 : w g * g (w h) = ((v g : Ω) * g (v h)) * τ / g (h τ) := by
      simp only [w, map_div₀, map_mul]
      field_simp
    rw [e1, hcoc g h]
    simp only [w, AlgEquiv.mul_apply]
    ring
  let E : Ω → ZMod N := fun x => if hx : ∃ i : ZMod N, ζ ^ i.val = x then hx.choose else 0
  let η : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => E (w g)
  have hη : ∀ g, ζ ^ (η g).val = w g := by
    intro g
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (hw_pow g)
    have hex : ∃ j : ZMod N, ζ ^ j.val = w g := ⟨(i : ZMod N), by rw [ZMod.val_cast_of_lt hi, hi']⟩
    simp only [η, E, dif_pos hex]
    exact hex.choose_spec
  refine ⟨η, hw_lc.comp E, ?_⟩
  intro g h
  have key : ζ ^ (η g + η h).val = ζ ^ (c g h + η (g * h)).val := by
    rw [KumLemma.pow_val_add hζ, KumLemma.pow_val_add hζ, hη g, hη h, hη (g * h)]
    have : g (w h) = w h := by rw [← hη h, map_pow, hfix]
    rw [← hw_coc, this]
  have hinj : η g + η h = c g h + η (g * h) :=
    ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) key)
  linear_combination -hinj

end GlobalTheory.Hilbert90CupCoboundary
end
end

