import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationSplitKaehlerDSmoothStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_split_kaehlerD_smooth : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  first | exact @GlobalTheory.bertini_derivation_split | exact GlobalTheory.bertini_derivation_split | (intros; apply GlobalTheory.bertini_derivation_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationsDualToFamilyOfNilpotentAugStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.derivation_normalise_family | exact GlobalTheory.derivation_normalise_family | (intros; apply GlobalTheory.derivation_normalise_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparatingStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_ne_zero_of_separating_functionals : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  first | exact @GlobalTheory.exists_det_ne_zero_of_rows_separating | exact GlobalTheory.exists_det_ne_zero_of_rows_separating | (intros; apply GlobalTheory.exists_det_ne_zero_of_rows_separating <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulStdBlockStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_one_mul_stdBlock' : ∀ {K : Type} [Field K] {n r : ℕ}, r < n → ∀ y : Matrix (Fin n) (Fin r) K, y.rank = r → ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  first | exact @GlobalTheory.exists_det_one_mul_stdBlock | exact GlobalTheory.exists_det_one_mul_stdBlock | (intros; apply GlobalTheory.exists_det_one_mul_stdBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHomStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowerEval_twoVars_ringHom : ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  first | exact @GlobalTheory.dpEval_two | exact GlobalTheory.dpEval_two | (intros; apply GlobalTheory.dpEval_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinsetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominating_dvr_containing_finset : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  first | exact @GlobalTheory.DomDVR.exists_dominating_dvr | exact GlobalTheory.DomDVR.exists_dominating_dvr | (intros; apply GlobalTheory.DomDVR.exists_dominating_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingLocalDomainEqMulMaximalStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧ (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  first | exact @GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | exact GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | (intros; apply GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form : ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  first | exact @GlobalTheory.exists_dvd_coords_of_definite_form | exact GlobalTheory.exists_dvd_coords_of_definite_form | (intros; apply GlobalTheory.exists_dvd_coords_of_definite_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocus
section
open GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.LocDivEtale

open IsLocalRing

theorem span_singleton_eq_maximalIdeal_pow {L : Type} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] (π : L)
    (hπ : maximalIdeal L = Ideal.span {π}) (x : L) (hx : x ≠ 0) :
    ∃ n : ℕ, Ideal.span {x} = maximalIdeal L ^ n := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal L) (maximalIdeal.isMaximal L).ne_top
  have hex : ∃ n, x ∉ maximalIdeal L ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ i, maximalIdeal L ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp
      | succ k => exact h k
    rw [hK] at this; exact this
  obtain ⟨n, hn, hn'⟩ : ∃ n, x ∉ maximalIdeal L ^ (n + 1) ∧ x ∈ maximalIdeal L ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  clear hex
  refine ⟨n, ?_⟩
  rw [hπ, Ideal.span_singleton_pow] at hn' hn ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hn'
  have hyu : IsUnit y := by
    by_contra hy'
    apply hn
    have : y ∈ maximalIdeal L := (mem_maximalIdeal _).2 hy'
    rw [hπ] at this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    rw [Ideal.mem_span_singleton']
    exact ⟨z, by rw [← hy, ← hz]; ring⟩
  rw [← hy]
  exact Ideal.span_singleton_mul_left_unit hyu _

theorem exists_local_uniformizer (B : Type) [CommRing B] [IsDedekindDomain B] (m : Ideal B) [m.IsPrime]
    (hm0 : m ≠ ⊥) : ∃ π ∈ m, ∀ b ∈ m, ∃ t ∉ m, ∃ c : B, t * b = π * c := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime m)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj m.primeCompl ϖ
  simp only at hπt
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨π, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m, ← hπt]
    exact Ideal.mul_mem_right _ _ (hϖ.not_isUnit)
  · intro b hb
    have hb' : algebraMap B (Localization.AtPrime m) b ∈ maximalIdeal (Localization.AtPrime m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m b).2 hb
    rw [hmax] at hb'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb'
    obtain ⟨⟨c, u⟩, hcu⟩ := IsLocalization.surj m.primeCompl z
    simp only at hcu
    have heq : algebraMap B (Localization.AtPrime m) (b * (t * u)) =
        algebraMap B (Localization.AtPrime m) (π * c) := by
      rw [map_mul, map_mul, map_mul, ← hz, ← hπt, ← hcu]; ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists m.primeCompl (Localization.AtPrime m)).1 heq
    refine ⟨w * (t * u), ?_, w * c, ?_⟩
    · exact (m.primeCompl).mul_mem w.2 ((m.primeCompl).mul_mem t.2 u.2)
    · rw [show (w : B) * (t * u) * b = w * (b * (t * u)) by ring, hw]; ring

theorem exists_dvd_mul_pow : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A']
    [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal →
    algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  intro B A' _ _ _ _ _ f hf hN a ha M hM hfM
  classical
  set m : Ideal B := M.comap (algebraMap B A') with hm_def
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hfm : f ∈ m := hfM
  have hm0 : m ≠ ⊥ := by
    intro h; apply hf
    rw [h] at hfm; exact (Submodule.mem_bot _).1 hfm
  obtain ⟨π, hπm, hπ⟩ := exists_local_uniformizer B m hm0
  let L := Localization.AtPrime M
  haveI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing M.primeCompl L inferInstance
  let φ : B →+* L := (algebraMap A' L).comp (algebraMap B A')
  have hmem : ∀ b ∈ m, φ b ∈ Ideal.span {φ π} := by
    intro b hb
    obtain ⟨t, ht, c, htc⟩ := hπ b hb
    have hu : IsUnit (φ t) := IsLocalization.map_units L (⟨algebraMap B A' t, ht⟩ : M.primeCompl)
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, htc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmax : maximalIdeal L = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := hN.1 x
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
      have hbm : b ∈ m := by
        show algebraMap B A' b ∈ M
        have : algebraMap B A' b = x - c * algebraMap B A' f := by rw [hc]; ring
        rw [this]; exact M.sub_mem hx (M.mul_mem_left _ hfM)
      have hx' : x = algebraMap B A' b + c * algebraMap B A' f := by rw [hc]; ring
      show algebraMap A' L x ∈ Ideal.span {φ π}
      rw [hx', map_add, map_mul]
      exact Ideal.add_mem _ (hmem b hbm) (Ideal.mul_mem_left _ _ (hmem f hfm))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hπm
  have ha0 : algebraMap A' L a ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl L a).1 h
    have : (s : A') = 0 := (mem_nonZeroDivisors_iff.1 ha).2 _ hs
    exact s.2 (this ▸ M.zero_mem)
  obtain ⟨n, hn⟩ := span_singleton_eq_maximalIdeal_pow (φ π) hmax _ ha0
  have hfL : φ f ^ n ∈ Ideal.span {algebraMap A' L a} := by
    rw [hn]; exact Ideal.pow_mem_pow ((IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hfM) n
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hfL
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj M.primeCompl z
  simp only at hys
  have heq : algebraMap A' L (algebraMap B A' f ^ n * s) = algebraMap A' L (y * a) := by
    rw [map_mul, map_mul, map_pow, ← hys]
    show φ f ^ n * _ = _
    rw [← hz]; ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M.primeCompl L).1 heq
  refine ⟨w * s, (M.primeCompl).mul_mem w.2 s.2, n, w * y, ?_⟩
  rw [show (w : A') * s * algebraMap B A' f ^ n = w * (algebraMap B A' f ^ n * s) by ring, hw]; ring

end GlobalTheory.LocDivEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionOfEssentiallyEtaleLocal
section
open TensorProduct IsLocalRing

namespace GlobalTheory

theorem tensorLift_injective_of_flat {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  let fK : K →ₐ[R] L := { toRingHom := f, commutes' := hf }
  let H : K ⊗[R] S →ₐ[R] L :=
    Algebra.TensorProduct.lift fK (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  have hH : ∀ k s, H (k ⊗ₜ s) = f k * algebraMap S L s := fun k s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hgH : ∀ x, g x = H (LinearMap.rTensor S i.toLinearMap x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hH]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hloc : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K S 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R S K)
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hHinj : Function.Injective H := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K S 1) y
    have hs : s = 0 := by
      have h1 : H (r • y) = 0 := by
        rw [Submonoid.smul_def, show H (r.1 • y) = r.1 • H y from H.toLinearMap.map_smul r.1 y, hy, smul_zero]
      rw [hr, TensorProduct.mk_apply, hH, map_one, one_mul] at h1
      exact IsFractionRing.injective S L (h1.trans (map_zero _).symm)
    have ha : algebraMap R K r.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have h2 : algebraMap R K r.1 • y = 0 := by
      rw [algebraMap_smul, ← Submonoid.smul_def, hr, hs, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    rw [← one_smul K y, ← inv_mul_cancel₀ ha, mul_smul, h2, smul_zero]
  intro x y hxy
  rw [hgH, hgH] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := S) i.toLinearMap hi (hHinj hxy)

def rangeValuationSubring {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L]
    (j : B →+* L) (hj : ∀ x : L, ∃ a b : B, j b ≠ 0 ∧ x = j a / j b) : ValuationSubring L where
  toSubring := j.range
  mem_or_inv_mem' x := by
    obtain ⟨a, b, hb, rfl⟩ := hj x
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · right
      have ha : j a ≠ 0 := fun h => hb (by rw [← hc, map_mul, h, zero_mul])
      exact ⟨c, by rw [inv_div, ← hc, map_mul, mul_div_cancel_left₀ _ ha]⟩
    · left
      exact ⟨c, by rw [← hc, map_mul, mul_div_cancel_left₀ _ hb]⟩

theorem exists_valuationSubring_extend_of_formallyEtale : ∀ {K K' R S : Type} [Field K] [Field K']
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K]
    [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S)
    [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType →
    φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K,
    IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) →
    ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧
      (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧
      (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  intro K K' R S _ _ _ _ _ _ _ _ _ _ _ _ φ σ _ hfl het hef hc V hV hRV
  letI : Algebra R S := σ.toAlgebra
  haveI : Module.Flat R S := hfl
  haveI : Algebra.FormallyEtale R S := het
  haveI : Algebra.EssFiniteType R S := hef
  haveI : IsLocalHom (algebraMap R S) := ‹IsLocalHom σ›
  haveI : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  letI : Algebra R V := ((algebraMap R K).codRestrict V hRV).toAlgebra
  letI : Algebra R K' := ((algebraMap S K').comp σ).toAlgebra
  haveI : IsScalarTower R S K' := .of_algebraMap_eq fun _ => rfl
  let fV : V →ₐ[R] K' := { toRingHom := φ.comp V.subtype, commutes' := fun r => RingHom.congr_fun hc r }
  let iV : V →ₐ[R] K := { toRingHom := V.subtype, commutes' := fun _ => rfl }
  let g : V ⊗[R] S →ₐ[R] K' :=
    Algebra.TensorProduct.lift fV (IsScalarTower.toAlgHom R S K') (fun _ _ => Commute.all _ _)
  have hg' : ∀ (a : V) (s : S), g (a ⊗ₜ s) = φ a * algebraMap S K' s := fun a s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hg1 : ∀ s : S, g (1 ⊗ₜ s) = algebraMap S K' s := fun s => by
    rw [hg']; simp
  have hg : Function.Injective g :=
    tensorLift_injective_of_flat (S := S) (L := K') iV Subtype.val_injective φ (RingHom.congr_fun hc) g.toRingHom hg'
  let C := V ⊗[R] S
  haveI : IsDomain C := Function.Injective.isDomain g.toRingHom hg
  obtain ⟨⟨Q, hQ⟩, hQm⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := C)
    ⟨maximalIdeal V, inferInstance⟩
  have hQm' : Q.comap (algebraMap V C) = maximalIdeal V := congrArg PrimeSpectrum.asIdeal hQm
  let B := Localization.AtPrime Q
  haveI : Module.Flat V B := Module.Flat.trans V C B
  haveI : Algebra.EssFiniteType V B := .comp V C B
  haveI : Algebra.FormallyEtale V B := .comp V C B
  have hQB : ∀ c : C, IsUnit (algebraMap C B c) ↔ c ∉ Q := fun c =>
    IsLocalization.AtPrime.isUnit_to_map_iff B Q c
  haveI : IsLocalHom (algebraMap V B) := ⟨fun v hv => by
    by_contra hn
    have h1 : algebraMap V C v ∈ Q := by rw [← Ideal.mem_comap, hQm']; exact hn
    rw [IsScalarTower.algebraMap_apply V C B] at hv
    exact (hQB _).mp hv h1⟩
  obtain ⟨_, hB⟩ := exists_isDiscreteValuationRing_of_unramified V B
  have hunit : ∀ y : Q.primeCompl, IsUnit (g.toRingHom y) := fun y => by
    refine Ne.isUnit fun h0 => y.2 ?_
    rw [hg (h0.trans (map_zero g).symm)]
    exact Q.zero_mem
  let j : B →+* K' := IsLocalization.lift (M := Q.primeCompl) (S := B) hunit
  have hjC : ∀ c, j (algebraMap C B c) = g c := IsLocalization.lift_eq (M := Q.primeCompl) (S := B) hunit
  have hj : Function.Injective j := IsLocalization.injective_of_map_algebraMap_zero (M := Q.primeCompl) B j fun x hx => by
    rw [hjC] at hx
    rw [hg (hx.trans (map_zero g).symm), map_zero]
  have hgen : ∀ x : K', ∃ a b : B, j b ≠ 0 ∧ x = j a / j b := fun x => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    refine ⟨algebraMap C B (1 ⊗ₜ a), algebraMap C B (1 ⊗ₜ b), ?_, ?_⟩
    · rw [hjC, hg1]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [hjC, hjC, hg1, hg1]
  let V' := rangeValuationSubring j hgen
  have hVV' : ∀ x ∈ V, φ x ∈ V' := fun x hx =>
    ⟨algebraMap C B (⟨x, hx⟩ ⊗ₜ 1), by rw [hjC, hg', map_one, mul_one]⟩
  let e₀ : B →+* V' := j.codRestrict V' fun b => ⟨b, rfl⟩
  have he₀ : Function.Bijective e₀ :=
    ⟨fun a b h => hj (congrArg Subtype.val h), fun y => by
      obtain ⟨b, hb⟩ := y.2
      exact ⟨b, Subtype.ext hb⟩⟩
  let e : B ≃+* V' := RingEquiv.ofBijective e₀ he₀
  have he : ∀ b, (e b : K') = j b := fun _ => rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have htQ : algebraMap V C t ∈ Q := by
    rw [← Ideal.mem_comap, hQm']
    exact (mem_maximalIdeal _).mpr ht.not_isUnit
  have htB : ¬ IsUnit (algebraMap C B (algebraMap V C t)) := fun h => (hQB _).mp h htQ
  have hφt : φ t ≠ 0 := by
    rw [map_ne_zero]
    exact fun h => ht.ne_zero (Subtype.ext h)
  have hjt : j (algebraMap C B (algebraMap V C t)) = φ t := by
    rw [hjC, Algebra.TensorProduct.algebraMap_apply, hg']
    simp
  have key : (φ t)⁻¹ ∉ V' := by
    rintro ⟨b, hb⟩
    refine htB (IsUnit.of_mul_eq_one b (hj ?_))
    rw [map_mul, hb, map_one, hjt, mul_inv_cancel₀ hφt]
  refine ⟨V', hVV', ?_, fun b => ⟨algebraMap C B (1 ⊗ₜ b), by rw [hjC, hg1]⟩, ?_, ?_⟩
  · obtain ⟨b, hbm, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field B)
    exact
      { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
        toIsLocalRing := inferInstance
        not_a_field' := fun h => by
          have h1 : e b ∈ maximalIdeal V' := fun hu => hbm (by simpa using hu.map e.symm.toRingHom)
          rw [h] at h1
          exact hb0 (e.injective (by simpa using h1)) }
  · intro x hx
    by_contra hxV
    have hinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x⁻¹, hinv⟩ : V)) (fun h => inv_ne_zero hx0 (congrArg Subtype.val h)) ht
    have hn' : x⁻¹ = (u : K) * (t : K) ^ n := congrArg Subtype.val hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hxV ?_)
      have h2 : ((u : V) : K) * (((u⁻¹ : Vˣ) : V) : K) = 1 := by
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have hn0 : x⁻¹ = (u : K) := by rw [hn', h0, pow_zero, mul_one]
      have : x = (((u⁻¹ : Vˣ) : V) : K) := by
        rw [← inv_inv x, hn0]
        exact inv_eq_of_mul_eq_one_right h2
      exact this ▸ Subtype.property _
    apply key
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have : (φ t)⁻¹ = φ ((t ^ m * u : V) : K) * φ x := by
      rw [← map_inv₀, ← map_mul]
      congr 1
      have hu0 : ((u : V) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
      have hx' : x = ((u : K) * (t : K) ^ (m + 1))⁻¹ := by rw [← hn', inv_inv]
      rw [hx']
      push_cast
      field_simp
      ring
    rw [this]
    exact mul_mem (hVV' _ (t ^ m * u : V).2) hx
  · letI : Algebra V V' := (φ.restrict V V' hVV').toAlgebra
    let eA : B ≃ₐ[V] V' := AlgEquiv.ofRingEquiv (f := e) fun v => Subtype.ext (by
      rw [he, IsScalarTower.algebraMap_apply V C B, hjC, Algebra.TensorProduct.algebraMap_apply,
        hg']
      simp
      rfl)
    exact ⟨Algebra.FormallyEtale.of_equiv eA, Algebra.EssFiniteType.of_surjective eA.toAlgHom eA.surjective⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRankStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq : ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q] (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ → (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R, ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) (Fintype.linearCombination R (b ∘ σ))) := by
  first | (exact @GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (exact GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (intros; apply GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimes
section
open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace GlobalTheory

theorem integral_of_forall_height_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      (t : FractionRing R),
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧
        t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) →
      ∃ a : R, algebraMap R (FractionRing R) a = t := by
  intro R _ _ _ _ t h
  exact ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (K := FractionRing R) t
    (fun p hp h1 => @h p hp h1)

end GlobalTheory
end

