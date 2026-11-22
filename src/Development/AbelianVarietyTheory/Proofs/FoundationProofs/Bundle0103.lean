import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuation
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KronRatio

open GlobalTheory.KroneckerCongruence

variable {Ω : Type} [Field Ω]

theorem mem_of_isIntegral_int (V : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).1 h
  rw [← hy]; exact y.2

theorem valuation_natCast_eq_one (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) (hD : ¬ q ∣ D) : V.valuation (D : Ω) = 1 := by
  have hcop : IsCoprime (q : ℤ) (D : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 hD
  obtain ⟨a, b, hab⟩ := hcop
  have hle : ∀ n : ℤ, V.valuation (n : Ω) ≤ 1 := fun n => (V.valuation_le_one_iff _).2 (intCast_mem V n)
  have hq1 : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.1 hqV
  by_contra hne
  have hD1 : V.valuation (D : Ω) < 1 := lt_of_le_of_ne ((V.valuation_le_one_iff _).2 (natCast_mem V D)) hne
  have h1 : (1 : Ω) = (a : Ω) * (q : Ω) + (b : Ω) * (D : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this.symm
  have h2 : V.valuation (1 : Ω) < 1 := by
    rw [h1]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hq1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hD1
  simp at h2

theorem mem_of_bdd (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime) (hqV : ((q : ℕ) : Ω) ∈ V.nonunits)
    (hD : ¬ q ∣ D) {a : Ω} (h : ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * a)) : a ∈ V := by
  obtain ⟨k, hk⟩ := h
  have h1 := mem_of_isIntegral_int V hk
  have hv := valuation_natCast_eq_one V hq hqV hD
  rw [← V.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, map_pow, hv, one_pow, one_mul] at h1

theorem coeff_mul_mem (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V)
    (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V := by
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_pow_mem (V : ValuationSubring Ω) (x : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V) (n : ℕ)
    (r : ℚ) : (x ^ n).coeff r ∈ V := by
  have he : x ^ n = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx ^ n) := by
    rw [map_pow, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_mul_mem_nonunits (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω)
    (hx : ∀ r, x.coeff r ∈ V.nonunits) (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V.nonunits := by
  have hx' : ∀ r, x.coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hx r)))
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ z : V, ρ z = 0 ↔ V.valuation (z : Ω) < 1 := fun z => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hX : hahnSeriesCoeffRingHomMap ρ (liftV V x hx') = 0 := by
    ext t
    rw [hahnSeriesCoeffRingHomMap_coeff]
    exact (hρ0 _).2 (V.mem_nonunits_iff.1 (hx t))
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx' * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 ((liftV V x hx' * liftV V y hy).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, map_mul, hX, zero_mul]
  rfl

end GlobalTheory.KronRatio

namespace GlobalTheory.KZ

open GlobalTheory.KroneckerCongruence GlobalTheory.KronRatio in

theorem kronecker_ratio_reduces_to_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  intro Ω _ _ _ ε X hε hj M f hM hf
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let F : SL(2, ZMod M) → X.K := fun τ =>
    if h : ∃ σ, red σ = τ then X.sl (ofSL h.choose) (f : X.K) else (f : X.K)
  have hF : ∀ σ : SL(2, ℤ), X.sl (ofSL σ) (f : X.K) = F (red σ) := by
    intro σ
    have h : ∃ σ', red σ' = red σ := ⟨σ, rfl⟩
    have e : F (red σ) = X.sl (ofSL h.choose) (f : X.K) := dif_pos h
    have hσ' : red h.choose = red σ := h.choose_spec
    have hγ : σ * h.choose⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      have : σ * h.choose⁻¹ ∈ red.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ', mul_inv_cancel]
      exact this
    rw [e]
    calc X.sl (ofSL σ) (f : X.K) = X.sl (ofSL (σ * h.choose⁻¹ * h.choose)) (f : X.K) := by
          rw [inv_mul_cancel_right]
      _ = X.sl (ofSL h.choose) (X.sl (ofSL (σ * h.choose⁻¹)) (f : X.K)) := by rw [map_mul, X.sl_mul]
      _ = _ := by rw [hf _ hγ]
  choose D hD0 hD using X.bdd
  let P : X.K → Finset ℕ := fun g => (D g).primeFactors ∪ (D g⁻¹).primeFactors
  refine ⟨M.primeFactors ∪ P f ∪ Finset.univ.biUnion (fun τ => P (F τ)), ?_⟩
  intro q hq hqS V s hqV hs σ hσ W hW hdom
  have hn : ∀ h : X.K, q ∉ (D h).primeFactors → ∀ r, (X.exp h).coeff r ∈ V := fun h hh r =>
    mem_of_bdd V hq hqV (fun hd => hh (Nat.mem_primeFactors.2 ⟨hq, hd, (hD0 h).ne'⟩)) (hD h r)
  have hint : ∀ g : X.K, q ∉ P g → (∀ r, (X.exp g).coeff r ∈ V) ∧ (∀ r, (X.exp g⁻¹).coeff r ∈ V) := fun g hg =>
    ⟨hn g fun h => hg (Finset.mem_union_left _ h), hn _ fun h => hg (Finset.mem_union_right _ h)⟩
  have hqM : q ∉ M.primeFactors := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hqf : q ∉ P f := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hqF : q ∉ P (F (red σ)) := fun h =>
    hqS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  obtain ⟨hf1, hf2⟩ := hint _ hqf
  rw [← hF σ] at hqF
  obtain ⟨hs1, hs2⟩ := hint _ hqF
  have hcop : Nat.Coprime q M :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  have hK := kronecker_congruence_tower ε X hε hj M q (f : X.K) hM hq hcop hf σ ⟨hσ.2.1, hσ.2.2⟩ V s hqV hs hf1 hs1
  refine ⟨1, one_ne_zero, ?_⟩
  generalize (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
    X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = A at hK ⊢
  have hB0 : X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 f.ne_zero)
      (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero _).2 f.ne_zero)))
  have hBinv : ∀ r, (X.exp (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q)⁻¹).coeff r ∈ V := by
    intro r
    rw [mul_inv, ← inv_pow, ← map_inv₀, ← map_inv₀ (X.gal s.symm), map_mul, map_pow]
    refine coeff_mul_mem V _ _ (fun t => ?_) (coeff_pow_mem V _ (fun t => ?_) q) r
    · rw [X.gal_exp]; exact (hs _ (hf2 t)).1
    · rw [X.gal_exp]; exact (hs _ (hs2 t)).2.1
  generalize X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q = B at hK hB0 hBinv ⊢
  have hge : algebraMap Ω X.K 1 * A / B - 1 = (A - B) * B⁻¹ := by
    rw [map_one, one_mul]; field_simp
  rw [hge]
  have hgc : ∀ r, (X.exp ((A - B) * B⁻¹)).coeff r ∈ V.nonunits := by
    intro r; rw [map_mul]; exact coeff_mul_mem_nonunits V _ _ hK hBinv r
  generalize (A - B) * B⁻¹ = g at hgc ⊢
  have hgV : ∀ r, (X.exp g).coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hgc r)))
  have h1 := hdom g hgV fun r _ => hgc r
  have hcV := V.mem_nonunits_iff.1 (hgc 0)
  have hcm := hgV 0
  generalize (X.exp g).coeff 0 = c at h1 hcV hcm
  have h2 : W.valuation (algebraMap Ω X.K c) < 1 := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact zero_lt_one
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 ((hW c).2 hcm)) fun heq => ?_
    have hinv : algebraMap Ω X.K c⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have h3 : V.valuation c⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 ((hW _).1 hinv)
    have h4 : V.valuation (c⁻¹ * c) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) hcV
    rw [inv_mul_cancel₀ hc0, map_one] at h4
    exact lt_irrefl _ h4
  have h5 := lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt h1 h2)
  rwa [sub_add_cancel] at h5

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsion
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem rootOfUnity_eq_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

theorem khat_no_l_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  intro Ω _ _ _ ε X l _ x hx
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, hker, hmul, hone, -, -, -⟩ := H3.cls_props Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, hred⟩ := H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_eq_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

end GlobalTheory.KZ.BettiB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadius
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_approx_critical : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) →
    ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  intro L _ v p hp F hF hvp α hα hvp0 s hs
  obtain ⟨θ, hθ, hθF⟩ := hF
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : p - 1 ≠ 0 := by omega
  by_cases hα0 : α = 0
  · refine ⟨0, F.zero_mem, ?_⟩
    simp [hα0, zero_pow hp1]
  by_contra hcon
  push_neg at hcon
  have hs0 : (0 : ℝ≥0) < s := zero_lt_one.trans hs
  have ha : 0 < v α := (Valuation.pos_iff v).2 hα0
  set a := v α with ha_def
  set c := s * v (p : L) * a ^ (p - 1) with hc_def
  have hc : 0 < c := by positivity
  set η : ℝ≥0 := max s⁻¹ (max θ (v (p : L))) with hη_def
  have hη : η < 1 := by
    simp only [hη_def, max_lt_iff]
    exact ⟨inv_lt_one_of_one_lt₀ hs, hθ, hvp⟩
  have step : ∀ y ∈ F, v (α - y) ≤ a → ∃ y' ∈ F, v (α - y') ^ p ≤ η * v (α - y) ^ p := by
    intro y hy hya
    obtain ⟨y', hy', h⟩ := GlobalTheory.T.exists_improved_approx_kummer_generator L v p hp F θ hθ.le hvp.le hθF α y hα hy hya
    refine ⟨y', hy', h.trans ?_⟩
    have hcb := hcon y hy
    set b := v (α - y)
    apply max_le
    · have h0 : s * (v (p : L) * a ^ (p - 1)) ≤ b ^ (p - 1) := by
        calc s * (v (p : L) * a ^ (p - 1)) = c := by rw [hc_def]; ring
          _ ≤ _ := hcb.le
      have h2 : v (p : L) * a ^ (p - 1) ≤ s⁻¹ * b ^ (p - 1) := by
        calc v (p : L) * a ^ (p - 1) = s⁻¹ * (s * (v (p : L) * a ^ (p - 1))) := (inv_mul_cancel_left₀ hs0.ne' _).symm
          _ ≤ s⁻¹ * b ^ (p - 1) := by gcongr
      have h1 : v (p : L) * b * a ^ (p - 1) ≤ s⁻¹ * b ^ p := by
        calc v (p : L) * b * a ^ (p - 1) = b * (v (p : L) * a ^ (p - 1)) := by ring
          _ ≤ b * (s⁻¹ * b ^ (p - 1)) := by gcongr
          _ = s⁻¹ * (b ^ (p - 1) * b) := by ring
          _ = s⁻¹ * b ^ p := by rw [← pow_succ]; congr 2; omega
      exact h1.trans (by gcongr; exact le_max_left _ _)
    · gcongr; exact le_max_right _ _
  have iter : ∀ k : ℕ, ∃ y ∈ F, v (α - y) ≤ a ∧ v (α - y) ^ p ≤ η ^ k * a ^ p := by
    intro k
    induction k with
    | zero => exact ⟨0, F.zero_mem, by simp [ha_def], by simp [ha_def]⟩
    | succ k ih =>
      obtain ⟨y, hy, hya, hyk⟩ := ih
      obtain ⟨y', hy', h'⟩ := step y hy hya
      have hle : v (α - y') ^ p ≤ v (α - y) ^ p :=
        h'.trans (mul_le_of_le_one_left (by positivity) hη.le)
      refine ⟨y', hy', ?_, ?_⟩
      · exact ((pow_le_pow_iff_left₀ (by positivity) (by positivity) hp.ne_zero).1 hle).trans hya
      · calc v (α - y') ^ p ≤ η * v (α - y) ^ p := h'
          _ ≤ η * (η ^ k * a ^ p) := by gcongr
          _ = η ^ (k + 1) * a ^ p := by ring
  have hA : 0 < (a ^ p) ^ (p - 1) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hc p) hA) hη
  obtain ⟨y, hy, -, hyk⟩ := iter k
  have hcb := hcon y hy
  have e1 : c ^ p < (v (α - y) ^ p) ^ (p - 1) := by
    calc c ^ p < (v (α - y) ^ (p - 1)) ^ p := pow_lt_pow_left₀ hcb (by positivity) hp.ne_zero
      _ = _ := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : (v (α - y) ^ p) ^ (p - 1) ≤ η ^ k * (a ^ p) ^ (p - 1) := by
    calc (v (α - y) ^ p) ^ (p - 1) ≤ (η ^ k * a ^ p) ^ (p - 1) := pow_le_pow_left₀ (by positivity) hyk _
      _ = (η ^ k) ^ (p - 1) * (a ^ p) ^ (p - 1) := mul_pow _ _ _
      _ ≤ η ^ k * (a ^ p) ^ (p - 1) :=
          mul_le_mul_of_nonneg_right (pow_le_of_le_one (by positivity) (pow_le_one₀ (by positivity) hη.le) hp1) (by positivity)
  have e3 : η ^ k * (a ^ p) ^ (p - 1) < c ^ p := (lt_div_iff₀ hA).1 hk
  exact lt_irrefl _ ((e1.trans_le e2).trans e3)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterPropertiesStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) := by
  first | exact @GlobalTheory.BadShare.LevGroup.lev_group | exact GlobalTheory.BadShare.LevGroup.lev_group | (intros; apply GlobalTheory.BadShare.LevGroup.lev_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosurePropertiesStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPowerUnitsTower_closure_properties : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧ (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧ ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  first | exact @GlobalTheory.KZ.UnClosure.un_closure | exact GlobalTheory.KZ.UnClosure.un_closure | (intros; apply GlobalTheory.KZ.UnClosure.un_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem dd_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ) :=
  (CuspForm.discriminant).holo'

theorem inR_mdifferentiable : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro E f ⟨N, w, hN, _, hq⟩
  obtain ⟨a, ha, _⟩ := hq 1
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) :=
    ha.mdifferentiable hN
  have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w) := fun τ => (dd_mdifferentiable τ).pow w
  have hdiv := hg.div hD (fun τ => pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ))
  have heq : ((fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) / fun τ : ℍ => DD τ ^ w) = f := by
    funext τ
    have h0 : DD τ ^ w ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    simp only [Pi.div_apply, one_smul]
    field_simp
  rwa [heq] at hdiv

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemClosureOfFixed
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ArtinFix

variable {K G : Type} [Field K] [Group G] (ρ : G →* RingAut K)

lemma rho_mul_apply (a b : G) (x : K) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

lemma rho_inv_apply_apply (g : G) (x : K) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl

lemma rho_apply_inv_apply (g : G) (x : K) : ρ g (ρ g⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one]; rfl

variable (Δ : Subgroup G)

def fixSub : Subfield K where
  carrier := {x | ∀ δ ∈ Δ, ρ δ x = x}
  mul_mem' := by
    intro a b ha hb δ hδ
    simp [map_mul, ha δ hδ, hb δ hδ]
  one_mem' := by intro δ _; simp
  add_mem' := by
    intro a b ha hb δ hδ
    simp [map_add, ha δ hδ, hb δ hδ]
  zero_mem' := by intro δ _; simp
  neg_mem' := by
    intro a ha δ hδ
    simp [map_neg, ha δ hδ]
  inv_mem' := by
    intro a ha δ hδ
    simp [map_inv₀, ha δ hδ]

lemma map_mem_fixSub [hN : Δ.Normal] (g : G) {x : K} (hx : x ∈ fixSub ρ Δ) :
    ρ g x ∈ fixSub ρ Δ := by
  intro δ hδ
  have hm : g⁻¹ * δ * g ∈ Δ := by simpa using hN.conj_mem δ hδ g⁻¹
  have h := hx _ hm
  calc ρ δ (ρ g x) = ρ g (ρ (g⁻¹ * δ * g) x) := by
        rw [← rho_mul_apply, ← rho_mul_apply]; congr 1; group
    _ = ρ g x := by rw [h]

def restr [Δ.Normal] : G →* RingAut (fixSub ρ Δ) where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, map_mem_fixSub ρ Δ g x.2⟩
      invFun := fun x => ⟨ρ g⁻¹ x, map_mem_fixSub ρ Δ g⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (rho_inv_apply_apply ρ g (x : K))
      right_inv := fun x => Subtype.ext (rho_apply_inv_apply ρ g (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : K) (y : K)) }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro a b
    ext x
    exact rho_mul_apply ρ a b x

lemma le_ker_restr [Δ.Normal] : Δ ≤ (restr ρ Δ).ker := by
  intro δ hδ
  rw [MonoidHom.mem_ker]
  ext x
  exact x.2 δ hδ

theorem mem_closure_of_fixed (K G : Type) [Field K] [Group G] (ρ : G →* RingAut K)
    (Δ : Subgroup G) (hN : Δ.Normal) (hfi : Δ.FiniteIndex) (Y : Set K) (f : K)
    (hY : ∀ y ∈ Y, ∀ δ ∈ Δ, ρ δ y = y) (hf : ∀ δ ∈ Δ, ρ δ f = f)
    (hfix : ∀ g : G, (∀ y ∈ Y, ρ g y = y) → ρ g f = f) :
    f ∈ Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y) := by
  let L := fixSub ρ Δ
  let act : G ⧸ Δ →* RingAut L := QuotientGroup.lift Δ (restr ρ Δ) (le_ker_restr ρ Δ)
  letI : MulSemiringAction (G ⧸ Δ) L := MulSemiringAction.compHom L act
  have hsmul : ∀ (g : G) (x : L), (((QuotientGroup.mk g : G ⧸ Δ) • x : L) : K) = ρ g x :=
    fun g x => rfl
  let F := FixedPoints.subfield (G ⧸ Δ) L
  let Y' : Set L := {y | (y : K) ∈ Y}
  let E : IntermediateField F L := IntermediateField.adjoin F Y'
  have hfE : (⟨f, hf⟩ : L) ∈ E := by
    rw [← IsGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    obtain ⟨q, rfl⟩ := FixedPoints.toAlgAut_surjective (G ⧸ Δ) L σ
    induction q using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk g : G ⧸ Δ) • (⟨f, hf⟩ : L) = ⟨f, hf⟩
      apply Subtype.ext
      rw [hsmul]
      apply hfix g
      intro y hy
      have h1 := hσ ⟨y, hY y hy⟩ (IntermediateField.subset_adjoin F Y' hy)
      have h2 := congrArg Subtype.val h1
      exact (hsmul g ⟨y, hY y hy⟩).symm.trans h2
  have hle : E.toSubfield ≤ (Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y)).comap L.subtype := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · apply Subfield.subset_closure
      left
      intro g
      have h1 := c.2 (QuotientGroup.mk g : G ⧸ Δ)
      exact (hsmul g _).symm.trans (congrArg Subtype.val h1)
    · exact Subfield.subset_closure (Or.inr hx)
  exact hle (show (⟨f, hf⟩ : L) ∈ E.toSubfield from hfE)

end GlobalTheory.ArtinFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMul
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem disc_pow_mul_slash : ∀ (w : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * f (γ • τ) := by
  intro w f γ
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hd : (UpperHalfPlane.denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [ReciprocityTheory.ChartRestriction.L1.DD_smul, mul_pow, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatioStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_class_eq_imp_pow_ratio : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ), X.cls l n f = X.cls l n f' → ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.Tower.cls_eq_pow | exact GlobalTheory.Tower.cls_eq_pow | (intros; apply GlobalTheory.Tower.cls_eq_pow <;> assumption)
end

