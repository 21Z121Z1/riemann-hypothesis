import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem tame_scale : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  intro l _ Ω _ _ _ W c c' y n w ψ a hle ha hT
  obtain ⟨Y, P, u, b, hY, hYO, hP, hu, hb, hco, hsum, hfr, htame⟩ := hT
  refine ⟨fun s x => a • Y s x, P, u, a • b, ?_, ?_, hle hP, hu, ?_, ?_, ?_, hfr, ?_⟩
  · exact hY.const_smul a
  · intro s x i
    simpa using c'.O.mul_mem ha (hle (hYO s x i))
  · intro i
    simpa using c'.O.mul_mem ha (hle (hb i))
  · intro s t x
    simp only [hco s t x, smul_add, Matrix.mulVec_smul]
  · intro s
    rw [finsum_eq_sum_of_fintype] at *
    rw [← Finset.smul_sum, ← finsum_eq_sum_of_fintype, hsum s]
    simp only [smul_add, smul_sub, Matrix.mulVec_smul, smul_comm a P]
  · intro q hq hl
    obtain ⟨B, hB, t, htO, ht⟩ := htame q hq hl
    refine ⟨B, hB, fun x => a • t x, ?_, ?_⟩
    · intro x i
      simpa using c'.O.mul_mem ha (hle (htO x i))
    · intro s hs x
      simp only [ht s hs x, smul_sub, Matrix.mulVec_smul]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAnnihilatorDepthOfNotCoboundary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharAnn

theorem approx_candidate {K : Type} [NormedField K] {Γ : Type} (k a : Γ → K) {s₀ : Γ}
    (hk : k s₀ ≠ 1) {X : K} {ε : ℝ}
    (h0 : ‖a s₀ - (k s₀ * X - X)‖ ≤ ε) (s : Γ) (hs : ‖a s - (k s * X - X)‖ ≤ ε) :
    ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤
      (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by
  have hk' : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hk'
  set X₀ := a s₀ / (k s₀ - 1)
  have hX : X₀ - X = (a s₀ - (k s₀ * X - X)) / (k s₀ - 1) := by
    simp only [X₀]; field_simp
  have hXn : ‖X₀ - X‖ ≤ ε / ‖k s₀ - 1‖ := by
    rw [hX, norm_div]; exact div_le_div_of_nonneg_right h0 hpos.le
  have hid : a s - (k s * X₀ - X₀) = (a s - (k s * X - X)) - (k s - 1) * (X₀ - X) := by ring
  rw [hid]
  calc ‖(a s - (k s * X - X)) - (k s - 1) * (X₀ - X)‖
      ≤ ‖a s - (k s * X - X)‖ + ‖(k s - 1) * (X₀ - X)‖ := norm_sub_le _ _
    _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
        rw [norm_mul]; gcongr
    _ = (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) * ε := by field_simp

theorem exists_depth_of_not_coboundary : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} (H : Set Γ) (k a : Γ → Qbar l), (∃ s ∈ H, k s ≠ 1) → (¬ ∃ X : Qbar l, ∀ s ∈ H, a s = k s * X - X) → ∃ r : ℕ, ∀ (n : ℕ) (x y : Qbar l), ‖x‖ ≤ 1 → (∀ s ∈ H, ‖x * a s - (k s * y - y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ (n - r)‖ := by
  intro l _ Γ H k a ⟨s₀, hs₀, hk⟩ hna
  by_contra hcon
  push_neg at hcon
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := GlobalTheory.CoefEmbed.norm_prime_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have happrox : ∀ r : ℕ, ∃ X : Qbar l, ∀ t ∈ H, ‖a t - (k t * X - X)‖ ≤ q ^ r := by
    intro r
    obtain ⟨n, x, y, hx1, hb, hx⟩ := hcon r
    rw [norm_pow] at hx hb
    by_cases hnr : n < r
    · rw [Nat.sub_eq_zero_of_le hnr.le, pow_zero] at hx
      exact absurd hx (not_lt.mpr hx1)
    push_neg at hnr
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (pow_nonneg hq0 _) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    refine ⟨y / x, fun t ht => ?_⟩
    have hid : x * a t - (k t * y - y) = x * (a t - (k t * (y / x) - y / x)) := by
      field_simp
    have h1 := hb t ht
    rw [hid, norm_mul] at h1
    have hsplit : q ^ n = q ^ (n - r) * q ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hnr]
    rw [hsplit] at h1
    by_contra hlt
    push_neg at hlt
    have : q ^ (n - r) * q ^ r < ‖x‖ * ‖a t - (k t * (y / x) - y / x)‖ :=
      mul_lt_mul'' hx hlt (pow_nonneg hq0 _) (pow_nonneg hq0 _)
    linarith
  apply hna
  refine ⟨a s₀ / (k s₀ - 1), fun s hs => ?_⟩
  set C : ℝ := 1 + ‖k s - 1‖ / ‖k s₀ - 1‖
  have hbound : ∀ r : ℕ, ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ ≤ C * q ^ r := by
    intro r
    obtain ⟨X, hX⟩ := happrox r
    exact approx_candidate k a hk (hX s₀ hs₀) s (hX s hs)
  have hlim : Filter.Tendsto (fun r : ℕ => C * q ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hle := ge_of_tendsto' hlim hbound
  have h0 : ‖a s - (k s * (a s₀ / (k s₀ - 1)) - a s₀ / (k s₀ - 1))‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

end GlobalTheory.LocCharAnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutator
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem fix_root {l : ℕ} [Fact l.Prime] {s : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) {n : ℕ} {x : Ω}
    (hx : x ^ (l ^ n) = 1) : s x = x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hs)
    apply Units.ext
    have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
      (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
    apply hinj
    simpa [cycBar] using h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x hx
  have h3 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := h1
  rw [h3] at h2
  have h4 : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x = s x := rfl
  rw [h4, Units.val_one, map_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one] at h2
  exact h2

theorem comm_apply {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a)
    {s t : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) (ht : t ∈ (cycBar ℚ Ω l).ker) {y : Ω}
    (hy : y ^ (l ^ n) = a) : s (t y) = t (s y) := by
  by_cases h0 : y = 0
  · simp [h0]
  have key : ∀ g : G ℚ Ω, (g y / y) ^ (l ^ n) = 1 := fun g => by
    rw [div_pow, ← map_pow, hy, ha, ← hy]
    exact div_self (pow_ne_zero _ h0)
  obtain ⟨c, hcr, es⟩ : ∃ c : Ω, c ^ (l ^ n) = 1 ∧ s y = c * y :=
    ⟨s y / y, key s, (div_mul_cancel₀ _ h0).symm⟩
  obtain ⟨d, hdr, et⟩ : ∃ d : Ω, d ^ (l ^ n) = 1 ∧ t y = d * y :=
    ⟨t y / y, key t, (div_mul_cancel₀ _ h0).symm⟩
  rw [et, es, map_mul, map_mul, fix_root hs hdr, fix_root ht hcr, es, et]
  ring

theorem comm_fix {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a) {σ : G ℚ Ω}
    (hσ : σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆) {y : Ω} (hy : y ^ (l ^ n) = a) : σ y = y := by
  let K : Subgroup (G ℚ Ω) := ⨅ z : {z : Ω // z ^ (l ^ n) = a}, MulAction.stabilizer (G ℚ Ω) (z : Ω)
  have hK : ∀ g, g ∈ K ↔ ∀ z : Ω, z ^ (l ^ n) = a → g z = z := fun g => by
    simp only [K, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, Subtype.forall]
  have hle : ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [hK]
    intro z hz
    have hz' : ((t * s)⁻¹ z) ^ (l ^ n) = a := by rw [← map_pow, hz, ha]
    have e : s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
    rw [commutatorElement_def, e, AlgEquiv.mul_apply, AlgEquiv.mul_apply, comm_apply ha hs ht hz', ← AlgEquiv.mul_apply,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  exact (hK σ).1 (hle hσ) y hy

theorem isOpen_stab (x : Ω) : IsOpen {τ : G ℚ Ω | τ x = x} := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hx : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) := IntermediateField.adjoin.finiteDimensional hx
  have h := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {x})
  have hle : (IntermediateField.adjoin ℚ {x}).fixingSubgroup ≤ MulAction.stabilizer (G ℚ Ω) x := fun g hg => by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : {τ : G ℚ Ω | τ x = x} = (MulAction.stabilizer (G ℚ Ω) x : Set (G ℚ Ω)) := by
    ext τ; simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  rw [e]
  exact Subgroup.isOpen_mono hle h

theorem root_mod {B : ValuationSubring Ω} {p m N : ℕ} (hp : p.Prime) (hpB : B.valuation (p : Ω) < 1) (hm : m ≠ 0)
    {α : Ω} (hα : α ^ m = (N : Ω)) (hfr : B.valuation α ≤ 1 → B.valuation (α - α ^ p) < 1) :
    ∃ x : ZMod p, x ^ m = (N : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hαle : B.valuation α ≤ 1 := by
    have h1 : B.valuation α ^ m ≤ 1 := by
      rw [← map_pow, hα]; exact (B.valuation_le_one_iff _).2 (natCast_mem B N)
    exact (pow_le_one_iff hm).1 h1
  have hαB : α ∈ B := (B.valuation_le_one_iff α).1 hαle
  let a : B := ⟨α, hαB⟩
  have hmax : ∀ b : B, B.valuation (b : Ω) < 1 → IsLocalRing.residue B b = 0 := fun b hb =>
    (IsLocalRing.residue_eq_zero_iff b).2 ((B.valuation_lt_one_iff b).2 hb)
  have hpk : ((p : ℕ) : IsLocalRing.ResidueField B) = 0 := by
    have := hmax (p : B) (by simpa using hpB)
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField B) p := (CharP.charP_iff_prime_eq_zero hp).2 hpk
  let φ : ZMod p →+* IsLocalRing.ResidueField B := ZMod.castHom (dvd_refl p) _
  have hφ : Function.Injective φ := φ.injective
  have hr : IsLocalRing.residue B a ^ p = IsLocalRing.residue B a := by
    have := hmax (a - a ^ p) (by simpa [a] using hfr hαle)
    rw [map_sub, map_pow, sub_eq_zero] at this
    exact this.symm
  have hP : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ hp.one_lt
  have hsub : Finset.univ.image φ ⊆
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hcard : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset.card ≤
      (Finset.univ.image φ).card := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, ZMod.card]
    calc _ ≤ Multiset.card (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).natDegree :=
          Polynomial.card_roots' _
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.one_lt
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hrmem : IsLocalRing.residue B a ∈
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, hr, sub_self]
  rw [← heq] at hrmem
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hrmem
  refine ⟨x, hφ ?_⟩
  have ha : a ^ m = (N : B) := Subtype.ext (by simp [a, hα])
  rw [map_pow, hx, map_natCast, ← map_pow, ha, map_natCast]

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem normV_eq_absNorm (v : Pl) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem absNorm_dvd_of_mem {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : (n : 𝓞 ℚ) ∈ I) : Ideal.absNorm I ∣ n := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
  rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1

theorem natCast_mem_iff (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq_absNorm]
  refine ⟨absNorm_dvd_of_mem, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime' (v : Pl) : (normV v).Prime := by
  have h1 : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (natCast_mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((natCast_mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((natCast_mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem val_natCast_lt_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {w : Pl}
    (h : IsPlaceOver A w) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ normV w ∣ n := by
  rw [← natCast_mem_iff, ← h]
  simp

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem exists_odd_prime_gt_two_bounds : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ)
    (S S' : Finset Pl) (U : Subgroup (G ℚ Ω)) (σ : G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) →
    σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ → ∃ (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω),
      w ∉ S ∧ w ∉ S' ∧ IsPlaceOver B w ∧ IsFrob B (normV w) τ ∧ τ ∈ Dec (F := ℚ) B ∧ σ⁻¹ * τ ∈ U ∧
      l ^ n ∣ normV w - 1 ∧ ∀ v ∈ S, ∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w)) := by
  intro l hl Ω _ _ _ n S S' U σ hU hσ
  classical
  haveI hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hm : 0 < l ^ n := pow_pos hl.out.pos n
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ n) := by
    haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hm.ne'⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ n) Ω)
      (Polynomial.degree_cyclotomic_pos _ Ω hm).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.1 hz⟩
  have hα : ∀ v : Pl, ∃ α : Ω, α ^ (l ^ n) = (normV v : Ω) := fun v => IsAlgClosed.exists_pow_nat_eq _ hm
  choose α hα using hα
  let T : Finset Ω := insert ζ (S.image α)
  let O : Set (G ℚ Ω) := {τ | σ⁻¹ * τ ∈ U} ∩ ⋂ x ∈ T, {τ | τ x = x}
  have hO : IsOpen O := (hU.preimage (continuous_mul_left σ⁻¹)).inter
    (isOpen_biInter_finset fun x _ => isOpen_stab x)
  have hσker : σ ∈ (cycBar ℚ Ω l).ker := Subgroup.commutator_le_left _ _ hσ
  have hσO : σ ∈ O := by
    refine ⟨by simp [U.one_mem], Set.mem_iInter₂.2 fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact fix_root hσker hζ.pow_eq_one
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
      exact comm_fix (fun g => map_natCast g _) hσ (hα v)
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  have hTfin : ((S : Set Pl) ∪ (S' : Set Pl) ∪ {v : Pl | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 ℚ)}}).Finite :=
    ((S.finite_toSet).union (S'.finite_toSet)).union (Ideal.finite_factors hl0)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hTfin
  obtain ⟨τ, hτO, w, hwT, -, B, hB, hτ⟩ := hdense.inter_open_nonempty O hO ⟨σ, hσO⟩
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or] at hwT
  obtain ⟨⟨hwS, hwS'⟩, hwl⟩ := hwT
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h =>
    hwl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hfix : ∀ x ∈ T, τ x = x := fun x hx => Set.mem_iInter₂.1 hτO.2 x hx
  have hp : (normV w).Prime := normV_prime' w
  have hpB : B.valuation ((normV w : ℕ) : Ω) < 1 := (val_natCast_lt_one_iff hB _).2 dvd_rfl
  have hlB : ¬ B.valuation ((l : ℕ) : Ω) < 1 := fun h => hlw ((hB _).1 (by simpa using h))
  have hnot : ¬ B.valuation ((l ^ n : ℕ) : Ω) < 1 := fun h =>
    hlB ((val_natCast_lt_one_iff hB l).2 (hp.dvd_of_dvd_pow ((val_natCast_lt_one_iff hB (l ^ n)).1 h)))
  have hpows := (ML.placeBasic Ω).2.2.2.2.2.2.1 B (normV w) (l ^ n) τ hτ hnot
  have h1 : ζ ^ normV w = ζ := (hpows ζ hζ.pow_eq_one).symm.trans (hfix ζ (Finset.mem_insert_self _ _))
  have h2 : ζ ^ (normV w - 1) = 1 := by
    have hz : ζ ≠ 0 := hζ.ne_zero hm.ne'
    refine mul_right_cancel₀ hz ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul, h1]
  refine ⟨w, B, τ, hwS, hwS', hB, hτ, hτ.1, hτO.1, hζ.dvd_of_pow_eq_one _ h2, fun v hv => ?_⟩
  have hτv : τ (α v) = α v := hfix _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem α hv))
  refine root_mod hp hpB hm.ne' (hα v) fun h => ?_
  have := hτ.2 (α v) h
  rwa [hτv] at this

end GlobalTheory.Ord2.AuxiliaryInertOddPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.PrimeChar

theorem normV_prime (v : Pl) : (normV v).Prime := by
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hp : (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := CharP.char_is_prime (𝓞 ℚ ⧸ v.asIdeal) _
  haveI : Fact (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := ⟨hp⟩
  have hs : Function.Surjective (ZMod.castHom (dvd_refl (ringChar (𝓞 ℚ ⧸ v.asIdeal))) (𝓞 ℚ ⧸ v.asIdeal)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact ⟨(n : ZMod _), by simp⟩
  have hb := Nat.card_eq_of_bijective _ ⟨RingHom.injective _, hs⟩
  rw [normV, ← hb, Nat.card_zmod]
  exact hp

theorem normV_mem (v : Pl) : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal

theorem val_normV_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {B : ValuationSubring Ω} {v : Pl}
    (h : IsPlaceOver B v) : B.valuation ((normV v : ℕ) : Ω) < 1 := by
  have := (h _).2 (normV_mem v)
  simpa using this

theorem eq_of_normV_eq {v w : Pl} (h : normV v = normV w) : v = w := by
  have hp := normV_prime w
  have hpr : Prime ((normV w : ℕ) : 𝓞 ℚ) := by
    have h1 : Prime ((normV w : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((normV w : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((normV w : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h1
  have hI : (Ideal.span {((normV w : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have hv : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hI.eq_of_le v.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem, ← h]; exact normV_mem v)
  have hw : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hI.eq_of_le w.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem]; exact normV_mem w)
  exact HeightOneSpectrum.ext (hv.symm.trans hw)

theorem exists_surj (p N : ℕ) [Fact p.Prime] (h : N ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod N), Function.Surjective f := by
  have hc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : N ∣ Nat.card (ZMod p)ˣ := by rw [Nat.card_eq_fintype_card, ZMod.card_units]; exact h
  let c : ZMod (Nat.card (ZMod p)ˣ) →+ ZMod N := (ZMod.castHom hcard (ZMod N)).toAddMonoidHom
  refine ⟨(AddMonoidHom.toMultiplicative c).comp (zmodCyclicMulEquiv hc).symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hcard (Multiplicative.toAdd y)
  refine ⟨zmodCyclicMulEquiv hc (Multiplicative.ofAdd x), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  show Multiplicative.ofAdd (c x) = y
  exact hx

theorem pow_self_eq_one (N : ℕ) (a : Multiplicative (ZMod N)) : a ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end GlobalTheory.Ord2.PrimeChar

namespace GlobalTheory.Ord2.PrimeChar

theorem exists_prime_char : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl),
    1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧
      Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧
      ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) →
        ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  intro l _ Ω _ _ _ n w _ hdiv
  have hp := normV_prime w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  haveI : NeZero (normV w) := ⟨hp.ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_surj (normV w) (l ^ n) hdiv

  have hine : ∀ B : ValuationSubring Ω, IsPlaceOver B w →
      ∃ τ ∈ Ine (F := ℚ) B, (f.comp (Chr.cls ℚ Ω (normV w)) τ).toAdd = 1 := by
    intro B hB
    have hBp := val_normV_lt_one hB
    obtain ⟨g0, hg0⟩ := hf (Multiplicative.ofAdd 1)
    have hd : normV w ^ 1 ∣ normV w := by rw [pow_one]
    obtain ⟨w0, hw0⟩ := KStar.TotallyRealRoots.redPow_surjective (l := normV w) 1 (ZMod.unitsMap hd g0)
    obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω (normV w) B hBp w0
    refine ⟨σ, hσ, ?_⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : NeZero ((normV w : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
    have hX : PadicInt.toZModPow 1 (w0 : ℤ_[normV w]) = (((g0 : ZMod (normV w)).val : ℕ) : ZMod (normV w ^ 1)) := by
      have h2 := congrArg (fun u : (ZMod (normV w ^ 1))ˣ => (u : ZMod (normV w ^ 1))) hw0
      simp only [ZMod.unitsMap_val] at h2
      rw [← ZMod.cast_natCast (R := ZMod (normV w ^ 1)) hd ((g0 : ZMod (normV w)).val), ZMod.natCast_zmod_val]
      exact h2
    have hcls : Chr.cls ℚ Ω (normV w) σ = g0 := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 σ g0 fun ζ hζ => ?_
      have hζ' : ζ ^ (normV w ^ 1) = 1 := by rw [pow_one]; exact hζ
      have hspec : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ ℚ Ω (normV w) σ : ℤ_[normV w]ˣ) : ℤ_[normV w])).val :=
        cyclotomicCharacter.spec (L := Ω) (normV w) (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ'
      rw [hspec, hσw, hX, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ']
    rw [MonoidHom.comp_apply, hcls, hg0, toAdd_ofAdd]
  refine ⟨f.comp (Chr.cls ℚ Ω (normV w)), fun s hs => ?_, fun y => ?_, hine, fun v hvw hx B hB => ?_⟩
  ·
    have h1 : Chr.cls ℚ Ω (normV w) s = 1 := (Chr.clsFacts ℚ Ω (normV w)).2.2.1 s 1 fun ζ hζ => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
      exact hs ζ hζ
    rw [MonoidHom.comp_apply, h1, map_one]
  ·
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨τ, -, hτ⟩ := hine B hB
    refine ⟨τ ^ (Multiplicative.toAdd y).val, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_pow, toAdd_pow, hτ, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  ·
    have hq := normV_prime v
    haveI : Fact (normV v).Prime := ⟨hq⟩
    have hne : normV v ≠ normV w := fun h => hvw (eq_of_normV_eq h)
    have hcop : (normV w).Coprime (normV v) := (Nat.coprime_primes hp hq).2 (Ne.symm hne)
    have hBq := val_normV_lt_one hB
    obtain ⟨x, hx⟩ := hx
    have hq0 : ((normV v : ℕ) : ZMod (normV w)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod (normV w)) (normV w)]
      exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hx
      exact hq0 hx.symm
    let uq : (ZMod (normV w))ˣ := ZMod.unitOfCoprime (normV v) hcop.symm
    have huq : uq = Units.mk0 x hx0 ^ (l ^ n) := by
      ext
      simp [uq, hx]
    have hfq : f uq = 1 := by rw [huq, map_pow, pow_self_eq_one]
    intro g hg
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω (normV v) B hBq (normV w) hcop g hg
    have hcls : Chr.cls ℚ Ω (normV w) g = uq ^ k := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 g (uq ^ k) fun ζ hζ => ?_
      rw [hk ζ hζ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hζ]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hcls, map_pow, hfq, one_pow]

end GlobalTheory.Ord2.PrimeChar
end
end

