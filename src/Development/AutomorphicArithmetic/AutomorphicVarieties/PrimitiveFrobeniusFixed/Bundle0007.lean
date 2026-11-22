import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem derivation_ne_zero (q : ℕ) (t : G ℚ Ω) {u : Ω} (hu : u ≠ 0) : der1 q t u ≠ 0 := by
  unfold der1
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero _).2 hu)

private theorem derivation_mul (q : ℕ) (t : G ℚ Ω) (u v : Ω) : der1 q t (u * v) = der1 q t u * der1 q t v := by
  unfold der1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, mul_pow]

private theorem derivation_zpow (q : ℕ) (t : G ℚ Ω) (u : Ω) (k : ℤ) : der1 q t (u ^ k) = der1 q t u ^ k := by
  unfold der1
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow₀, ← zpow_natCast ((t ^ i) u ^ k) i, ← zpow_natCast ((t ^ i) u) i, ← zpow_mul, ← zpow_mul,
    mul_comm]

private theorem derivation_galois_equivariant (q : ℕ) (t g : G ℚ Ω) (u : Ω) (h : ∀ s : G ℚ Ω, g (s u) = s (g u)) :
    g (der1 q t u) = der1 q t (g u) := by
  unfold der1
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, h]

private theorem der_mul (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) : der τ L (u * v) = der τ L u * der τ L v := by
  induction L with
  | nil => simp only [der.eq_1]
  | cons q L ih => rw [der.eq_2, der.eq_2, der.eq_2, ih, derivation_mul]

private theorem der_one (τ : ℕ → G ℚ Ω) (L : List ℕ) : der τ L (1 : Ω) = 1 := by
  induction L with
  | nil => rw [der.eq_1]
  | cons q L ih =>
    rw [der.eq_2, ih]
    unfold der1
    simp

private def derHom (τ : ℕ → G ℚ Ω) (L : List ℕ) : Ω →* Ω where
  toFun := der τ L
  map_one' := der_one τ L
  map_mul' := der_mul τ L

private theorem tele (q : ℕ) (t : G ℚ Ω) (u : Ω) (hu : u ≠ 0) (h : (t ^ (q - 1)) u = u) :
    t (der1 q t u) / der1 q t u = u ^ (q - 1) / nrm q t u := by
  have key : ∀ (a : ℕ → Ω) (n : ℕ),
      (∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n =
        a 0 * a n ^ n * ∏ i ∈ Finset.range n, a i ^ i := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
      calc (∏ i ∈ Finset.range n, a (i + 1) ^ i) * a (n + 1) ^ n * ((∏ i ∈ Finset.range n, a i) * a n) * a (n + 1)
          = ((∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n) * a (n + 1) ^ (n + 1) := by ring
        _ = a 0 * a n ^ n * (∏ i ∈ Finset.range n, a i ^ i) * a (n + 1) ^ (n + 1) := by rw [ih]
        _ = a 0 * a (n + 1) ^ (n + 1) * ((∏ i ∈ Finset.range n, a i ^ i) * a n ^ n) := by ring
  have hD : der1 q t u ≠ 0 := derivation_ne_zero q t hu
  have hN : nrm q t u ≠ 0 := by
    unfold nrm
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hu
  have htD : t (der1 q t u) = ∏ i ∈ Finset.range (q - 1), ((t ^ (i + 1)) u) ^ i := by
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, pow_succ', AlgEquiv.mul_apply]
  have hk := key (fun i => (t ^ i) u) (q - 1)
  simp only [pow_zero, AlgEquiv.one_apply, h] at hk
  rw [div_eq_div_iff hD hN, htD]
  have hD' : der1 q t u = ∏ i ∈ Finset.range (q - 1), ((t ^ i) u) ^ i := rfl
  have hN' : nrm q t u = ∏ i ∈ Finset.range (q - 1), (t ^ i) u := rfl
  rw [hD', hN']
  apply mul_right_cancel₀ hu
  linear_combination hk

end

theorem UpperTheory.V.ML.derBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N r : ℕ), N ≠ 0 → ∀ (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω), u ≠ 0 → (∀ g ∈ fixMu ℚ Ω N, g u = u) →
    der τ L u ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g (der τ L u) = der τ L u) ∧ (∀ g : G ℚ Ω, g (der τ L u) = der τ L (g u)) ∧
    ((∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (der τ L u) = 1) ∧
    (∀ v : Ω, der τ L (u * v) = der τ L u * der τ L v) ∧ (∀ k : ℤ, der τ L (u ^ k) = der τ L u ^ k) ∧
    (∀ q, der τ L (der1 q (τ q) u) = der1 q (τ q) (der τ L u)) ∧ (∀ L', L.Perm L' → der τ L u = der τ L' u) ∧
    ∀ q : ℕ, 1 ≤ q → (τ q ^ (q - 1)) u = u → τ q (der1 q (τ q) u) / der1 q (τ q) u = u ^ (q - 1) / nrm q (τ q) u := by
  intro Ω _ _ _ N r hN τ L u hu hfix
  obtain ⟨-, -, -, -, -, hcomm, -, -, -, -⟩ := galBasic Ω N hN
  have hfix1 : ∀ (q : ℕ) (t : G ℚ Ω) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der1 q t x) = der1 q t x := by
    intro q t x hx g hg
    rw [derivation_galois_equivariant q t g x (fun s => hcomm x hx g s), hx g hg]
  have hfixL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der τ L x) = der τ L x := by
    intro L x hx
    induction L with
    | nil => simpa only [der.eq_1] using hx
    | cons q L ih =>
      rw [der.eq_2]
      exact hfix1 q (τ q) _ ih
  have hneL : ∀ L : List ℕ, der τ L u ≠ 0 := by
    intro L
    induction L with
    | nil =>
      rw [der.eq_1]
      exact hu
    | cons q L ih =>
      rw [der.eq_2]
      exact derivation_ne_zero q (τ q) ih
  have hcommL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g : G ℚ Ω, g (der τ L x) = der τ L (g x) := by
    intro L x hx g
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih =>
      rw [der.eq_2, der.eq_2, derivation_galois_equivariant q (τ q) g _ (fun s => hcomm _ (hfixL L x hx) g s), ih]
  have hder1 : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (q : ℕ) (t : G ℚ Ω), der τ L (der1 q t x) = der1 q t (der τ L x) := by
    intro L x hx q t
    have e : der τ L (der1 q t x) = derHom τ L (der1 q t x) := rfl
    rw [e]
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow]
    show der τ L ((t ^ i) x) ^ i = _
    rw [← hcommL L x hx]
  have hconj : ∀ x : Ω, (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1) →
      ∀ (s : G ℚ Ω) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (s x) = 1 := by
    intro x hx s A hA
    obtain ⟨-, -, -, hlt, heq⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.2 (s⁻¹ • A) s
    have hsA : s • (s⁻¹ • A) = A := smul_inv_smul s A
    rw [hsA] at hlt heq
    apply (heq x).mpr
    apply hx
    intro hB
    apply hA
    have hr := (hlt (r : Ω)).mpr hB
    show A.valuation (r : Ω) < 1
    simpa using hr
  have hvalL : (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) →
      ∀ (L : List ℕ) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (der τ L u) = 1 := by
    intro hu1 L
    induction L with
    | nil => simpa only [der.eq_1] using hu1
    | cons q L ih =>
      intro A hA
      rw [der.eq_2]
      unfold der1
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [Valuation.map_pow, hconj _ ih _ A hA, one_pow]
  have hzpowL : ∀ (L : List ℕ) (k : ℤ), der τ L (u ^ k) = der τ L u ^ k := by
    intro L k
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih => rw [der.eq_2, der.eq_2, ih, derivation_zpow]
  have hperm : ∀ L' : List ℕ, L.Perm L' → der τ L u = der τ L' u := by
    intro L' hp
    induction hp with
    | nil => rfl
    | cons q _ ih => rw [der.eq_2, der.eq_2, ih]
    | swap a b l =>
      rw [der.eq_2, der.eq_2, der.eq_2, der.eq_2]
      have hx := hfixL l u hfix
      have h1 : der1 b (τ b) (der1 a (τ a) (der τ l u)) = der τ [b] (der1 a (τ a) (der τ l u)) := by
        rw [der.eq_2, der.eq_1]
      rw [h1, hder1 [b] _ hx, der.eq_2, der.eq_1]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact ⟨hneL L, hfixL L u hfix, fun g => hcommL L u hfix g, fun h => hvalL h L, der_mul τ L u, hzpowL L,
    fun q => hder1 L u hfix q (τ q), hperm, fun q _ h => tele q (τ q) u hu h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ImportsAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.ext :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ), F ≠ 0 → ∀ (β : G ℚ Ω →* Oˣ) (ν : G ℚ Ω → W), IsNu M F n β ν → ∀ δ : G ℚ Ω, IsUnit ((β δ : O) - 1) →
    ∃ c : G ℚ Ω → W, IsCoc β c ∧ (∀ u ∈ fixMu ℚ Ω F, c u = ν u) ∧ ∀ g, ∃ u ∈ fixMu ℚ Ω F, ∃ y : O, c g = y • ν u := by
  intro Ω _ _ _ O W _ _ _ M F n hF β ν hν δ hδ
  obtain ⟨hN, -, hcomm, -⟩ := galBasic Ω F hF
  have hk : (↑hδ.unit⁻¹ : O) * ((β δ : O) - 1) = 1 := hδ.val_inv_mul
  have h1 : ν 1 = 0 := by
    have := hν.add 1 (fixMu ℚ Ω F).one_mem 1 (fixMu ℚ Ω F).one_mem
    simpa using this
  have hinv : ∀ u ∈ fixMu ℚ Ω F, ν u⁻¹ = -ν u := by
    intro u hu
    have := hν.add u hu u⁻¹ ((fixMu ℚ Ω F).inv_mem hu)
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact this.symm)
  have hcm : ∀ g, g * δ * g⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := fun g => hcomm g δ
  refine ⟨fun g => (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹), ⟨?_, ?_⟩, ?_, fun g => ⟨_, hcm g, _, rfl⟩⟩
  · have hc : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹ * δ⁻¹) := by
      have c1 : Continuous (fun g : G ℚ Ω => g * δ) := continuous_mul_right δ
      have c2 : Continuous (fun g : G ℚ Ω => g⁻¹) := continuous_inv
      have c3 : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹) := c1.mul c2
      exact (continuous_mul_right δ⁻¹).comp c3
    have hf : Continuous (fun g : G ℚ Ω => (⟨g * δ * g⁻¹ * δ⁻¹, hcm g⟩ : fixMu ℚ Ω F)) := hc.subtype_mk hcm
    have hl : IsLocallyConstant (fun g : G ℚ Ω => ν (g * δ * g⁻¹ * δ⁻¹)) := hν.lc.comp_continuous hf
    exact hl.comp (fun w => (-(↑hδ.unit⁻¹ : O)) • w)
  · intro g h
    have e : g * h * δ * (g * h)⁻¹ * δ⁻¹ = g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ * (g * δ * g⁻¹ * δ⁻¹) := by
      group
    have hmem : g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ (hcm h) g
    show (-(↑hδ.unit⁻¹ : O)) • ν (g * h * δ * (g * h)⁻¹ * δ⁻¹) =
      (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹) + (β g : O) • ((-(↑hδ.unit⁻¹ : O)) • ν (h * δ * h⁻¹ * δ⁻¹))
    rw [e, hν.add _ hmem _ (hcm g), hν.eqv g _ (hcm h), smul_add, smul_comm (-(↑hδ.unit⁻¹ : O)) (β g : O)]
    abel
  · intro u hu
    have hconj : δ * u⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ ((fixMu ℚ Ω F).inv_mem hu) δ
    have e : u * δ * u⁻¹ * δ⁻¹ = u * (δ * u⁻¹ * δ⁻¹) := by
      group
    have e2 : ν u + (β δ : O) • -ν u = -(((β δ : O) - 1) • ν u) := by
      rw [sub_smul, one_smul, smul_neg]
      abel
    show (-(↑hδ.unit⁻¹ : O)) • ν (u * δ * u⁻¹ * δ⁻¹) = ν u
    rw [e, hν.add u hu _ hconj, hν.eqv δ u⁻¹ ((fixMu ℚ Ω F).inv_mem hu), hinv u hu, e2, smul_neg, neg_smul,
      neg_neg, smul_smul, hk, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * n), h z = z) ∧ z ^ M = g y / y) → ∃ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ := by
  intro Ω _ _ _ M F n a _ hFn ζ hζ δ hδ y hy hfix hz
  have hM : M ≠ 0 := NeZero.ne M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hM)
  have hcomm := (galBasic Ω (F * n) hFn).2.2.2.2.2.1 y hfix
  have hroot : ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ∃ k : ℕ, k < M ∧ ζ ^ k = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro g _ z hz'
    apply hζ.eq_pow_of_pow_eq_one
    have hgy : g y ≠ 0 := by simpa using hy
    have hdy : δ y ≠ 0 := by simpa using hy
    have hdgy : δ (g y) ≠ 0 := by simpa using hgy
    unfold opP
    calc (g (δ Y / Y ^ a) / (δ Y / Y ^ a) / (δ z / z ^ a)) ^ M
        = g (δ (Y ^ M)) / (g (Y ^ M)) ^ a / (δ (Y ^ M) / (Y ^ M) ^ a) / (δ (z ^ M) / (z ^ M) ^ a) := by
          simp only [map_div₀, map_pow, div_pow]
          ring
      _ = 1 := by
          rw [hY, hz', map_div₀ δ, hcomm g δ]
          field_simp
          rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero a hy)]
  classical
  choose! zf hzf using hz
  have hk := fun g hg => hroot g hg (zf g) (hzf g hg).2
  choose! kf hkf using hk
  refine ⟨fun g => (kf g : ZMod M), Y, hY, fun g hg => ⟨zf g, (hzf g hg).1, (hzf g hg).2, ?_⟩⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hkf g hg).1]
  exact (hkf g hg).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolHom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem opP_mul' (δ : G ℚ Ω) (a : ℕ) (x y : Ω) : opP δ a (x * y) = opP δ a x * opP δ a y := by
  simp only [opP, map_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

private theorem opP_ne' (δ : G ℚ Ω) (a : ℕ) {x : Ω} (hx : x ≠ 0) : opP δ a x ≠ 0 :=
  div_ne_zero ((map_ne_zero δ).2 hx) (pow_ne_zero _ hx)

private theorem opP_eq' {M a : ℕ} (hM : M ≠ 0) {δ : G ℚ Ω} (hδ : Pows M a δ) {x y : Ω} (hy : y ^ M ≠ 0)
    (h : x ^ M = y ^ M) : opP δ a x = opP δ a y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hy
    exact hy rfl
  have hw : (x / y) ^ M = 1 := by rw [div_pow, h, div_self hy]
  have hw0 : x / y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hw
    exact zero_ne_one hw
  have hx : x = y * (x / y) := (mul_div_cancel₀ x hy0).symm
  have h1 : opP δ a (x / y) = 1 := by
    unfold opP
    rw [hδ _ hw, div_self (pow_ne_zero _ hw0)]
  rw [hx, opP_mul', h1, mul_one]

private theorem zeta_inj' {M : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) {i j k : ZMod M}
    (h : ζ ^ i.val = ζ ^ j.val * ζ ^ k.val) : i = j + k := by
  rw [← pow_add] at h
  have h2 : ζ ^ (j.val + k.val) = ζ ^ ((j + k).val) := by
    rw [ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (j.val + k.val) M, pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  exact ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h.trans h2))

end

theorem UpperTheory.V.ML.kolHom :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) ∧ IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) ∧
    ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y → ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
  intro Ω _ _ _ M F n a _ hFn hMF ζ hζ δ hδ y hy hfix κ hK
  have hM : M ≠ 0 := NeZero.ne M
  have gb := galBasic Ω (F * n) hFn
  have gbF : fixMu ℚ Ω (F * n) ≤ fixMu ℚ Ω F := gb.2.2.2.2.2.2.2.2.1 F (dvd_mul_right F n)
  obtain ⟨Y₀, hY₀, hK'⟩ := hK
  have hgy : ∀ g : G ℚ Ω, g y / y ≠ 0 := fun g => div_ne_zero ((map_ne_zero g).mpr hy) hy
  have hY0 : Y₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hY₀
    exact hy hY₀.symm
  have hA : opP δ a Y₀ ≠ 0 := opP_ne' δ a hY0
  have key : ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro Y hY g hg z hz
    obtain ⟨z₀, -, hz₀, hκ⟩ := hK' g hg
    have e1 : opP δ a Y = opP δ a Y₀ :=
      opP_eq' hM hδ (by rw [hY₀]; exact hy) (hY.trans hY₀.symm)
    have e2 : opP δ a z = opP δ a z₀ :=
      opP_eq' hM hδ (by rw [hz₀]; exact hgy g) (hz.trans hz₀.symm)
    rw [e1, e2]
    exact hκ
  have hmul : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v := by
    intro u hu v hv
    obtain ⟨zu, -, hzu, hκu⟩ := hK' u hu
    obtain ⟨zv, hzvfix, hzv, hκv⟩ := hK' v hv
    have hzu0 : zu ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzu
      exact hgy u hzu.symm
    have hzv0 : zv ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzv
      exact hgy v hzv.symm
    have huy : u y ≠ 0 := (map_ne_zero u).mpr hy
    have hz : (u zv * zu) ^ M = (u * v) y / y := by
      rw [mul_pow, ← map_pow, hzv, hzu, map_div₀, AlgEquiv.mul_apply]
      field_simp
    have euv := key Y₀ hY₀ (u * v) (mul_mem hu hv) (u zv * zu) hz
    have hcomm : δ (u zv) = u (δ zv) := gb.2.2.2.2.2.1 zv hzvfix δ u
    have hPu : opP δ a (u zv) = u (opP δ a zv) := by
      unfold opP
      rw [hcomm, map_div₀, map_pow]
    rw [opP_mul', hPu, AlgEquiv.mul_apply] at euv
    have hfixζ : u (ζ ^ (κ v).val) = ζ ^ (κ v).val := by
      apply hu
      obtain ⟨c, hc⟩ := hMF
      rw [hc, pow_mul, ← pow_mul ζ, mul_comm (κ v).val M, pow_mul, hζ.pow_eq_one, one_pow,
        one_pow]
    have ev' : ζ ^ (κ v).val = u (v (opP δ a Y₀)) / u (opP δ a Y₀) / u (opP δ a zv) := by
      rw [← hfixζ, hκv, map_div₀, map_div₀]
    have hB : opP δ a zu ≠ 0 := opP_ne' δ a hzu0
    have huA : u (opP δ a Y₀) ≠ 0 := (map_ne_zero u).mpr hA
    have huC : u (opP δ a zv) ≠ 0 := (map_ne_zero u).mpr (opP_ne' δ a hzv0)
    apply zeta_inj' hζ
    rw [euv, hκu, ev']
    field_simp
  refine ⟨hmul, ?_, key⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ (opP δ a Y₀) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hint
  let H : Set (G ℚ Ω) := (fixMu ℚ Ω (F * n) : Set (G ℚ Ω)) ∩
    ((IntermediateField.adjoin ℚ {opP δ a Y₀}).fixingSubgroup : Set (G ℚ Ω))
  have hHo : IsOpen H := gb.2.1.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hH0 : ∀ h ∈ H, κ h = 0 := by
    rintro h ⟨h1, h2⟩
    have e := key Y₀ hY₀ h (gbF h1) 1 (by rw [one_pow, hfix h h1, div_self hy])
    have hP1 : opP δ a (1 : Ω) = 1 := by simp [opP]
    have hfx : h (opP δ a Y₀) = opP δ a Y₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 _
        (IntermediateField.mem_adjoin_simple_self ℚ _)
    rw [hP1, hfx, div_self hA, div_one] at e
    have e0 := zeta_inj' hζ (i := κ h) (j := 0) (k := 0)
      (by rw [e, ZMod.val_zero, pow_zero, one_mul])
    simpa using e0
  have hS : IsOpen {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_subtype_val)
  have hx : x ∈ {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} := by
    show (x : G ℚ Ω)⁻¹ * x ∈ H
    rw [inv_mul_cancel]
    exact ⟨one_mem _, one_mem _⟩
  filter_upwards [hS.mem_nhds hx] with w hw
  have hw' : (x : G ℚ Ω)⁻¹ * w ∈ fixMu ℚ Ω F := gbF hw.1
  have e := hmul x x.2 _ hw'
  rw [mul_inv_cancel_left, hH0 _ hw, add_zero] at e
  exact e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShtNu
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.shtNu :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → ∀ δ : G ℚ Ω, IsUnit ((α δ : O) - 1) → ∀ a : O, a ∣ (l : O) ^ m → ∀ c ∈ ShT (QO l O) α δ F a,
    IsNu (l ^ m) F F α c ∧ ((∀ u ∈ fixMu ℚ Ω F, c u = 0) → c = 0) ∧
    ∀ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), q.Prime → q ≡ 1 [MOD F] → Over A q → IsFrob (F := ℚ) A q φ → c φ = 0 →
      ∀ A' : ValuationSubring Ω, Over A' q → ∀ g ∈ Dec (F := ℚ) A', c g = 0 := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N₀ m F α hD δ hδ a ha c hc
  obtain ⟨⟨hlc, hcoc⟩, hcδ, hac, hunr, -⟩ := hc
  have hkill : ∀ x ∈ fixMu ℚ Ω F, ∀ w : QO l O, a • w = 0 → (α x : O) • w = w := by
    intro x hx w hw
    obtain ⟨t, ht⟩ := hD.triv x hx
    obtain ⟨b, hb⟩ := ha
    have h1 : ((α x : O) - 1) • w = 0 := by
      rw [ht, hb, show a * b * t = (b * t) * a by ring, mul_smul, hw, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at h1
  have h1 : c 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at e
    simpa using e
  have heqv : ∀ g u, u ∈ fixMu ℚ Ω F → c (g * u * g⁻¹) = (α g : O) • c u := by
    intro g u hu
    have e1 := hcoc (g * u) g⁻¹
    have e2 := hcoc g u
    have e3 := hcoc g g⁻¹
    rw [mul_inv_cancel, h1] at e3
    rw [e1, e2, map_mul, Units.val_mul, mul_smul, hkill u hu _ (hac _), add_right_comm, ← e3, zero_add]
  have hF : F ≠ 0 := by
    rw [hD.lev]
    have hl : l.Prime := Fact.out
    have hN : N₀ ≠ 0 := by
      rintro rfl
      exact hl.one_lt.ne' ((Nat.coprime_zero_left _).mp hD.cop)
    exact mul_ne_zero hN (pow_ne_zero _ hl.ne_zero)
  obtain ⟨-, hopen, hcomm, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u hu v _
    rw [hcoc, hkill u hu _ (hac _)]
  · exact hlc.comp_continuous continuous_subtype_val
  · exact heqv
  · intro u _
    obtain ⟨b, hb⟩ := ha
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hb, mul_comm, mul_smul, hac, smul_zero]
  · exact hunr
  · intro hz
    refine funext fun g => ?_
    have hk := hcomm g δ
    have e : g * δ = (g * δ * g⁻¹ * δ⁻¹) * (δ * g) := by group
    have e1 := hcoc g δ
    rw [hcδ, smul_zero, add_zero, e, hcoc _ (δ * g), hz _ hk, zero_add,
      hkill _ hk _ (hac _), hcoc δ g, hcδ, zero_add] at e1
    have e2 : ((α δ : O) - 1) • c g = 0 := by rw [sub_smul, one_smul, e1, sub_self]
    exact (hδ.smul_eq_zero).mp e2
  · intro q A φ hq hq1 hA hφ hcφ A' hA' x hx
    obtain ⟨-, -, -, hcopNot, hIne, -, hPows, hconj, hplace, hact⟩ := placeBasic Ω
    have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
    have hAF : ¬Over A F := hcopNot A q F hcop hA
    have hφF : φ ∈ fixMu ℚ Ω F := by
      intro y hy
      rw [hPows A q F φ hφ hAF y hy, pow_eq_pow_mod q hy, hq1, ← pow_eq_pow_mod 1 hy, pow_one]
    let K : Subgroup (G ℚ Ω) :=
      { carrier := {g | g ∈ fixMu ℚ Ω F ∧ c g = 0}
        mul_mem' := fun {u v} hu hv =>
          ⟨mul_mem hu.1 hv.1, by rw [hcoc, hu.2, hkill _ hu.1 _ (hac _), hv.2, add_zero]⟩
        one_mem' := ⟨one_mem _, h1⟩
        inv_mem' := fun {u} hu => by
          refine ⟨inv_mem hu.1, ?_⟩
          have e := hcoc u u⁻¹
          rw [mul_inv_cancel, h1, hu.2, zero_add, hkill _ hu.1 _ (hac _)] at e
          exact e.symm }
    have hKo : IsOpen (K : Set (G ℚ Ω)) := hopen.inter (hlc.isOpen_fiber 0)
    have hIK : Ine A ≤ K := fun g hg => ⟨hIne A F hAF hg, hunr A hAF g hg⟩
    obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
    have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
    have hDec : Dec A ≤ K := Kum.decGen ℚ Ω A v φ K hv hfr hKo hIK ⟨hφF, hcφ⟩
    obtain ⟨g, rfl⟩ := hconj A A' q hq hA hA'
    have hy := hDec (((hact A g).1 x).mp hx)
    have ex : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [ex, heqv g _ hy.1, hy.2, smul_zero]
end

