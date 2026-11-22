import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulSubOneLeOfValuation
section
namespace GlobalTheory.MulSubOneValuation

theorem mul_sub_one_le_of_valuation {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by

  have hM : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have he : (A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s =
      (A - 1) r s + (B - 1) r s + ((A - 1) * (B - 1)) r s := by
    simpa [Matrix.sub_apply, Matrix.add_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M r s) hM
  rw [he, Matrix.mul_apply]
  refine v.map_add_le (v.map_add_le (hA r s) (hB r s)) (v.map_sum_le fun k _ => ?_)
  calc v ((A - 1) r k * (B - 1) k s) = v ((A - 1) r k) * v ((B - 1) k s) := map_mul v _ _
    _ ≤ γ * γ := mul_le_mul' (hA r k) (hB k s)
    _ ≤ γ := mul_le_of_le_one_right' hγ

theorem mul_sub_one_le {E : Type} [Field E] [NumberField E]
    {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)} {n N : ℕ}
    {A B : Matrix (Fin n) (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)}
    (hA : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (A r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (B r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) ((A * B) r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  have hγ : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact mul_sub_one_le_of_valuation Valued.v hγ hA hB r s

end GlobalTheory.MulSubOneValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEval
section
namespace GlobalTheory

open MvPolynomial Finset

theorem clearDenominators {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K)
    (P D : ι → MvPolynomial τ K) :
    ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) →
      MvPolynomial.eval y M ≠ 0 ∧
      MvPolynomial.eval y G = MvPolynomial.eval y M *
        MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  classical
  set N := F.totalDegree
  refine ⟨∑ m ∈ F.support, C (F.coeff m) * ∏ i ∈ F.vars, (P i) ^ (m i) * (D i) ^ (N - m i),
    ∏ i ∈ F.vars, (D i) ^ N, fun y hy => ⟨?_, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow]; exact pow_ne_zero _ (hy i)
  · have hle : ∀ m ∈ F.support, ∀ i, m i ≤ N := fun m hm i =>
      (monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree F i)
    have hsub : ∀ m ∈ F.support, m.support ⊆ F.vars := fun m hm i hi =>
      (mem_vars i).mpr ⟨m, hm, hi⟩
    rw [MvPolynomial.eval_eq (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F,
      map_prod, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_subset (hsub m hm) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow]
    have hd := hy i
    have hk := hle m hm i
    rw [div_pow, ← pow_sub_mul_pow (MvPolynomial.eval y (D i)) hk]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAlgHomAlgebraicClosure
section
namespace GlobalTheory.PointFunction

open IsLocalRing

theorem nonempty_algHom_algebraicClosure (F k : Type) [Field F] [Field k] [IsAlgClosed k]
    [Algebra F k] : Nonempty (AlgebraicClosure F →ₐ[F] k) :=
  ⟨IsAlgClosed.lift⟩

theorem exists_common_factor (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (q : Ideal A) [q.IsPrime] (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k)
    (hφ : ∀ a, φ a = 0 ↔ a ∈ q) :
    ∃ χ : AlgebraicClosure q.ResidueField →ₐ[K] k,
      χ.comp (IsScalarTower.toAlgHom K A (AlgebraicClosure q.ResidueField)) = φ := by
  letI : Algebra A k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A k := .of_algebraMap_eq fun x => (φ.commutes x).symm
  let g : q.ResidueField →ₐ[A] k := Ideal.ResidueField.liftₐ q (Algebra.ofId A k)
    (fun a ha => (hφ a).2 ha) (fun a ha => by
      have : φ a ≠ 0 := fun h => ha ((hφ a).1 h)
      exact isUnit_iff_ne_zero.2 this)
  letI : Algebra q.ResidueField k := g.toRingHom.toAlgebra
  haveI : IsScalarTower A q.ResidueField k := .of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨χ⟩ := nonempty_algHom_algebraicClosure q.ResidueField k
  refine ⟨(χ.restrictScalars A).restrictScalars K, ?_⟩
  ext a
  exact (χ.restrictScalars A).commutes a

theorem valuationSubring_step (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (ι : A →ₐ[K] Ω)
    (V : ValuationSubring Ω) (h : ∀ a, ι a ∈ V) :
    W Ω ι ∈ V ∧ ∃ (_ : Algebra K (AlgebraicClosure (ResidueField V)))
      (φ : A →ₐ[K] AlgebraicClosure (ResidueField V)),
      (∀ a, φ a = 0 ↔ (⟨ι a, h a⟩ : V) ∈ maximalIdeal V) ∧
        ∀ r, ι r = W Ω ι → W _ φ = φ r := by
  let j : A →+* V := ι.toRingHom.codRestrict V.toSubring h
  letI : Algebra K V := (j.comp (algebraMap K A)).toAlgebra
  let jA : A →ₐ[K] V := { j with commutes' := fun _ => rfl }
  let s : V →ₐ[K] Ω := { V.subtype with commutes' := fun x => ι.commutes x }
  have hs : s.comp jA = ι := by ext a; rfl
  have hcl : IsAlgClosed (FractionRing V) :=
    IsAlgClosed.of_ringEquiv Ω _ (FractionRing.algEquiv V Ω).symm.toRingEquiv
  obtain ⟨v, hv⟩ := h2 V hcl jA
  have hw : W Ω ι = v := by rw [← hs, hv]; rfl
  refine ⟨hw ▸ v.2, ?_⟩
  let ρ : V →+* AlgebraicClosure (ResidueField V) :=
    (algebraMap (ResidueField V) _).comp (residue V)
  letI alg : Algebra K (AlgebraicClosure (ResidueField V)) := (ρ.comp (algebraMap K V)).toAlgebra
  let ρA : V →ₐ[K] AlgebraicClosure (ResidueField V) := { ρ with commutes' := fun _ => rfl }
  refine ⟨alg, ρA.comp jA, fun a => ?_, fun r hr => ?_⟩
  · change algebraMap (ResidueField V) (AlgebraicClosure (ResidueField V)) (residue V ⟨ι a, h a⟩) = 0 ↔ _
    rw [map_eq_zero, residue_eq_zero_iff]
  · rw [hv]
    have : v = jA r := Subtype.ext (by rw [← hw, ← hr]; rfl)
    rw [this]; rfl

theorem exists_eq_eval (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h1 : ∀ (k k' : Type) [Field k] [IsAlgClosed k] [Algebra K k] [Field k'] [IsAlgClosed k']
      [Algebra K k'] (φ : A →ₐ[K] k) (χ : k →ₐ[K] k'), W k' (χ.comp φ) = χ (W k φ))
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v) :
    ∃ r : A, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k),
      W k φ = φ r := by
  let L := FractionRing A
  let Ω := AlgebraicClosure L
  let ι : A →ₐ[K] Ω := IsScalarTower.toAlgHom K A Ω
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsGalois L Ω := inferInstance
  have hinj : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A L Ω]
    exact (algebraMap L Ω).injective.comp (IsFractionRing.injective A L)
  obtain ⟨x, hx⟩ : W Ω ι ∈ Set.range (algebraMap L Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (W Ω ι)).2 fun σ => ?_
    have e : ((σ : Ω →ₐ[L] Ω).restrictScalars K).comp ι = ι := by
      ext a
      exact ((σ : Ω →ₐ[L] Ω).restrictScalars A).commutes a
    have := h1 Ω Ω ι ((σ : Ω →ₐ[L] Ω).restrictScalars K)
    rw [e] at this
    exact this.symm
  have hint : IsIntegral A (W Ω ι) := by
    by_contra hn
    haveI : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
      inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
    obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure A Ω).toSubring) (x := W Ω ι) hn
    exact hxV (valuationSubring_step K A W h2 Ω ι V
      fun a => hV ((integralClosure A Ω).algebraMap_mem a)).1
  have hint' : IsIntegral A x := by
    rw [← hx] at hint
    exact (isIntegral_algebraMap_iff (algebraMap L Ω).injective).1 hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
  have hrw : ι r = W Ω ι := by
    rw [← hx, ← hr]; exact IsScalarTower.algebraMap_apply A L Ω r
  refine ⟨r, fun k _ _ _ φ => ?_⟩
  let q : Ideal A := RingHom.ker φ
  haveI : q.IsPrime := RingHom.ker_isPrime φ
  let f : Localization.AtPrime q →+* Ω := IsLocalization.lift (M := q.primeCompl)
    (g := algebraMap A Ω) fun y => by
      refine isUnit_iff_ne_zero.2 fun h0 => y.2 ?_
      have : (y : A) = 0 := hinj (by rw [h0, map_zero])
      rw [this]; exact q.zero_mem
  have hf : ∀ a, f (algebraMap A _ a) = ι a := fun a => IsLocalization.lift_eq _ a
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hmem : ∀ a, ι a ∈ V := fun a => hf a ▸ hV _
  obtain ⟨-, alg, ψ, hψ, hψr⟩ := valuationSubring_step K A W h2 Ω ι V hmem
  have hψq : ∀ a, ψ a = 0 ↔ a ∈ q := fun a => by
    rw [hψ, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      ← isUnit_map_iff (f.codRestrict V.toSubring hV)]
    have : f.codRestrict V.toSubring hV (algebraMap A _ a) = ⟨ι a, hmem a⟩ := Subtype.ext (hf a)
    rw [this]
  obtain ⟨χ, hχ⟩ := exists_common_factor K A q k φ fun a => Iff.rfl
  obtain ⟨χ', hχ'⟩ := exists_common_factor K A q _ ψ hψq
  have e := hψr r hrw
  rw [← hχ', h1] at e
  rw [← hχ, h1, χ'.toRingHom.injective e]
  rfl

end GlobalTheory.PointFunction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPow
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem psd_real_quad_single (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosSemidef) (i j : Fin g)
    (hij : i ≠ j) (c : ℝ) : 0 ≤ Y i i + c * Y i j + c * Y j i + c * c * Y j j := by
  have h := hY.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j c)
  simp only [star_trivial, mulVec_add, add_dotProduct, dotProduct_add, mulVec_single,
    single_dotProduct, dotProduct_single] at h
  simp [Pi.single_apply, hij, hij.symm] at h
  linarith

theorem abs_entry_le_of_psd_le (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ)
    (hY : Y.PosSemidef) (hMY : (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) (i j : Fin g) :
    |Y i j| ≤ M := by
  have hdiag : ∀ k, Y k k ≤ M := by
    intro k
    have := hMY.diag_nonneg (i := k)
    simp at this
    linarith
  have hsym : Y j i = Y i j := by
    have := congrFun (congrFun hY.isHermitian j) i
    simpa [conjTranspose_apply] using this.symm
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg (hY.diag_nonneg (i := i))]
    exact hdiag i
  · have h1 := psd_real_quad_single g Y hY i j hij 1
    have h2 := psd_real_quad_single g Y hY i j hij (-1)
    have hi := hdiag i
    have hj := hdiag j
    rw [hsym] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith

theorem det_map_ofReal_norm_le : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef →
    (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef →
    ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  intro g Y M _ hY hMY
  have hmap : (Y.map Complex.ofReal).det = ((Y.det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom Y
    exact this.symm
  rw [hmap, Complex.norm_real, Real.norm_eq_abs]
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := M) (A := Y)
    (fun i j => abs_entry_le_of_psd_le g Y M hY hMY i j)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubOneLe
section
universe u_1

namespace GlobalTheory.NormPowSubOne

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hζ, one_mul]
    exact ih

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ :=
  fun hζ a => norm_pow_sub_one_le hζ a

end GlobalTheory.NormPowSubOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe
section
namespace GlobalTheory.NormEvalSubBound

open Polynomial

section
variable {C : Type} [NormedField C] [IsUltrametricDist C]

lemma norm_pow_sub_pow_le {y a : C} (hy : ‖y‖ ≤ 1) (ha : ‖a‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - a ^ i‖ ≤ ‖y - a‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - a ^ (i + 1) = y * (y ^ i - a ^ i) + (y - a) * a ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - a‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - a‖ * ‖a‖ ^ i ≤ ‖y - a‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
        _ = ‖y - a‖ := mul_one _

lemma norm_eval_sub_le (Q : C[X]) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {y a : C} (hy : ‖y‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) : ‖Q.eval y - Q.eval a‖ ≤ ‖y - a‖ := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖Q.coeff i‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
        mul_le_mul (hc i) (norm_pow_sub_pow_le hy ha i) (norm_nonneg _) zero_le_one
    _ = ‖y - a‖ := one_mul _

lemma norm_le_one_of_root (Q : C[X]) (hm : Q.Monic) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {a : C}
    (h : Q.eval a = 0) : ‖a‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  set n := Q.natDegree
  have hpos : 0 < ‖a‖ := lt_trans zero_lt_one hlt
  have hs : ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ ≤ ‖a‖ ^ n / ‖a‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    calc ‖Q.coeff i‖ * ‖a‖ ^ i * ‖a‖ ≤ 1 * ‖a‖ ^ i * ‖a‖ := by
          gcongr
          exact hc i
      _ = ‖a‖ ^ (i + 1) := by ring
      _ ≤ ‖a‖ ^ n := pow_le_pow_right₀ hlt.le hi'
  have hlt2 : ‖a‖ ^ n / ‖a‖ < ‖a‖ ^ n := div_lt_self (by positivity) hlt
  have he : Q.eval a = a ^ n + ∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by
    conv_lhs => rw [hm.as_sum]
    simp [eval_finset_sum, n]
  rw [h] at he
  have : a ^ n = -∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by linear_combination -he
  have h3 : ‖a‖ ^ n = ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ := by
    rw [← norm_pow, this, norm_neg]
  linarith
end

theorem main_theorem : (let d1 : {C : Type} → [inst : NormedField C] → [IsUltrametricDist C] → Subfield C → Subring C := @(fun {C : Type} [NormedField C] [IsUltrametricDist C] (F : Subfield C) ↦ Subfield.toSubring F ⊓ Valuation.integer NormedField.valuation); ∀ {C : Type} [inst : NormedField C] [inst_1 : IsUltrametricDist C] {F : Subfield C} [IsAlgClosed C] [inst_3 : IsLocalRing ↥(d1 F)], (∀ (x : C), ‖x‖ ≤ (1 : ℝ) → ∃ y ∈ F, ‖x - y‖ < (1 : ℝ)) → IsAlgClosed (IsLocalRing.ResidueField ↥(d1 F))) := by
  intro d1 C _ _ F _ _ hdense
  have mem : ∀ x : C, x ∈ d1 F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := by
    intro x
    simp only [d1, Subring.mem_inf, Subfield.mem_toSubring, Valuation.mem_integer_iff,
      NormedField.valuation_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
  apply IsAlgClosed.of_exists_root
  intro p hmon hirr
  have hlift : p ∈ lifts (IsLocalRing.residue (d1 F)) :=
    (mem_lifts p).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_degree_eq_and_monic hlift hmon
  set Q : C[X] := q.map (d1 F).subtype with hQ
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    rw [hQ, coeff_map]; exact ((mem _).mp (q.coeff i).2).2
  have hQm : Q.Monic := hqmon.map _
  have hQdeg : Q.degree ≠ 0 := by
    rw [hQ, degree_map_eq_of_injective (Subring.subtype_injective _), hqdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q hQdeg
  have ha1 : ‖a‖ ≤ 1 := norm_le_one_of_root Q hQm hQc ha
  obtain ⟨y, hyF, hya⟩ := hdense a ha1
  have hy1 : ‖y‖ ≤ 1 := by
    have : y = a - (a - y) := by ring
    rw [this]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 ?_)
    rw [norm_neg]; exact hya.le
  let y' : d1 F := ⟨y, (mem y).mpr ⟨hyF, hy1⟩⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [← hqmap, eval_map, eval₂_hom, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval : ((q.eval y' : d1 F) : C) = Q.eval y := by
    rw [hQ, eval_map]
    exact (eval₂_hom (d1 F).subtype y').symm
  have hn : ‖((q.eval y' : d1 F) : C)‖ < 1 := by
    rw [hval]
    have : Q.eval y = Q.eval y - Q.eval a := by rw [IsRoot.def.mp ha, sub_zero]
    rw [this]
    refine lt_of_le_of_lt (norm_eval_sub_le Q hQc hy1 ha1) ?_
    rwa [norm_sub_rev]
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have h1 : ((q.eval y' : d1 F) : C) * (v : C) = 1 := by
    have := congrArg Subtype.val huv
    simpa using this
  have hv : ‖(v : C)‖ ≤ 1 := ((mem _).mp v.2).2
  have : ‖((q.eval y' : d1 F) : C) * (v : C)‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ ‖((q.eval y' : d1 F) : C)‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hn
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

end GlobalTheory.NormEvalSubBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NrmAbsOfValuationEqExp
section
noncomputable section

namespace GlobalTheory.Mem.NrmCompl

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)

theorem nrmAbs_apply (x : P.adicCompletion L) : nrmAbs P x = ‖x‖ := rfl

theorem nrmAbs_eq_toNNReal (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x

theorem nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl

theorem nrmAbs_of_valuation_eq_exp {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]

theorem nrmAbs_le_one_iff (x : P.adicCompletion L) : nrmAbs P x ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)

theorem nrmAbs_eq_one_iff (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'

theorem continuous_nrmAbs : Continuous (nrmAbs P) := continuous_norm

end GlobalTheory.Mem.NrmCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
section
noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  C (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (emb k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

def polFun {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K) :
    (ι → Matrix (Fin n) (Fin n) K) → K :=
  fun y => eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem polFun_apply {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K)
    (y : ι → Matrix (Fin n) (Fin n) K) : polFun P y = eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P := rfl

open MvPolynomial in
private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.eval_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (x : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2)
        (_root_.GlobalTheory.IntegralityCompare.twSub emb M s P) =
      (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (emb k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSub, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
end

