import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0052
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeLeCompletionGluedLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLattice_le_completion_glued_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), (∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p) → (∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p) → (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) → ∀ p, Λ p ≤ A.lat p Γ := by
  first | exact @GlobalTheory.HL.Glue.local_le_lat_of_approx | exact GlobalTheory.HL.Glue.local_le_lat_of_approx | (intros; apply GlobalTheory.HL.Glue.local_le_lat_of_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopCountExponentBound
section
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem loop_count_exponent_bound : ∀ C₁ Ad : ℝ, 1 ≤ C₁ → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C ≥ C₀, ∀ (s r f : ℕ) (De NT HH : ℝ), 1 ≤ s → 1 ≤ f → 1 ≤ De → 1 ≤ NT → 1 ≤ HH → De ≤ HH ^ Ad → NT ≤ HH → De ^ (4 + Real.logb 2 (2 * f)) * (De * NT) ^ (C₁ * s + C₁ * Real.log f) * (9 ^ (s * f) * (HH ^ (max Ad 3)) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2 ≤ HH ^ (C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + Real.logb 2 (2 * f))) * (C * s * f) ^ (6 * s * f) := by
  intro C₁ Ad hC₁
  have ha3 : (3 : ℝ) ≤ max Ad 3 := le_max_right _ _
  have haA : Ad ≤ max Ad 3 := le_max_left _ _
  generalize max Ad 3 = a at ha3 haA ⊢
  have hb : (0 : ℝ) ≤ (a + 1) * C₁ := by positivity
  refine ⟨5 * a + (a + 1) * C₁, by linarith, ?_⟩
  intro C hC s r f De NT HH hs hf hDe hNT hHH hDA hN
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hH0 : 0 < HH := by linarith
  have hlf0 : 0 ≤ Real.log f := Real.log_nonneg hf'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlfL : Real.log f ≤ Real.logb 2 (2 * f) := by
    rw [Real.logb, le_div_iff₀ hl2, Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hL0 : 0 ≤ Real.logb 2 (2 * (f : ℝ)) := le_trans hlf0 hlfL
  generalize Real.logb 2 (2 * (f : ℝ)) = L at hlfL hL0 ⊢
  generalize Real.log (f : ℝ) = l at hlfL hlf0 ⊢
  have hDa : De ≤ HH ^ a := hDA.trans (Real.rpow_le_rpow_of_exponent_le hHH haA)
  have hDN : De * NT ≤ HH ^ (a + 1) := by
    rw [Real.rpow_add hH0, Real.rpow_one]
    exact mul_le_mul hDa hN (by linarith) (by positivity)
  have h1 : De ^ (4 + L) ≤ HH ^ (a * (4 + L)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by linarith) hDa (by linarith)
  have h2 : (De * NT) ^ (C₁ * s + C₁ * l) ≤ HH ^ ((a + 1) * (C₁ * s + C₁ * l)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by positivity) hDN (by positivity)
  have h3 : ((HH ^ a) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2
      = HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
    congr 1
    push_cast
    ring
  have hC3 : (3 : ℝ) ≤ C * s * f := by
    have h0 : (3 : ℝ) ≤ C := by linarith
    have : (3 : ℝ) ≤ C * s := by nlinarith
    nlinarith
  have h4 : ((9 : ℝ) ^ (s * f)) ^ 2 ≤ (C * s * f) ^ (6 * s * f) := by
    calc ((9 : ℝ) ^ (s * f)) ^ 2 = 3 ^ (4 * (s * f)) := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
          congr 1; ring
      _ ≤ 3 ^ (6 * s * f) := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (s * f)])
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hC3 _
  have hexp : a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))
      ≤ C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + L) := by
    set P : ℝ := ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) with hP
    have hsr : (0 : ℝ) ≤ s * r := by positivity
    have hrr : (0 : ℝ) ≤ r ^ 2 := by positivity
    have e1 : (s : ℝ) ≤ P := by rw [hP]; nlinarith
    have e2 : 2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2) ≤ 5 * P := by rw [hP]; nlinarith
    have hP0 : 0 ≤ P := by linarith
    have e3 : (5 * a + (a + 1) * C₁) * P ≤ C * P := mul_le_mul_of_nonneg_right hC hP0
    have e4 : (5 * a + (a + 1) * C₁) * (1 + L) ≤ C * (1 + L) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    have e5 : (a + 1) * C₁ * s ≤ (a + 1) * C₁ * P := mul_le_mul_of_nonneg_left e1 hb
    have e6 : (a + 1) * C₁ * l ≤ (a + 1) * C₁ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hb
    have e7 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ a by linarith)
    have e8 : a * (4 + L) ≤ a * (5 * (1 + L)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e9 : C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) = C * P := by rw [hP]; ring
    rw [e9]
    clear_value P
    linear_combination e3 + e4 + e5 + e6 + e7 + e8
  rw [mul_pow, h3]
  calc _ ≤ HH ^ (a * (4 + L)) * HH ^ ((a + 1) * (C₁ * s + C₁ * l)) *
        ((C * s * f) ^ (6 * s * f) * HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)))) := by
        gcongr
    _ = HH ^ (a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) * (C * s * f) ^ (6 * s * f) := by
        rw [Real.rpow_add hH0, Real.rpow_add hH0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hHH hexp) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m i : ℕ), 1 ≤ i → (1 : Matrix (Fin m) (Fin m) E) ∈ congK L ϖ m i ∧ (∀ A ∈ congK L ϖ m i, IsIntM L A ∧ IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ A⁻¹ ∈ congK L ϖ m i ∧ (∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i) ∧ ∀ i' ≥ i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' ∧ B ∈ congK L ϖ m i) ∧ ∀ Γ : Matrix (Fin m) (Fin m) E, IsHerm L Γ → IsUnit Γ.det → IsCO (hermLat L m) (horb L ϖ Γ i) ∧ 0 < cont (hermLat L m) (horb L ϖ Γ i) := by
  first | exact @GlobalTheory.CongGrp.congK_group | exact GlobalTheory.CongGrp.congK_group | (intros; apply GlobalTheory.CongGrp.congK_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIntegersLocalisationIffSumCmData
section
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_disc_notMem (hc : Formalism.BasicNotions.CMData F E) (p : HeightOneSpectrum (𝓞 F)) :
    ∃ (θ t : 𝓞 E) (d : 𝓞 F), (t : E) = star (θ : E) ∧ d ∉ p.asIdeal ∧
      algebraMap F E (d : F) = ((θ : E) - (t : E)) ^ 2 := by
  haveI := p.isMaximal
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact bot_le)
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
  have ht' : (t : E) = star (θ : E) := ht
  obtain ⟨d0, hd0⟩ := (hc.fixed (((θ : E) - (t : E)) ^ 2)).1 (by
    rw [ht', star_pow, star_sub, star_star]; ring)
  have hint : IsIntegral ℤ d0 := by
    have h1 : IsIntegral ℤ (algebraMap F E d0) := by
      rw [hd0]
      exact (θ.isIntegral_coe.sub t.isIntegral_coe).pow 2
    exact (isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective).1 h1
  refine ⟨θ, t, ⟨d0, hint⟩, ht', ?_, hd0⟩
  intro hd
  rw [← hPp] at hd
  replace hd := Ideal.mem_comap.1 hd
  have : algebraMap (𝓞 F) (𝓞 E) ⟨d0, hint⟩ = (θ - t) ^ 2 := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_sub]
    exact hd0
  rw [this] at hd
  exact hθ (hP.isPrime.mem_of_pow_mem 2 hd)

theorem exists_coord (hc : Formalism.BasicNotions.CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by rw [← neg_sub, h, neg_zero])
  obtain ⟨b, hb⟩ := (hc.fixed ((x - star x) / (θ - star θ))).1 (by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]; field_simp; ring)
  obtain ⟨a, ha⟩ := (hc.fixed (x - (x - star x) / (θ - star θ) * θ)).1 (by
    rw [star_sub, star_mul, star_div₀, star_sub, star_sub, star_star, star_star]; field_simp; ring)
  exact ⟨a, b, by rw [ha, hb]; ring⟩

omit [StarRing E] in
theorem isIntegral_ιE {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
    (x : 𝓞 E) : IsIntegral 𝒪[A.Fp] (A.ιE (x : E)) :=
  (x.isIntegral_coe.map A.ιE.toIntAlgHom).tower_top

omit [StarRing E] in
theorem mem_integer_of_isIntegral {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (a : A.Fp) (h : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep a)) :
    a ∈ 𝒪[A.Fp] := by
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  have h1 : IsIntegral 𝒪[A.Fp] a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).1 h
  exact (Valuation.integer.integers (valuation A.Fp)).mem_of_integral h1

omit [StarRing E] in
theorem valuation_ιF_eq_one {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (d : 𝓞 F) (hd : d ∉ p.asIdeal) :
    valuation A.Fp (A.ιF (d : F)) = 1 := by
  have h : p.valuation F (d : F) = 1 := (p.valuation_eq_one_iff_notMem (K := F)).2 hd
  have h1 := (A.val (d : F) 1).2 (by rw [h, map_one])
  have h2 := (A.val 1 (d : F)).2 (by rw [h, map_one])
  rw [Valuation.Compatible.vle_iff_le (v := valuation A.Fp)] at h1 h2
  simp only [map_one] at h1 h2
  exact le_antisymm h1 h2

theorem mem_O_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A y
  constructor
  · intro hy
    rw [A.O_def] at hy
    obtain ⟨θ, t, d, ht, hd, hdisc⟩ := exists_disc_notMem hc p
    have hv := valuation_ιF_eq_one A d hd
    have hne : (θ : E) - star (θ : E) ≠ 0 := by
      intro h
      rw [ht, h] at hdisc
      have : d = 0 := by
        apply RingOfIntegers.ext
        simpa using hdisc
      exact hd (this ▸ p.asIdeal.zero_mem)
    have hco : ∀ z : A.Ep, ∃ a b : A.Fp,
        z = algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E) := by
      intro z
      have hz : z ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
      induction hz using Submodule.span_induction with
      | mem _ hx =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨a, b, rfl⟩ := exists_coord hc θ hne x
        exact ⟨A.ιF a, A.ιF b, by rw [map_add, map_mul, A.compat, A.compat]⟩
      | zero => exact ⟨0, 0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨a, b, rfl⟩ := h1
        obtain ⟨a', b', rfl⟩ := h2
        exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
      | smul c _ _ h1 =>
        obtain ⟨a, b, rfl⟩ := h1
        exact ⟨c * a, c * b, by rw [map_mul, map_mul, Algebra.smul_def]; ring⟩
    obtain ⟨a, b, rfl⟩ := hco y
    have hcj := hy.map (A.cj.toAlgHom.restrictScalars 𝒪[A.Fp])
    have hcj' : IsIntegral 𝒪[A.Fp]
        (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E)) := by
      have e : A.cj (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E)) =
          algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E) := by
        rw [map_add, map_mul, A.cj.commutes, A.cj.commutes, A.cj_ιE, hsig, ht]
      rw [← e]; exact hcj
    have hbd : b * A.ιF (d : F) ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := (hy.sub hcj').mul ((isIntegral_ιE A θ).sub (isIntegral_ιE A t))
      convert this using 1
      rw [map_mul, ← A.compat, hdisc, map_pow, map_sub]; ring
    have hb : b ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff] at hbd ⊢
      rwa [map_mul, hv, mul_one] at hbd
    have hbI : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep b) :=
      isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := ⟨b, hb⟩)
    have ha : a ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := hy.sub (hbI.mul (isIntegral_ιE A θ))
      simpa using this
    exact ⟨2, ![⟨a, ha⟩, ⟨b, hb⟩], ![1, θ], by simp [Fin.sum_univ_two]⟩
  · rintro ⟨n, c, x, rfl⟩
    rw [A.O_def]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (isIntegral_ιE A _)
    exact isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := c i)

end GlobalTheory.LocSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfIntegralStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximal_compact_of_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (h : S.GLV) (s si s' si' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), h ∈ S.St → (∀ i j, s i j ∈ L.O) → (∀ i j, si i j ∈ L.O) → s * si = 1 → (∀ i j, s' i j ∈ L.O) → (∀ i j, si' i j ∈ L.O) → s' * si' = 1 → (∀ j, h (S.f j) = ∑ i, s i j • S.f i) → (∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) → h ∈ S.K0 := by
  first | exact @GlobalTheory.HL.Frames.mem_K0_of_integral | exact GlobalTheory.HL.Frames.mem_K0_of_integral | (intros; apply GlobalTheory.HL.Frames.mem_K0_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NatCastIsUnitQuadraticCompletionAlmostAllStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (N : ℕ), N ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  first | exact @GlobalTheory.HL.Glue.natCast_isUnit_ae | exact GlobalTheory.HL.Glue.natCast_isUnit_ae | (intros; apply GlobalTheory.HL.Glue.natCast_isUnit_ae <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesWithGramMatrixResidueRing
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_eq_sum_tail {α : Type} [Fintype α] {m : ℕ} (S : Set (Fin (m + 1) → α))
    (T : Set (Fin m → α)) (h : ∀ X ∈ S, Fin.tail X ∈ T) :
    S.ncard = ∑ x ∈ T.toFinset, Set.ncard {y : α | (Fin.cons y x : Fin (m + 1) → α) ∈ S} := by
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := fun X => Fin.tail X) (t := T.toFinset)
      (by intro X hX; simpa using h X (by simpa using hX))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun y _ => (Fin.cons y x : Fin (m + 1) → α)) ?_ ?_ ?_
  · intro y hy
    simpa using hy
  · intro y _ y' _ hyy
    simpa using congrFun hyy 0
  · intro X hX
    simp only [Finset.mem_filter, Set.mem_toFinset] at hX
    obtain ⟨h1, rfl⟩ := hX
    exact ⟨X 0, by simpa using h1, by simp⟩

variable {B : Type} [CommRing B]

theorem tail_mem_sols (c : B →+* B) {m n : ℕ} (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (X : Fin (m + 1) → Fin n → B) (hX : X ∈ sols c n G) :
    Fin.tail X ∈ sols c n (G.submatrix Fin.succ Fin.succ) := by
  obtain ⟨⟨y, hy⟩, h2⟩ := hX
  refine ⟨⟨Fin.tail y, fun a b => ?_⟩, fun a b => h2 _ _⟩
  simpa [Fin.tail] using hy a.succ b.succ

theorem cons_mem_sols (c : B →+* B) (hc : ∀ u, c (c u) = u) {m n : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (hG : ∀ a b, c (G b a) = G a b)
    (x : Fin m → Fin n → B) (hx : x ∈ sols c n (G.submatrix Fin.succ Fin.succ))
    (y : Fin n → B) :
    (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G ↔
      Prim c (Fin.cons y x : Fin (m + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = G i.succ 0) ∧
        ip c y y = G 0 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => by simpa using h2 i.succ 0, by simpa using h2 0 0⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simpa using h3
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [← cj_ip c hc, h2, hG]
    · simpa using h2 a
    · simpa using hx.2 a b

theorem pow_le_eta_mul {q m n : ℕ} (hq : 2 ≤ q) (h : 2 * m + 1 ≤ n) :
    (q : ℝ) ^ n ≤ (2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n - (2 * m + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : 2 * (2 * m + 1 + d) - (2 * m + 1) = (2 * m + 1 + d) + d := by omega
  have h2 : (2 : ℝ) ^ d ≤ (q : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) d
  have h3 : (2 : ℝ) ^ (2 * m + 1) / 2 ^ (2 * m + 1 + d) = 1 / 2 ^ d := by
    rw [pow_add (2 : ℝ) (2 * m + 1) d]; field_simp
  rw [h1, h3, pow_add (q : ℝ) (2 * m + 1 + d) d, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  gcongr

theorem eta_le {m n : ℕ} (h : 2 * m + 3 ≤ n) : (2 : ℝ) ^ (2 * m + 1) / 2 ^ n ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (2 * m + 3) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
  have h2 : (2 : ℝ) ^ (2 * m + 3) = 4 * 2 ^ (2 * m + 1) := by ring
  linarith

theorem ncard_sols_eta [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) (ω : B)
    (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (n m : ℕ) :
    2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) →
      (1 - 2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n * m - m ^ 2)
          ≤ (Set.ncard (sols c n G) : ℝ) ∧
        (Set.ncard (sols c n G) : ℝ)
          ≤ (1 + 2 * (2 ^ (2 * m + 1) / 2 ^ n)) * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  induction m with
  | zero =>
    intro _ G _
    have h1 : sols c n G = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact ⟨⟨x, fun a => a.elim0⟩, fun a => a.elim0⟩
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * 0 + 1) / 2 ^ n := by positivity
    rw [h1, Set.ncard_univ, Nat.card_unique]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsub_self,
      pow_zero, mul_one, Nat.cast_one] at h2 ⊢
    constructor <;> linarith
  | succ m ih =>
    intro hn G hG
    obtain ⟨i1, i2⟩ := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    have hη := eta_le (m := m) (n := n) (by omega)
    have hp := pow_le_eta_mul (m := m) (n := n) hq (by omega)
    have he : (2 : ℝ) ^ (2 * (m + 1) + 1) / 2 ^ n = 4 * (2 ^ (2 * m + 1) / 2 ^ n) := by ring
    have hx : 2 * n * (m + 1) - (m + 1) ^ 2 = (2 * n * m - m ^ 2) + (2 * n - (2 * m + 1)) := by
      have h1 : m ^ 2 ≤ 2 * n * m := by nlinarith
      have h2 : 2 * n * (m + 1) = 2 * n * m + 2 * n := by ring
      have h3 : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      omega
    have hη0 : (0 : ℝ) ≤ 2 ^ (2 * m + 1) / 2 ^ n := by positivity
    rw [he, hx, pow_add (q : ℝ)]
    set η : ℝ := 2 ^ (2 * m + 1) / 2 ^ n
    set Q : ℝ := (q : ℝ) ^ (2 * n * m - m ^ 2) with hQ
    set R : ℝ := (q : ℝ) ^ (2 * n - (2 * m + 1)) with hR
    have hQ0 : 0 ≤ Q := by positivity
    have hR0 : 0 ≤ R := by positivity
    have key : ∀ x ∈ (sols c n (G.submatrix Fin.succ Fin.succ)).toFinset,
        (1 - 3 * η) * R ≤ (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ∧
          (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ≤ (1 + 3 * η) * R := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      have := GlobalTheory.T.card_primitiveTuple_extensions_le c hc ω hω hf q hq hB m n (by omega) x hx.1 (fun i => G i.succ 0)
        (G 0 0) (hG 0 0)
      simp only [cons_mem_sols c hc G hG x hx]
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    rw [ncard_eq_sum_tail _ _ (tail_mem_sols c G), Nat.cast_sum]
    rw [Set.ncard_eq_toFinset_card'] at i1 i2
    have k1 := Finset.card_nsmul_le_sum _ _ _ (fun x hx => (key x hx).1)
    have k2 := Finset.sum_le_card_nsmul _ _ _ (fun x hx => (key x hx).2)
    rw [nsmul_eq_mul] at k1 k2
    have hQR : 0 ≤ Q * R := mul_nonneg hQ0 hR0
    constructor
    · refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_right i1
        (mul_nonneg (by linarith) hR0)) k1)
      nlinarith [mul_nonneg (mul_nonneg hη0 hη0) hQR]
    · refine le_trans k2 (le_trans (mul_le_mul_of_nonneg_right i2
        (mul_nonneg (by linarith) hR0)) ?_)
      nlinarith [mul_nonneg (mul_nonneg hη0 (show 0 ≤ 1 / 4 - η by linarith)) hQR,
        mul_nonneg hη0 hQR]

theorem ncard_sols_residue : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  intro B _ _ c hc ω hω hf q hq hB m n hn G hG
  obtain ⟨h1, h2⟩ := ncard_sols_eta c hc ω hω hf q hq hB n m hn G hG
  have hη := eta_le hn
  have hQ : (0 : ℝ) ≤ (q : ℝ) ^ (2 * n * m - m ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right hη hQ
  constructor <;> nlinarith

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberField_lattice_determined_by_local_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧ {p | A.lat p Λ ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by
  first | exact @GlobalTheory.HL.PlacesRec.lattice_local | exact GlobalTheory.HL.PlacesRec.lattice_local | (intros; apply GlobalTheory.HL.PlacesRec.lattice_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingConjInverseAdjointCloseToOneStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  first | exact @GlobalTheory.Sloc.CloseConj.main | exact GlobalTheory.Sloc.CloseConj.main | (intros; apply GlobalTheory.Sloc.CloseConj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserEqOneOfFixesSecondFrameStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, (∀ b, x (G.f' b) = G.f' b) → x = 1 := by
  first | exact @GlobalTheory.HL.StabFix.eq_one_of_fix | exact GlobalTheory.HL.StabFix.eq_one_of_fix | (intros; apply GlobalTheory.HL.StabFix.eq_one_of_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelfStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPairingMatrix_inv_mul_self : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), G.Zh⁻¹ * G.Zh = 1 := by
  first | exact @GlobalTheory.HL.GFrames.Zh_inv_mul | exact GlobalTheory.HL.GFrames.Zh_inv_mul | (intros; apply GlobalTheory.HL.GFrames.Zh_inv_mul <;> assumption)
end

