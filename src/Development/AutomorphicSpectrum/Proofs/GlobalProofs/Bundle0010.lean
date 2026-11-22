import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0002
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import GroundTheory.AutomorphicForms.MeasuresGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockParabolicModulusIntegral
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.ModB

variable {F : Type} [Field F]

def dg {n : ℕ} (v : Fin n → F) (hv : ∀ i, v i ≠ 0) : GL (Fin n) F where
  val := Matrix.diagonal v
  inv := Matrix.diagonal fun i => (v i)⁻¹
  val_inv := by simp [Matrix.diagonal_mul_diagonal, hv]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, hv]

end GlobalTheory.CompanionTheory.QL.ModB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartanDecompositionGeneralLinearStatement
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_generalLinear : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), ∃ k₁ ∈ GLint O n, ∃ k₂ ∈ GLint O n, ∃ (e : Fin n → ℤ) (d : GL (Fin n) F), (d : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => ϖ ^ e i) ∧ g = k₁ * d * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.QL.KAK.cartan | exact GlobalTheory.CompanionTheory.QL.KAK.cartan | (intros; apply GlobalTheory.CompanionTheory.QL.KAK.cartan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePowerStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_dvd_ramified_prime_power : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 → (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) → differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  first | exact @GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | exact GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | (intros; apply GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DirichletLogDerivBoundLeftHalfPlane
section
open Complex DirichletCharacter ArithmeticFunction

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft

theorem bound_right : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 3 / 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (3 / 2) n‖ :=
    (LSeriesSummable_vonMangoldt (s := 3 / 2) (by norm_num)).norm
  refine ⟨∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (3 / 2) n‖,
    tsum_nonneg fun _ => norm_nonneg _, ?_⟩
  intro N _ χ s hs2
  have hs : 1 < s.re := by linarith
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_
  refine (LSeries.norm_term_le s (g := fun n => (vonMangoldt n : ℂ)) ?_).trans
    (LSeries.norm_term_le_of_re_le_re _ (by simpa using hs2) n)
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N →
    χ.IsPrimitive → ∀ s : ℂ, s.re ≤ -(1/2 : ℝ) →
    (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -((k : ℝ) + 1/2)) →
    DirichletCharacter.LFunction χ s ≠ 0 ∧
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ C * Real.log (N * (‖s‖ + 2)) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.T.digamma_log_bound_left_region
  obtain ⟨B, hB, HB⟩ := bound_right
  refine ⟨4 + C₁ + C₂ + B, by positivity, ?_⟩
  intro N _ χ hN hχ s hre hs

  have hint : ∀ m : ℤ, s ≠ (m : ℂ) := by
    rintro m rfl
    rcases hs with h | ⟨k, hk⟩
    · simp at h
      linarith
    · have hk' : (m : ℝ) = -((k : ℝ) + 1 / 2) := by simpa using hk
      have h2 : ((2 * m + 2 * k + 1 : ℤ) : ℝ) = 0 := by
        push_cast
        linarith
      have h3 : (2 * m + 2 * k + 1 : ℤ) = 0 := by exact_mod_cast h2
      omega
  have hL : LFunction χ s ≠ 0 := by
    intro h0
    obtain ⟨⟨n, hn⟩, -⟩ := GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ s (by linarith) h0
    exact hint (-(n : ℤ)) (by rw [hn]; push_cast; rfl)
  refine ⟨hL, ?_⟩
  have hre' : (3 / 2 : ℝ) ≤ (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have hL' : LFunction χ⁻¹ (1 - s) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr fun h => by rw [h] at hre'; norm_num at hre')
      (by linarith)
  obtain ⟨a, hpar, m, hm, rfl⟩ : ∃ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) ∧
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ a = (m : ℂ) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, Or.inl ⟨h, rfl⟩, 0, Or.inl rfl, by simp⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩, 1, Or.inr rfl, by simp⟩
  have hm0 : (0 : ℝ) ≤ m := by rcases hm with rfl | rfl <;> simp
  have hm1 : (m : ℝ) ≤ 1 := by rcases hm with rfl | rfl <;> simp
  have hnorm : ‖(m : ℂ)‖ ≤ 1 := by rcases hm with rfl | rfl <;> simp
  have hz : (1 / 2 : ℝ) ≤ ((1 - s + (m : ℂ)) / 2).re := by
    have : ((1 - s + (m : ℂ)) / 2).re = (1 - s.re + m) / 2 := by simp
    rw [this]
    linarith
  have hwre : ((s + (m : ℂ)) / 2).re = (s.re + m) / 2 := by simp
  have hwim : ((s + (m : ℂ)) / 2).im = s.im / 2 := by simp
  have hc1 : ∀ n : ℕ, (s + (m : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    refine hint (-2 * n - m) ?_
    push_cast
    linear_combination 2 * h
  have hc2 : ∀ n : ℕ, (1 - s + (m : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    have h1 := congrArg Complex.re h
    rw [show ((1 - s + (m : ℂ)) / 2).re = (1 - s.re + m) / 2 by simp] at h1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at h1
    linarith
  rw [GlobalTheory.T.dirichlet_logDeriv_reflection_formula N χ hN hχ _ hpar s hc1 hc2 hL hL']

  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsn : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    have h2 := neg_abs_le s.re
    linarith
  have hpos : 0 < (N : ℝ) * (‖s‖ + 2) := by positivity
  set X := Real.log (N * (‖s‖ + 2)) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, Real.le_log_iff_exp_le hpos]
    have := Real.exp_one_lt_d9
    nlinarith
  have hlogN : Real.log N ≤ X := by
    refine Real.log_le_log (by linarith) ?_
    nlinarith [norm_nonneg s]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi3 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  have t1 : ‖(((Real.log (N / Real.pi) : ℝ)) : ℂ)‖ ≤ 4 * X := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      Real.log_div (by linarith) Real.pi_ne_zero, abs_le]
    constructor <;> linarith
  have t2 : ‖digamma ((1 - s + (m : ℂ)) / 2)‖ ≤ C₁ * X := by
    refine (H₁ _ hz).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁.le
    refine Real.log_le_log (by positivity) ?_
    have : ‖(1 - s + (m : ℂ)) / 2‖ ≤ (2 + ‖s‖) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have h1 := norm_add_le (1 - s) (m : ℂ)
      have h2 := norm_sub_le (1 : ℂ) s
      simp only [norm_one] at h2
      linarith
    nlinarith [norm_nonneg s]
  have t3 : ‖digamma ((s + (m : ℂ)) / 2)‖ ≤ C₂ * X := by
    have hcond : 1 / 2 ≤ |((s + (m : ℂ)) / 2).im| ∨
        ∃ k : ℤ, ((s + (m : ℂ)) / 2).re = (k : ℝ) / 2 + 1 / 4 := by
      rcases hs with h | ⟨k, hk⟩
      · left
        rw [hwim, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        linarith
      · right
        refine ⟨m - k - 1, ?_⟩
        rw [hwre, hk]
        push_cast
        ring
    refine (H₂ _ (by rw [hwre]; linarith) hcond).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂.le
    refine Real.log_le_log (by positivity) ?_
    have : ‖(s + (m : ℂ)) / 2‖ ≤ (‖s‖ + 1) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have h1 := norm_add_le s (m : ℂ)
      linarith
    nlinarith [norm_nonneg s]
  have t4 := HB N χ⁻¹ (1 - s) hre'
  have hh : ∀ x y z u : ℂ, ‖-x - y / 2 - z / 2 - u‖ ≤ ‖x‖ + ‖y‖ / 2 + ‖z‖ / 2 + ‖u‖ := by
    intro x y z u
    have e : -x - y / 2 - z / 2 - u = -x + -(y / 2) + -(z / 2) + -u := by ring
    rw [e]
    refine (norm_add₄_le).trans ?_
    simp [norm_neg, norm_div]
  refine (hh _ _ _ _).trans ?_
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteContinuousCrossedHomomorphisms
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Cocycles

section Algebra

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}

theorem cocycle_map_one (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : f 1 = 0 := by
  simpa using hf 1 1

theorem cocycle_map_inv (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (a : G) :
    f a⁻¹ = -ρ a⁻¹ (f a) := by
  have h := hf a⁻¹ a
  rw [inv_mul_cancel, cocycle_map_one hf] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def cocycleKer (ρ : Representation k G V) (f : G → V)
    (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : Subgroup G where
  carrier := {g | ρ g = 1 ∧ f g = 0}
  one_mem' := ⟨map_one ρ, cocycle_map_one hf⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
    rw [hf, ha', hb', map_zero, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have h2 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [ha, mul_one] at h2
    refine ⟨h1, ?_⟩
    rw [cocycle_map_inv hf, ha', map_zero, neg_zero]

theorem mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) :
    g ∈ cocycleKer ρ f hf ↔ ρ g = 1 ∧ f g = 0 := by
  exact Iff.rfl

theorem cocycle_mul_mem (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) {c : G}
    (hc : c ∈ cocycleKer ρ f hf) : f (g * c) = f g := by
  have hc' := ((mem_cocycleKer hf c).1 hc).2
  rw [hf, hc', map_zero, add_zero]

theorem inv_mul_mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) {a b : G}
    (h1 : f a = f b) (h2 : ρ a = ρ b) : a⁻¹ * b ∈ cocycleKer ρ f hf := by
  refine (mem_cocycleKer hf _).2 ⟨?_, ?_⟩
  · rw [map_mul, ← h2, ← map_mul, inv_mul_cancel, map_one]
  · rw [hf, cocycle_map_inv hf, h1, neg_add_cancel]

theorem injective_out_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    Function.Injective fun q : G ⧸ cocycleKer ρ f hf =>
      ((f q.out, ⇑(ρ q.out)) : V × (V → V)) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : ρ q₁.out = ρ q₂.out := LinearMap.coe_injective h2
  rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
  exact inv_mul_mem_cocycleKer hf h1 h2'

theorem index_cocycleKer [Finite V] (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    (cocycleKer ρ f hf).index ≠ 0 ∧
      (cocycleKer ρ f hf).index ≤ Nat.card (V × (V → V)) := by
  have hinj := injective_out_cocycleKer hf
  haveI : Finite (G ⧸ cocycleKer ρ f hf) := Finite.of_injective _ hinj
  exact ⟨Subgroup.index_ne_zero_of_finite, Nat.card_le_card_of_injective _ hinj⟩

theorem finite_right_invariant [Finite V] (H : Subgroup G) (hH : H.index ≠ 0) :
    {f : G → V | ∀ g, ∀ c ∈ H, f (g * c) = f g}.Finite := by
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hH
  refine (Set.finite_range (fun φ : G ⧸ H → V => φ ∘ (QuotientGroup.mk : G → G ⧸ H))).subset ?_
  intro f₀ hf₀
  simp only [Set.mem_ofPred_eq] at hf₀
  refine ⟨fun q => f₀ q.out, ?_⟩
  funext g
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul H g
  simp only [Function.comp_apply]
  rw [hc]
  exact hf₀ g c c.2

end Algebra

theorem isOpen_cocycleKer {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] [Finite A.V] {f : G → A.V}
    (hlc : IsLocallyConstant f) (hf : ∀ g h : G, f (g * h) = f g + A.ρ g (f h)) :
    IsOpen (cocycleKer A.ρ f hf : Set G) := by
  have hU : IsOpen ((⋂ v : A.V, (stabilizer A.ρ v : Set G)) ∩ {g | f g = 0}) :=
    (isOpen_iInter_of_finite fun v => IsDiscreteRep.isOpen_stabilizer v).inter (hlc.isOpen_fiber 0)
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨Set.mem_iInter.2 fun v => ?_, cocycle_map_one hf⟩) ?_
  · rw [SetLike.mem_coe, mem_stabilizer, map_one]
    rfl
  · rintro g ⟨hg1, hg2⟩
    refine ⟨LinearMap.ext fun v => ?_, hg2⟩
    exact (mem_stabilizer A.ρ v g).1 (Set.mem_iInter.1 hg1 v)

theorem finite_cocycles : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V →
    (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) →
    {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  intro k G _ _ _ _ A _ hV hN
  refine ((hN (Nat.card (A.V × (A.V → A.V)))).biUnion (fun H hH => finite_right_invariant H hH.2.1)).subset ?_
  rintro f ⟨hlc, hf⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨cocycleKer A.ρ f hf, ⟨isOpen_cocycleKer A hlc hf, index_cocycleKer hf⟩,
    fun g c hc => cocycle_mul_mem hf g hc⟩

end GlobalTheory.CompanionTheory.Cocycles
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndex
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem openSubgroups_finite_of_fields_finite :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Set (HeightOneSpectrum (𝓞 F))),
      (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
        Module.finrank F E ≤ N}.Finite) →
      ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) |
        IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S hfin N
  haveI : IsGalois F Ω := IsSepClosure.isGalois
  let K := maxUnramifiedOutside F Ω S
  let φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω :=
    fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))
  have key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) →
      (IntermediateField.fixedField H).fixingSubgroup = H := fun H hH =>
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  apply Set.Finite.of_finite_image (f := φ)
  · apply (hfin N).subset
    rintro _ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩
    have hfix := key H hHo
    have hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F))) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)
    let e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H) :=
      IntermediateField.equivMap _ (IntermediateField.val K)
    haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine ⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2
      (IntermediateField.lift_le _), ?_⟩
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hHN
  · intro H₁ h₁ H₂ h₂ h
    have h' := IntermediateField.lift_injective K h
    exact (key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))

end GlobalTheory.CompanionTheory.GlobalFiniteness
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearUnimodularHaar
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.HaarGL

theorem exists_haar_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro F _ _ _ _ O ϖ nrm q hLF n
  obtain ⟨hKo, hKc, hlc, _hsc, ht2, -, -⟩ := GlobalTheory.T.generalLinear_integral_compact_open hLF n
  haveI := hlc
  haveI := ht2
  haveI : BorelSpace (GL (Fin n) F) := GlobalTheory.CompanionTheory.QL.instBorelGL n
  refine ⟨?_, fun μ hμ => ?_⟩
  · let μ₀ : Measure (GL (Fin n) F) := Measure.haar
    have hpos : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ 0 :=
      hKo.measure_ne_zero μ₀ ⟨1, (GLint O n).one_mem⟩
    have hfin : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ ⊤ := hKc.measure_lt_top.ne
    refine ⟨(μ₀ (GLint O n : Set (GL (Fin n) F)))⁻¹ • μ₀, inferInstance, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · haveI := hμ
    exact ⟨GroundTheory.Automorphic.Measures.isMulRightInvariant_GL F n μ,
      ⟨GroundTheory.Automorphic.Measures.inv_eq_self_GL F n μ⟩⟩

end GlobalTheory.CompanionTheory.QL.HaarGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localField_topology_norm_balls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by
  first | exact @GlobalTheory.CompanionTheory.QLTop.localField_top | exact GlobalTheory.CompanionTheory.QLTop.localField_top | (intros; apply GlobalTheory.CompanionTheory.QLTop.localField_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OneLeNormOneSub
section
open Complex DirichletCharacter

namespace GlobalTheory.CompanionTheory.An

open GlobalTheory.Mem.An

theorem one_le_norm_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h1 : χ ≠ 1) {w : ℂ}
    (hw : LFunction χ w = 0) (hB : w ∉ zerosIn χ 0 1) : 1 ≤ ‖1 - w‖ := by
  have hre : w.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (not_lt.1 h) hw
  by_cases h0 : 0 < w.re
  · have him : 1 < |w.im| := by
      by_contra h
      refine hB ⟨h0, hre, ?_, hw⟩
      simpa using not_lt.1 h
    have := Complex.abs_im_le_norm (1 - w)
    have e : |(1 - w).im| = |w.im| := by simp
    linarith
  · have := Complex.abs_re_le_norm (1 - w)
    have e : (1 - w).re = 1 - w.re := by simp
    rw [e] at this
    have := le_abs_self (1 - w.re)
    linarith [not_lt.1 h0]

theorem norm_sub_two_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {w : ℂ}
    (hw : w ∈ zerosIn χ 0 1) : ‖w - 2‖ ≤ 7 / 2 := by
  obtain ⟨h0, h1, h2, -⟩ := hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a : (w - 2).re = w.re - 2 := by simp
  have b : (w - 2).im = w.im := by simp
  rw [a, b]
  have h3 : |w.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h4 : |w.im| ≤ 1 := by simpa using h2
  linarith

theorem logDerOne_holds : LogDerOne := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hχ => ?_⟩
  have h1 : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero h1
  obtain ⟨hW, hcount, hmain⟩ := H q χ h1 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hW hcount hmain
  set W : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hWdef
  set B : Set ℂ := zerosIn χ 0 1 with hBdef
  set g : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) with hg
  have hBW : B ⊆ W := fun w hw => ⟨norm_sub_two_le hw, hw.2.2.2⟩
  have hz : zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) = ∑ᶠ w ∈ B, g w := by
    unfold zsum zmult
    refine finsum_mem_congr rfl fun w _ => ?_
    simp only [hg, mul_one_div]
  have hsplit : ∑ᶠ w ∈ B, g w + ∑ᶠ w ∈ W \ B, g w = ∑ᶠ w ∈ W, g w :=
    finsum_mem_add_sdiff hBW hW
  have hD : ‖∑ᶠ w ∈ W \ B, g w‖ ≤ ∑ᶠ w ∈ W, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    have hfin : (W \ B).Finite := hW.subset Set.diff_subset
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hW]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w ∈ hfin.toFinset, ‖g w‖
        ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : w ∈ W \ B := by simpa using hw
          have h2 := one_le_norm_one_sub h1 hw'.1.2 hw'.2
          simp only [hg, norm_div, Complex.norm_natCast]
          exact div_le_self (Nat.cast_nonneg _) h2
      _ ≤ ∑ w ∈ hW.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
          intro x hx
          simp only [Set.Finite.mem_toFinset] at hx ⊢
          exact hx.1
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hz]
  have hmain' : ‖deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w‖ ≤ C * Real.log (q * 2) := hmain
  have e : deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ B, g w =
      (deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w) + ∑ᶠ w ∈ W \ B, g w := by
    rw [← hsplit]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h3 := hD.trans hcount
  have h4 := mul_le_mul_of_nonneg_left hlog hC.le
  linarith

end GlobalTheory.CompanionTheory.An
end

