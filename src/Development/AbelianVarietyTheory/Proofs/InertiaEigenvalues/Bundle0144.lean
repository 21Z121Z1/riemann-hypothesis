import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0133
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.NeutralLocalFields.Bundle0001
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnramifiedQuadraticLocalExt
section
namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem trace_int : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O,
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  fun K K' d φ hU y => trace_int_of_isIntegral hU _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hU.ne_zero y)

end GlobalTheory.UnitLemma.Unr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlusElementEtaNormNegOneStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_plus_element_eta_norm_neg_one : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 → (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f → ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  first | exact @GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one | exact GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one | (intros; apply GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegralStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_quadraticGaussIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  first | exact @GlobalTheory.JR.WeilQuad.exists_stableGauss | exact GlobalTheory.JR.WeilQuad.exists_stableGauss | (intros; apply GlobalTheory.JR.WeilQuad.exists_stableGauss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodPowCoboundaryOfRationalCoboundary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_addHom_zmod_pow_extend (O : Type) [CommRing O] (l n : ℕ) [Fact l.Prime]
    (hinj : Function.Injective (fun o : O => (l : O) ^ n * o)) (β : O →+ ZMod (l ^ 1)) :
    ∃ A : O →+ ZMod (l ^ (n + 1)), ∀ o : O,
      A ((l : O) ^ n * o) = ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1))) := by
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl0⟩

  have hcong : ∀ x : ℕ, ((l ^ n * (x % l ^ 1) : ℕ) : ZMod (l ^ (n + 1)))
      = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
    intro x
    rw [ZMod.natCast_eq_natCast_iff, pow_one, pow_succ]
    exact Nat.ModEq.mul_left' _ (Nat.mod_modEq x l)
  let g : O →+ ZMod (l ^ (n + 1)) :=
    { toFun := fun o => ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1)))
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [map_add, ZMod.val_add, hcong, mul_add, Nat.cast_add] }

  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    (AddMonoidHom.mulLeft ((l : O) ^ n)) hinj ((ZMod.toAddCircle).comp g)
  have hh' : ∀ o, h ((l : O) ^ n * o) = ZMod.toAddCircle (g o) := fun o =>
    DFunLike.congr_fun hh o

  have htors : ∀ o, (l ^ (n + 1)) • h o = 0 := by
    intro o
    have hlo : β ((l : O) * o) = 0 := by
      have hz : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [pow_one])
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, hz, zero_mul]
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, pow_succ, mul_assoc, hh']
    simp [g, hlo]

  have hdesc : ∀ o, ∃ k : ZMod (l ^ (n + 1)), ZMod.toAddCircle k = h o := by
    intro o
    have ht := htors o
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (h o)
    rw [← hx] at ht ⊢
    rw [← QuotientAddGroup.mk_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    refine ⟨(m : ZMod (l ^ (n + 1))), ?_⟩
    rw [ZMod.toAddCircle_intCast]
    congr 1
    have hN : ((l ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hl0
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hm
    rw [hm, mul_div_cancel_left₀ _ hN]
  choose A hA using hdesc
  have hAadd : ∀ a b, A (a + b) = A a + A b := by
    intro a b
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [map_add, hA, hA, hA, map_add]
  refine ⟨⟨⟨A, ?_⟩, hAadd⟩, ?_⟩
  · apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [hA, map_zero, map_zero]
  · intro o
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    show ZMod.toAddCircle (A _) = _
    rw [hA, hh']
    rfl

theorem addHom_zmod_pow_algebraMap_mul (O : Type) [CommRing O] (l m : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (A : O →+ ZMod (l ^ m)) (u : ℤ_[l]) (o : O) :
    A (algebraMap ℤ_[l] O u * o) = PadicInt.toZModPow m u * A o := by
  set v : ℕ := (PadicInt.toZModPow m u).val with hv

  have hk : u - (v : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨w, hw⟩ := hk
  have hu : u = (v : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have hkill : ∀ x : O, A ((l : O) ^ m * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hsplit : algebraMap ℤ_[l] O u * o
      = v • o + (l : O) ^ m * (algebraMap ℤ_[l] O w * o) := by
    rw [hu, map_add, map_mul, map_pow, map_natCast, map_natCast, nsmul_eq_mul]
    ring
  rw [hsplit, map_add, hkill, add_zero, map_nsmul, nsmul_eq_mul, hv, ZMod.natCast_zmod_val]

theorem exists_zmod_pow_coboundary_of_rational_coboundary :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (ε : Γ → ℤ_[l]) (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L] [TopologicalSpace L] [IsTopologicalRing L] (ι : O →+* L), Function.Injective ι → IsOpen (Set.range ι) → (l : L) ≠ 0 → (∀ x : L, ∃ n : ℕ, (l : L) ^ n * x ∈ Set.range ι) → ∀ (β : O →+ ZMod (l ^ 1)) (z : Γ → Γ → O) (f : Γ → L), Continuous f → (∀ g h, ι (z g h) = ι (algebraMap ℤ_[l] O (ε g)) * f h - f (g * h) + f g) → ∃ (n : ℕ) (a : Γ → ZMod (l ^ (n + 1))), Continuous a ∧ ∀ g h, PadicInt.toZModPow (n + 1) (ε g) * a h - a (g * h) + a g = ((l ^ n * (β (z g h)).val : ℕ) : ZMod (l ^ (n + 1))) := by
  intro Γ _ _ _ l _ ε O L _ _ _ _ _ ι hι hopen hl hcov β z f hf hz

  have hstep : ∀ k x, (l : L) ^ k * x ∈ Set.range ι → (l : L) ^ (k + 1) * x ∈ Set.range ι := by
    rintro k x ⟨o, ho⟩
    exact ⟨(l : O) * o, by rw [map_mul, map_natCast, ho, pow_succ]; ring⟩
  have hmono : Monotone (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι}) :=
    monotone_nat_of_le_succ (fun k x hx => hstep k x hx)
  obtain ⟨N, hN⟩ := (isCompact_range hf).elim_directed_cover
    (fun k : ℕ => {x : L | (l : L) ^ k * x ∈ Set.range ι})
    (fun k => hopen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono.directed_le
  have hN' : ∀ g, ∃ o : O, ι o = (l : L) ^ N * f g := fun g => hN ⟨g, rfl⟩
  choose F hF using hN'
  have hlN : ∀ k, (l : L) ^ k ≠ 0 := fun k => pow_ne_zero _ hl
  have hinjO : Function.Injective (fun o : O => (l : O) ^ N * o) := by
    intro a b hab
    apply hι
    have := congrArg ι hab
    simp only [map_mul, map_pow, map_natCast] at this
    exact mul_left_cancel₀ (hlN N) this
  obtain ⟨A, hA⟩ := exists_addHom_zmod_pow_extend O l N hinjO β

  have hrel : ∀ g h, (l : O) ^ N * z g h
      = algebraMap ℤ_[l] O (ε g) * F h - F (g * h) + F g := by
    intro g h
    apply hι
    rw [map_mul, map_pow, map_natCast, hz, map_add, map_sub, map_mul, hF, hF, hF]
    ring
  have hkill : ∀ x : O, A ((l : O) ^ (N + 1) * x) = 0 := by
    intro x
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨N, fun g => A (F g), ?_, ?_⟩
  ·
    refine ((IsLocallyConstant.iff_eventually_eq _).mpr fun g₁ => ?_).continuous
    have hPo : IsOpen {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} :=
      hopen.preimage (continuous_const.mul ((continuous_const.mul hf).sub continuous_const))
    have hmem : g₁ ∈ {g : Γ | ((l : L) ^ (N + 1))⁻¹ * ((l : L) ^ N * f g - (l : L) ^ N * f g₁)
        ∈ Set.range ι} := ⟨0, by simp⟩
    filter_upwards [hPo.mem_nhds hmem] with g hg
    obtain ⟨o, ho⟩ := hg
    have hFg : F g = F g₁ + (l : O) ^ (N + 1) * o := by
      apply hι
      rw [map_add, map_mul, map_pow, map_natCast, ho, mul_inv_cancel_left₀ (hlN _), hF, hF]
      ring
    show A (F g) = A (F g₁)
    rw [hFg, map_add, hkill, add_zero]
  · intro g h
    rw [← addHom_zmod_pow_algebraMap_mul O l (N + 1) A (ε g) (F h), ← map_sub, ← map_add,
      ← hrel, hA]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FewRootsSmallDisc
section
open Polynomial
open Classical

namespace GlobalTheory

theorem roots_taylor_eq_map_sub {K : Type*} [Field K] (p : K[X]) (w : K) :
    (taylor w p).roots = p.roots.map (fun x => x - w) := by
  have h := roots_comp_C_mul_X_add_C p (1 : K) w isUnit_one
  rw [taylor_apply]
  simpa using h

theorem coeff_sum_monomial_pow (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (k : ℕ)
    (hk : k ≤ E) :
    (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff (l ^ k) = a k := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp [coeff_monomial]
  · intro i _ hik
    rw [coeff_monomial, if_neg]
    intro h
    exact hik (Nat.pow_right_injective hl h)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_sum_monomial_small (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hgt : ∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) (j : ℕ) (hj : l ^ M < j) :
    ‖(∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j‖ * ρ ^ j
      < ‖(l : ℂ_[l])‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  by_cases h : ∃ k, k ≤ E ∧ l ^ k = j
  · obtain ⟨k, hkE, rfl⟩ := h
    rw [coeff_sum_monomial_pow l E a k hkE]
    have hMk : M < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hj
    exact hgt k hMk hkE
  · have h0 : (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j = 0 := by
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_monomial, if_neg]
      intro hij
      exact h ⟨i, by have := Finset.mem_range.mp hi; omega, hij⟩
    rw [h0, norm_zero, zero_mul]
    exact hlpos

theorem few_roots_small_disc : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  intro l _ E M a ρ W hME ha hρ0 hρ1 hM hgt hW
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k) with hG
  set H := taylor W G with hH
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  have hroots : Multiset.card (G.roots.filter fun z => ‖z - W‖ ≤ ρ)
      = Multiset.card (H.roots.filter fun z => ‖z‖ ≤ ρ) := by
    rw [hH, roots_taylor_eq_map_sub, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [hroots]
  have hd1 : 1 ≤ l ^ M := Nat.one_le_pow _ _ (by omega)
  have hGd : G.coeff (l ^ M) = a M := coeff_sum_monomial_pow l E a M hME
  have hdiff : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ ≤ ‖(l : ℂ_[l])‖ :=
    GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l l E a W ha hW
  have hρj : ∀ j, 1 ≤ j → ρ ^ j < 1 := fun j hj => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hdiffsmall : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ * ρ ^ j < ‖(l : ℂ_[l])‖ := by
    intro j hj
    calc ‖H.coeff j - G.coeff j‖ * ρ ^ j ≤ ‖(l : ℂ_[l])‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right (hdiff j hj) (by positivity)
      _ < ‖(l : ℂ_[l])‖ := mul_lt_of_lt_one_right hlpos (hρj j hj)
  have hHd : ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ := by
    have hlt : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ < ‖G.coeff (l ^ M)‖ := by
      have h1 : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ * ρ ^ l ^ M
          < ‖G.coeff (l ^ M)‖ * ρ ^ l ^ M := by
        rw [hGd, hM]; have h0 := hdiffsmall _ hd1; rwa [hGd] at h0
      exact lt_of_mul_lt_mul_right h1 (by positivity)
    have h2 : H.coeff (l ^ M) = G.coeff (l ^ M) + (H.coeff (l ^ M) - G.coeff (l ^ M)) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hGd, hM]
  have hHd0 : H.coeff (l ^ M) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hHd
    exact hlpos.ne hHd
  have hbig : ∀ j, l ^ M < j → ‖H.coeff j‖ * ρ ^ j < ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M := by
    intro j hj
    rw [hHd]
    have h2 : H.coeff j = G.coeff j + (H.coeff j - G.coeff j) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max (G.coeff j) (H.coeff j - G.coeff j)
    rw [← h2] at h3
    have hρ : 0 ≤ ρ ^ j := by positivity
    calc ‖H.coeff j‖ * ρ ^ j ≤ max ‖G.coeff j‖ ‖H.coeff j - G.coeff j‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right h3 hρ
      _ = max (‖G.coeff j‖ * ρ ^ j) (‖H.coeff j - G.coeff j‖ * ρ ^ j) := max_mul_of_nonneg _ _ hρ
      _ < ‖(l : ℂ_[l])‖ := max_lt (coeff_sum_monomial_small l E M a ρ hρ0 hgt j hj)
          (hdiffsmall j (by omega))
  exact (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] H ρ (l ^ M) hρ0 hHd0).2 hbig

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  first | exact @GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure | exact GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure | (intros; apply GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierIndicatorHermitianIntegralLatticeStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_indicator_hermitianIntegralLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  first | exact @GlobalTheory.JR.fourB_indicator_intLattice | exact GlobalTheory.JR.fourB_indicator_intLattice | (intros; apply GlobalTheory.JR.fourB_indicator_intLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElementsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLattice_sandwich_between_integral_elements : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧ ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  first | exact @GlobalTheory.UnitLemma.lattice_sandwich | exact GlobalTheory.UnitLemma.lattice_sandwich | (intros; apply GlobalTheory.UnitLemma.lattice_sandwich <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeights
section
noncomputable section
namespace GlobalTheory.PhiGam.PolarKernel
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem finrank_le_gmult (T : Module.End k U) (P Q Z S : Submodule k U) [FiniteDimensional k S]
    (hP : P ≤ S ⊔ Q) (hZ : ∀ x ∈ Z, x ∈ P ∧ T x ∈ Q) :
    finrank k (↥Z ⧸ Q.submoduleOf Z) ≤ gmult T P Q 0 := by
  unfold gmult
  rw [finrank_quot, finrank_quot, map_zero (algebraMap k (Module.End k U)), sub_zero]
  have hfin : FiniteDimensional k ((P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ) := by
    have h : (P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ ≤ S.map Q.mkQ := by
      have := Submodule.map_mono (f := Q.mkQ) ((inf_le_left (b := ⨆ m : ℕ, Q.comap (T ^ m))).trans hP)
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le h
  refine Submodule.finrank_mono (Submodule.map_mono fun x hx => ⟨(hZ x hx).1, ?_⟩)
  refine Submodule.mem_iSup_of_mem 1 ?_
  rw [Submodule.mem_comap, pow_one]
  exact (hZ x hx).2
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem le_span_sup {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V)
    (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh_iff_exists.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq_coe_X, mul_smul]
  exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) _

theorem exists_finite_le_sup (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := le_span_sup e _ he
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC w Z hZ
  have hr := GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen R g hg N hN hC (-w) w 0
  simp only [zero_add, neg_add_cancel, sh_zero_eq] at hr
  obtain ⟨S, hS, hF⟩ := exists_finite_le_sup N hN.1 (-w) w
  rw [neg_add_cancel, sh_zero_eq] at hF
  rw [← hr]
  exact finrank_le_gmult (nab g) _ _ Z S hF hZ

end GlobalTheory.PhiGam.PolarKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HilbertSubgroupLeKerOfKillsInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  first | exact @GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | exact GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | (intros; apply GlobalTheory.HilbertKill.hilbertSubgroup_le_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
section
noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

def D0 (G : Type) [Group G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ (H : Subgroup G) (χ : H →* ℂˣ),
    f = ind H (fun h => (χ h : ℂ)) - ind H (fun _ => 1)}

theorem ind_sub {G : Type} [Group G] [Finite G] (T : Subgroup G) (a b : T → ℂ) :
    ind T (a - b) = ind T a - ind T b :=
  (indAddHomComplex T).map_sub a b

theorem ind_const {G : Type} [Group G] [Finite G] (T : Subgroup G) (c : ℂ) (g : G) :
    ind T (fun _ => c) g = c * ind T (fun _ => 1) g := by
  classical
  haveI := Fintype.ofFinite G
  simp only [ind, finsum_eq_sum_of_fintype, ext0]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem ind_apply_one {G : Type} [Group G] [Finite G] (T : Subgroup G) (ψ : T → ℂ) :
    ind T ψ 1 = (T.index : ℂ) * ψ 1 := by
  classical
  haveI := Fintype.ofFinite G
  have h1 : ∀ x : G, ext0 T ψ (x⁻¹ * 1 * x) = ψ 1 := fun x => by
    have e : x⁻¹ * 1 * x = 1 := by group
    simp only [ext0, e, dif_pos T.one_mem]
    rfl
  simp only [ind, finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← T.card_mul_index]
  have : (Nat.card T : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := T)).ne'
  push_cast
  field_simp

theorem ind_top {G : Type} [Group G] [Finite G] (F : G → ℂ) (hF : ∀ g x : G, F (x⁻¹ * g * x) = F g) :
    ind (⊤ : Subgroup G) (fun h => F h) = F := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  simp only [ind, finsum_eq_sum_of_fintype, ext0, Subgroup.mem_top, dite_true, hF]
  have hc : Nat.card {x : G // True} = Nat.card G := Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]
  have : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  field_simp

theorem indFun_eq_ind {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    GlobalTheory.Published.indFun H f = ind H f := by
  classical
  funext g
  simp only [GlobalTheory.Published.indFun, ind, finsum_eq_sum_of_fintype, ext0]

end GlobalTheory.BrauerZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeOverUnramifiedExtIffStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  first | exact @GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isLat_overExt_iff <;> assumption)
end

