import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhTau
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic MeasureTheory ZSpan
open scoped Real ModularForm UpperHalfPlane

noncomputable section

theorem latticeArea_latticeOfTau (τ : ℍ) : latticeArea (latticeOfTau τ).lattice = τ.im := by
  have hvol : volume.real (fundamentalDomain Complex.basisOneI) = 1 := by
    rw [← Complex.toBasis_orthonormalBasisOneI,
      measureReal_congr (fundamentalDomain_ae_parallelepiped _ volume)]
    rw [measureReal_def, OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
    simp
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ (latticeOfTau τ).latticeBasis
    Complex.basisOneI, hvol, mul_one, Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr, abs_of_pos τ.im_pos]

theorem PhTau.proof (hΔ : DeltaEta.Statement) : PhTau.Statement := by
  intro τ
  have hy : 0 < τ.im := τ.im_pos
  have hη : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero (z := (τ : ℂ)) τ.im_pos
  have hn : 0 < ‖η (τ : ℂ)‖ := norm_pos_iff.2 hη
  have h1 : ‖((2 * π : ℝ) : ℂ) ^ 12 * η (τ : ℂ) ^ 24‖ = ((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have h6 : (1 / 6 : ℝ) * Real.log (((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6) =
      Real.log ((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) := by
    rw [Real.log_pow]; push_cast; ring
  unfold logPeriod
  rw [latticeArea_latticeOfTau, hΔ τ, h1, h6, ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdealPrimes
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global.Quadratic

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem absNorm_span_natCast_quadratic (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) = n ^ 2 := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem ramified_eq_span_sqrtDiscr {d : ℕ} (hd : d.Prime) (hdisc : discr K = -(d : ℤ))
    (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsPrime] (hN : (Ideal.absNorm 𝔭).Prime)
    (h2 : 𝔭 ^ 2 = Ideal.span {((Ideal.absNorm 𝔭 : ℕ) : 𝓞 K)}) :
    𝔭 = Ideal.span {sqrtDiscr K} := by
  set p := Ideal.absNorm 𝔭 with hp
  have h𝔭top : 𝔭 ≠ ⊤ := h𝔭.ne_top
  have hconj : ∀ x ∈ 𝔭, conjRing K x ∈ 𝔭 := by
    intro x hx
    have hx2 : x ^ 2 ∈ Ideal.span {(p : 𝓞 K)} := by
      rw [← h2]
      exact Ideal.pow_mem_pow hx 2
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx2
    have hp𝔭 : (p : 𝓞 K) ∈ 𝔭 := by
      have : (p : 𝓞 K) ∈ 𝔭 ^ 2 := by
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      exact Ideal.pow_le_self two_ne_zero this
    have hsq : (conjRing K x) ^ 2 ∈ 𝔭 := by
      have e : (conjRing K x) ^ 2 = conjRing K y * (p : 𝓞 K) := by
        rw [← map_pow, ← hy, map_mul, map_natCast]
      rw [e]
      exact Ideal.mul_mem_left _ _ hp𝔭
    exact h𝔭.mem_of_pow_mem 2 hsq
  have hres : ∀ x : 𝓞 K, ∃ n : ℤ, x - n ∈ 𝔭 := by
    intro x
    have hcard : Nat.card (𝓞 K ⧸ 𝔭) = p := by
      rw [hp, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have : Fact (Nat.card (𝓞 K ⧸ 𝔭)).Prime := ⟨hcard ▸ hN⟩
    have h1 : (1 : 𝓞 K ⧸ 𝔭) ≠ 0 := by
      rw [ne_eq, ← map_one (Ideal.Quotient.mk 𝔭), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h ↦ h𝔭top ((Ideal.eq_top_iff_one _).2 h)
    have htop : AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) = ⊤ := by
      rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card
          (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭)) with h | h
      · exfalso
        apply h1
        have : (1 : 𝓞 K ⧸ 𝔭) ∈ AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) :=
          AddSubgroup.mem_zmultiples 1
        rw [h] at this
        exact (AddSubgroup.mem_bot).1 this
      · exact h
    have hx : Ideal.Quotient.mk 𝔭 x ∈ AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) := by
      rw [htop]
      trivial
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
    refine ⟨n, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hn, map_intCast, zsmul_one, sub_self]
  have hsub : ∀ x : 𝓞 K, conjRing K x - x ∈ 𝔭 := by
    intro x
    obtain ⟨n, hn⟩ := hres x
    have hc := hconj _ hn
    rw [map_sub, map_intCast] at hc
    have := 𝔭.sub_mem hc hn
    rwa [sub_sub_sub_cancel_right] at this
  have hδ : sqrtDiscr K ∈ 𝔭 := by
    have e : sqrtDiscr K = intBasis K 0 * (conjRing K (intBasis K 1) - intBasis K 1) -
        intBasis K 1 * (conjRing K (intBasis K 0) - intBasis K 0) := by
      rw [sqrtDiscr]
      ring
    rw [e]
    exact 𝔭.sub_mem (𝔭.mul_mem_left _ (hsub _)) (𝔭.mul_mem_left _ (hsub _))
  have hnormsq : Ideal.absNorm (Ideal.span {sqrtDiscr K}) ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, sqrtDiscr_sq', hdisc, Int.cast_neg, Int.cast_natCast,
      Ideal.span_singleton_neg, absNorm_span_natCast_quadratic]
  have hnorm : Ideal.absNorm (Ideal.span {sqrtDiscr K}) = d :=
    Nat.pow_left_injective two_ne_zero hnormsq
  have hmax : (Ideal.span {sqrtDiscr K}).IsMaximal :=
    (Ideal.isPrime_of_irreducible_absNorm (hnorm ▸ hd)).isMaximal
      (by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact sqrtDiscr_ne_zero K)
  exact (hmax.eq_of_le h𝔭top ((Ideal.span_singleton_le_iff_mem _).2 hδ)).symm

theorem prime_cases {d : ℕ} (hd : d.Prime) (hdisc : discr K = -(d : ℤ))
    (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) :
    (∃ a : 𝓞 K, 𝔭 = Ideal.span {a}) ∨
      ∃ p : ℕ, p.Prime ∧ Ideal.absNorm 𝔭 = p ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsPrime ∧
        Ideal.absNorm 𝔮 = p ∧ 𝔭 * 𝔮 = Ideal.span {(p : 𝓞 K)} ∧ 𝔮 ≠ 𝔭 := by
  have : 𝔭.IsMaximal := h𝔭.isMaximal h0
  obtain ⟨p, k, hk, hpmem, hpp, hNk⟩ := Ideal.exists_prime_and_absNorm_eq_pow 𝔭
  have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hpmem
  have hdvdN : p ^ k ∣ p ^ 2 := by
    rw [← hNk, ← absNorm_span_natCast_quadratic (K := K)]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hpp.one_lt).1 hdvdN
  obtain ⟨𝔮, h𝔮⟩ : 𝔭 ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_iff_le.2 hle
  have hN𝔮 : Ideal.absNorm 𝔭 * Ideal.absNorm 𝔮 = p ^ 2 := by
    rw [← map_mul, ← h𝔮, absNorm_span_natCast_quadratic]
  have hp0 : 0 < p := hpp.pos
  interval_cases k
  · rw [hNk, pow_one, sq] at hN𝔮
    have hq : Ideal.absNorm 𝔮 = p := Nat.eq_of_mul_eq_mul_left hp0 hN𝔮
    have h𝔮p : 𝔮.IsPrime := Ideal.isPrime_of_irreducible_absNorm (hq ▸ hpp)
    by_cases he : 𝔮 = 𝔭
    · left
      refine ⟨sqrtDiscr K, ramified_eq_span_sqrtDiscr hd hdisc 𝔭 (by rw [hNk, pow_one]; exact hpp) ?_⟩
      rw [hNk, pow_one, sq, h𝔮, he]
    · right
      exact ⟨p, hpp, by rw [hNk, pow_one], 𝔮, h𝔮p, hq, h𝔮.symm, he⟩
  · rw [hNk] at hN𝔮
    have hq : Ideal.absNorm 𝔮 = 1 := by
      have h' : p ^ 2 * Ideal.absNorm 𝔮 = p ^ 2 * 1 := by rw [mul_one]; exact hN𝔮
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h'
    rw [Ideal.absNorm_eq_one_iff] at hq
    left
    exact ⟨p, by rw [h𝔮, hq, Ideal.mul_top]⟩

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdealPrincipal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

theorem eisensteinSum_scale_of_ne_zero (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) (n : ℕ) :
    eisensteinSum (scaleLattice c Λ) n = (c ^ n)⁻¹ * eisensteinSum Λ n := by
  let e : Λ ≃ₗ[ℤ] scaleLattice c Λ :=
    Submodule.equivMapOfInjective (LinearMap.mulLeft ℤ c) (mul_right_injective₀ hc) Λ
  rw [eisensteinSum, eisensteinSum, ← e.toEquiv.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

theorem latticeDiscr_scale_of_ne_zero (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) :
    latticeDiscr (scaleLattice c Λ) = (c ^ 12)⁻¹ * latticeDiscr Λ := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scale_of_ne_zero Λ hc]
  field_simp

variable {K : Type} [Field K] [NumberField K]

theorem idealLattice_spanSingleton_mul (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (x : K) :
    idealLattice σ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) * L.lattice =
      scaleLattice (σ x) L.lattice := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm l hl
    obtain ⟨y, hy, rfl⟩ := (mem_idealLattice σ).1 hm
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hy
    have hb : σ (algebraMap (𝓞 K) K b) ∈ latticeEnd L := by
      rw [hL]
      exact (mem_cmRing σ).2 ⟨b, rfl⟩
    refine Submodule.mem_map.2 ⟨σ (algebraMap (𝓞 K) K b) * l, hb l hl, ?_⟩
    simp only [LinearMap.mulLeft_apply, Algebra.smul_def, map_mul]
    ring
  · rw [scaleLattice, Submodule.map_le_iff_le_comap]
    intro l hl
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact Submodule.mul_mem_mul
      (map_mem_idealLattice σ (FractionalIdeal.mem_spanSingleton_self _ x)) hl

def spanNZ (a : 𝓞 K) (ha : a ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {a}, mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.zero_eq_bot,
    Ideal.span_singleton_eq_bot])⟩

theorem discrRatio_span_singleton (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (a : 𝓞 K) (ha : a ≠ 0) :
    discrRatio σ L.lattice (FractionalIdeal.mk0 K (spanNZ a ha)) = σ (algebraMap (𝓞 K) K a) ^ 12 := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha
  have hσ : σ (algebraMap (𝓞 K) K a) ≠ 0 := (map_ne_zero σ).2 haK
  rw [discrRatio, Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0, spanNZ,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
    idealLattice_spanSingleton_mul σ L hL, latticeDiscr_scale_of_ne_zero _ ((map_ne_zero σ).2 (inv_ne_zero haK)),
    map_inv₀, inv_pow, inv_inv, latticeDiscr_lattice, mul_div_assoc, div_self (discr_ne_zero L), mul_one]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWUnitOffPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField NumberField.InfinitePlace Module GroundTheory.Global GroundTheory.Global.Elliptic FractionalIdeal
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem isTotallyComplex_of_primeDiscriminant [Algebra.IsQuadraticExtension ℚ K]
    (S : PrimeDiscriminant K) : IsTotallyComplex K := by
  rw [← nrRealPlaces_eq_zero_iff]
  have h2 : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hr := card_add_two_mul_card_eq_rank (K := K)
  have hs := sign_discr (K := K)
  rw [S.discr_eq] at hs
  have hd : (0 : ℤ) < S.d := by exact_mod_cast S.prime.pos
  rw [Int.sign_eq_neg_one_of_neg (by omega)] at hs
  rcases Nat.even_or_odd (nrComplexPlaces K) with he | ho
  · rw [he.neg_one_pow] at hs
    norm_num at hs
  · obtain ⟨m, hm⟩ := ho
    omega

variable (σ : K →+* ℂ)

theorem image_idealLattice_spanSingleton_mul (c : ℂ) (b : K) (M : Ideal (𝓞 K)) :
    (c * ·) '' (idealLattice σ (spanSingleton (𝓞 K)⁰ b * (M : FractionalIdeal (𝓞 K)⁰ K)) : Set ℂ) =
      (fun x : 𝓞 K ↦ c * σ (b * algebraMap (𝓞 K) K x)) '' (M : Set (𝓞 K)) := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice, mem_singleton_mul, mem_coeIdeal]
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

theorem le_and_relIndex (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔭 : (Ideal (𝓞 K))⁰)
    (L' : PeriodPair)
    (hL' : L'.lattice = idealLattice σ ↑(FractionalIdeal.mk0 K 𝔭)⁻¹ * L.lattice) :
    L.lattice ≤ L'.lattice ∧
      L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup =
        Ideal.absNorm (𝔭 : Ideal (𝓞 K)) := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K)
    (↑(FractionalIdeal.mk0 K 𝔭)⁻¹) hI
  rw [← hL'] at h'
  obtain ⟨a, J₀, ha, hJ⟩ := exists_eq_spanSingleton_mul
    ((↑(FractionalIdeal.mk0 K 𝔭)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K))
  have hIJ : (I : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a)⁻¹ * ↑((𝔭 : Ideal (𝓞 K)) * J₀) := by
    rw [coeIdeal_mul, mul_left_comm, ← hJ, ← FractionalIdeal.coe_mk0 (K := K) 𝔭,
      Units.mul_inv_cancel_left]
  have ha' : (algebraMap (𝓞 K) K a)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 ha)
  let f : 𝓞 K →+ ℂ :=
    { toFun := fun x ↦ c * σ ((algebraMap (𝓞 K) K a)⁻¹ * algebraMap (𝓞 K) K x)
      map_zero' := by simp
      map_add' := fun x y ↦ by simp only [map_add, mul_add] }
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : c * σ ((algebraMap (𝓞 K) K a)⁻¹ * algebraMap (𝓞 K) K x) =
        c * σ ((algebraMap (𝓞 K) K a)⁻¹ * algebraMap (𝓞 K) K y) := hxy
    exact FaithfulSMul.algebraMap_injective (𝓞 K) K
      (mul_left_cancel₀ ha' (σ.injective (mul_left_cancel₀ hc hxy')))
  have hLset : L.lattice.toAddSubgroup = ((𝔭 : Ideal (𝓞 K)) * J₀).toAddSubgroup.map f := by
    apply SetLike.coe_injective
    rw [AddSubgroup.coe_map]
    show (L.lattice : Set ℂ) = _
    rw [hI, hIJ, image_idealLattice_spanSingleton_mul]
    rfl
  have hL'set : L'.lattice.toAddSubgroup = J₀.toAddSubgroup.map f := by
    apply SetLike.coe_injective
    rw [AddSubgroup.coe_map]
    show (L'.lattice : Set ℂ) = _
    rw [h', hJ, image_idealLattice_spanSingleton_mul]
    rfl
  have hle : ((𝔭 : Ideal (𝓞 K)) * J₀).toAddSubgroup ≤ J₀.toAddSubgroup :=
    (Submodule.toAddSubgroup_le _ _).2 (Ideal.mul_le.2 fun a _ b hb ↦ J₀.mul_mem_left a hb)
  refine ⟨?_, ?_⟩
  · rw [← Submodule.toAddSubgroup_le, hLset, hL'set]
    exact AddSubgroup.map_mono hle
  · rw [hLset, hL'set, AddSubgroup.relIndex_map_map_of_injective _ _ hf]
    have hJ0 : J₀ ≠ ⊥ := by
      rintro rfl
      refine ((FractionalIdeal.mk0 K 𝔭)⁻¹ * I).ne_zero ?_
      rw [Units.val_mul, hJ, coeIdeal_bot, mul_zero]
    have key := AddSubgroup.relIndex_mul_index hle
    rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, map_mul] at key
    have hn : Ideal.absNorm J₀ ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact mul_right_cancel₀ hn key

theorem discrRatio_spanSingleton (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (π : K)
    (hπ : π ≠ 0) (U : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hU : (U : FractionalIdeal (𝓞 K)⁰ K) = spanSingleton (𝓞 K)⁰ π) :
    discrRatio σ L.lattice U = σ π ^ 12 := by
  obtain ⟨L'', hL'', -⟩ := exists_lattice_mul σ hK L hL U
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K) (↑U⁻¹) hI
  rw [← hL''] at h'
  have hσπ : σ π ≠ 0 := (map_ne_zero σ).2 hπ
  have hscale : (L''.lattice : Set ℂ) = ((σ π)⁻¹ * ·) '' L.lattice := by
    rw [h', hI, Units.val_inv_eq_inv_val, hU, spanSingleton_inv, Set.image_image]
    ext z
    simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice, mem_singleton_mul]
    constructor
    · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      exact ⟨σ y, ⟨y, hy, rfl⟩, by rw [map_mul, map_inv₀]; ring⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, by rw [map_mul, map_inv₀]; ring⟩
  have hG : ∀ n, L''.G n = σ π ^ n * L.G n := fun n ↦ by
    rw [G_eq_of_lattice_eq_smul (inv_ne_zero hσπ) hscale n, inv_pow, inv_inv]
  have h₂ : L''.g₂ = σ π ^ 4 * L.g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, hG]; ring
  have h₃ : L''.g₃ = σ π ^ 6 * L.g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, hG]; ring
  rw [discrRatio, ← hL'', latticeDiscr_lattice, latticeDiscr_lattice, discr_of_g₂_g₃ h₂ h₃,
    mul_div_assoc, div_self (discr_ne_zero L), mul_one]

theorem isIntegral_discrRatio (hΔ : DeltaRatioIntegral.Statement)
    (hj : ∀ L : PeriodPair, latticeEnd L = cmRing σ → IsIntegral ℤ (weierstrassCurve L).j)
    (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔭 : (Ideal (𝓞 K))⁰)
    (hp : (Ideal.absNorm (𝔭 : Ideal (𝓞 K))).Prime) :
    IsIntegral ℤ (discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭)) := by
  obtain ⟨L', hL', -⟩ := exists_lattice_mul σ hK L hL (FractionalIdeal.mk0 K 𝔭)
  obtain ⟨hle, hidx⟩ := le_and_relIndex σ hK L hL 𝔭 L' hL'
  have h := hΔ L L' _ hp hle hidx
  have : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ {(weierstrassCurve L).j}) :=
    Algebra.IsIntegral.adjoin (by rintro x rfl; exact hj L hL)
  rw [discrRatio, ← hL']
  exact isIntegral_trans _ h

variable [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)

theorem exists_discrRatio_pow (hW : WCocycle.Statement S) (hΔ : DeltaRatioIntegral.Statement)
    (hj : JIntegral.Statement S) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (𝔭 : (Ideal (𝓞 K))⁰) (hp : (Ideal.absNorm (𝔭 : Ideal (𝓞 K))).Prime) (n : ℕ) :
    ∃ c : ℂ, IsIntegral ℤ c ∧ discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭 ^ (n + 1)) =
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) * c := by
  induction n with
  | zero => exact ⟨1, isIntegral_one, by rw [zero_add, pow_one, mul_one]⟩
  | succ n ih =>
    obtain ⟨c, hc, e⟩ := ih
    obtain ⟨L', hL', hL'e⟩ := exists_lattice_mul σ hK L hL (FractionalIdeal.mk0 K 𝔭 ^ (n + 1))
    have hw := isIntegral_discrRatio σ hK hΔ (hj σ) L' hL'e 𝔭 hp
    refine ⟨c * discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔭), hc.mul hw, ?_⟩
    rw [pow_succ, hW σ L hL, e, ← hL', mul_assoc]

omit hK [IsTotallyComplex K] in

theorem WUnitOffPrime.proof (hW : WCocycle.Statement S) (hΔ : DeltaRatioIntegral.Statement)
    (hj : JIntegral.Statement S) : WUnitOffPrime.Statement S := by
  intro σ L hL 𝔭 h𝔭 hp
  have := isTotallyComplex_of_primeDiscriminant S
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

  obtain ⟨n, π, hπ0, hπ⟩ : ∃ (n : ℕ) (π : 𝓞 K), π ≠ 0 ∧
      (𝔭 : Ideal (𝓞 K)) ^ (n + 1) = Ideal.span {π} := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos (ClassGroup.mk0 𝔭)).ne'
    have h1 : ClassGroup.mk0 (𝔭 ^ (n + 1)) = 1 := by
      rw [map_pow, show n + 1 = orderOf (ClassGroup.mk0 𝔭) from hn.symm, pow_orderOf_eq_one]
    have hpr := (ClassGroup.mk0_eq_one_iff (𝔭 ^ (n + 1)).2).1 h1
    rw [SubmonoidClass.coe_pow] at hpr
    refine ⟨n, Submodule.IsPrincipal.generator _, ?_, (Ideal.span_singleton_generator _).symm⟩
    intro h0
    have hb : (𝔭 : Ideal (𝓞 K)) ^ (n + 1) = ⊥ := by
      rw [← Ideal.span_singleton_generator ((𝔭 : Ideal (𝓞 K)) ^ (n + 1)), h0,
        Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero (𝔭 ^ (n + 1)) (by rw [SubmonoidClass.coe_pow, hb]; rfl)
  have hπK : algebraMap (𝓞 K) K π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hπ0
  have hU : ((FractionalIdeal.mk0 K 𝔭 ^ (n + 1) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K π) := by
    rw [Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0, ← coeIdeal_pow, hπ,
      coeIdeal_span_singleton]
  obtain ⟨c, hc, e⟩ := exists_discrRatio_pow σ hK S hW hΔ hj L hL 𝔭 hp n
  rw [discrRatio_spanSingleton σ hK L hL _ hπK _ hU] at e
  have hwint := isIntegral_discrRatio σ hK hΔ (hj σ) L hL 𝔭 hp
  refine ⟨(hwint.tower_top (A := ℚ)).isAlgebraic, ?_⟩
  rintro F _ _ ι τ hτ ⟨x, hx⟩
  have hcomp : ∀ z : K, τ (ι z) = σ z := fun z ↦ by rw [← hτ]; rfl
  have hσπ : σ (algebraMap (𝓞 K) K π) ≠ 0 := (map_ne_zero σ).2 hπK
  have hw0 : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e
    exact pow_ne_zero 12 hσπ e
  have hxint : IsIntegral ℤ x := by
    rw [← isIntegral_algHom_iff τ.toIntAlgHom τ.injective]
    change IsIntegral ℤ (τ x)
    rw [hx]
    exact hwint
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [← hx, map_zero])
  set y : F := ι (algebraMap (𝓞 K) K π) ^ 12 / x with hy_def
  have hy : τ y = c := by
    rw [hy_def, map_div₀, map_pow, hcomp, hx, e, mul_div_cancel_left₀ _ hw0]
  have hyint : IsIntegral ℤ y := by
    rw [← isIntegral_algHom_iff τ.toIntAlgHom τ.injective]
    change IsIntegral ℤ (τ y)
    rw [hy]
    exact hc
  refine ⟨⟨x, hxint⟩, hx, fun Q hQ hnot hxQ ↦ hnot ?_⟩
  have hxy : (⟨x, hxint⟩ : 𝓞 F) * ⟨y, hyint⟩ = RingOfIntegers.mapRingHom ι π ^ 12 := by
    ext
    change x * y = algebraMap (𝓞 F) F (RingOfIntegers.mapRingHom ι π ^ 12)
    rw [hy_def, mul_div_cancel₀ _ hx0, map_pow]
    rfl
  have hπQ : RingOfIntegers.mapRingHom ι π ∈ Q :=
    hQ.isPrime.mem_of_pow_mem 12 (hxy ▸ Q.mul_mem_right _ hxQ)
  have hle : Ideal.map (RingOfIntegers.mapRingHom ι) ((𝔭 : Ideal (𝓞 K)) ^ (n + 1)) ≤ Q := by
    rw [hπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hπQ
  rw [Ideal.map_pow] at hle
  have := hQ.isPrime
  exact Ideal.IsPrime.le_of_pow_le hle

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PowerIntegralStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def PowerIntegral.Statement : Prop :=
  ∀ (a s : ℝ), 0 < a → 1 / 2 < s →
    ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s) =
      √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * a ^ (1 - 2 * s)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.ShiftedSumIntegralStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def ShiftedSumIntegral.Statement : Prop :=
  ∀ (a u s : ℝ), 0 < a → 1 / 2 < s →
    Summable (fun n : ℤ ↦ (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s)) ∧
    |∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s) - ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s)| ≤
      a ^ (-2 * s)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

