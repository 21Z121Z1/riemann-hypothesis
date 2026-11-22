import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.LatticeInvariants

lemma tsum_subtype_congr {p q : ℂ → Prop} (f : ℂ → ℂ) (h : ∀ w, f w ≠ 0 → (p w ↔ q w)) :
    ∑' w : {w // p w}, f w = ∑' w : {w // q w}, f w := by
  refine (tsum_subtype {w | p w} f).trans (Eq.trans ?_ (tsum_subtype {w | q w} f).symm)
  congr with w
  by_cases h0 : f w = 0
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h w h0]

lemma eisG_eq_tsum (Λ : AddSubgroup ℂ) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = ∑' w : Λ, ((w : ℂ) ^ (2 * k))⁻¹ := by
  simp only [eisG, one_div]
  refine tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0) (q := fun w ↦ w ∈ Λ)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w hw ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rintro rfl
  simp [hk] at hw

section

variable {L : PeriodPair} {Λ : AddSubgroup ℂ} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
include h

lemma eisG_eq_G {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  rw [eisG_eq_tsum Λ hk]
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w _ ↦ h w

lemma g2_eq : g2 Λ = L.g₂ := by rw [g2, eisG_eq_G h two_ne_zero]; rfl

lemma lattice_invariant_g3_eq : g3 Λ = L.g₃ := by rw [g3, eisG_eq_G h three_ne_zero]; rfl

lemma wpD_eq (z : ℂ) : wpD Λ z = L.derivWeierstrassP z := by
  rw [wpD, PeriodPair.derivWeierstrassP, neg_mul, ← tsum_mul_left]
  simp only [mul_one_div]
  congr 1
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ 2 / (z - w) ^ 3) fun w _ ↦ h w

lemma wpF_eq (z : ℂ) : wpF Λ z = L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, wpF, add_comm]
  congr 1
  · refine Eq.trans (tsum_congr fun w ↦ ?_) (tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0)
      (q := fun w ↦ w ∈ L.lattice)
      (fun w ↦ if w = 0 then 0 else 1 / (z - w) ^ 2 - 1 / w ^ 2) fun w hw ↦ ?_)
    · rw [if_neg w.2.2]
    · have : w ≠ 0 := by rintro rfl; simp at hw
      simp [h, this]
  · simp

lemma area_eq : area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  refine IsLeast.csInf_eq ⟨⟨?_, L.ω₂, (h _).2 L.ω₂_mem_lattice, L.ω₁, (h _).2 L.ω₁_mem_lattice,
    by rw [mul_comm]⟩, ?_⟩
  · rw [abs_pos]
    intro h0
    have hi := LinearIndependent.pair_iff.mp L.indep
    simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re] at h0
    have h1 := hi L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have h2 := hi L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have h3 : L.ω₂ = 0 := Complex.ext h1.1 h2.1
    simpa using (hi 0 1 (by simp [h3])).2
  · rintro a ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₁)
    obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₂)
    have e : (starRingEnd ℂ (m * L.ω₁ + n * L.ω₂) * (p * L.ω₁ + q * L.ω₂)).im =
        (n * p - m * q : ℤ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
      simp
      ring
    rw [e, abs_mul] at ha ⊢
    have h1 : (n * p - m * q : ℤ) ≠ 0 := by
      intro h0
      simp [h0] at ha
    have h2 : (1 : ℝ) ≤ |((n * p - m * q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact le_mul_of_one_le_left (abs_nonneg _) h2

end

lemma discrete_of_eisG_ne_zero {Λ : AddSubgroup ℂ} {k : ℕ} (hk : k ≠ 0) (h : eisG Λ k ≠ 0) :
    DiscreteTopology Λ := by
  rw [eisG_eq_tsum Λ hk] at h
  have hs : Summable fun w : Λ ↦ ((w : ℂ) ^ (2 * k))⁻¹ := by
    by_contra hs
    exact h (tsum_eq_zero_of_not_summable hs)
  have hf : {w : Λ | ¬ ‖((w : ℂ) ^ (2 * k))⁻¹‖ < 1}.Finite :=
    Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually_lt_const one_pos)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ?_
  have ho : IsOpen {w : Λ | ‖(w : ℂ)‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  convert ho.sdiff hf.isClosed using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_not]
  constructor
  · rintro rfl
    simp [hk]
  · rintro ⟨h1, h2⟩
    by_contra h0
    have h3 : 0 < ‖(w : ℂ)‖ := by simpa using h0
    rw [norm_inv, norm_pow] at h2
    exact absurd h2 (not_lt.2 ((one_le_inv₀ (by positivity)).2 (pow_le_one₀ h3.le h1.le)))

lemma eisG_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ) (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = (a ^ (2 * k))⁻¹ * (2 * riemannZeta (2 * k : ℕ)) := by
  rw [eisG_eq_tsum Λ hk]
  rcases eq_or_ne a 0 with rfl | h0
  · have : ∀ w : Λ, (w : ℂ) = 0 := fun w ↦ by simpa [eq_comm] using h w w.2
    simp [this, hk]
  let e : ℤ → Λ := fun m ↦ ⟨m • a, Λ.zsmul_mem ha m⟩
  have he : Function.Bijective e := ⟨fun m n hmn ↦ by simpa [e, h0] using hmn,
    fun w ↦ (h w w.2).imp fun m hm ↦ Subtype.ext hm⟩
  rw [← (Equiv.ofBijective e he).tsum_eq,
    two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by omega) (even_two_mul k), ← tsum_mul_left]
  congr with m
  simp [e, mul_pow]

lemma discr_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ)
    (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w) : TaylorLogMetric.discr Λ = 0 := by
  have h6 : riemannZeta 6 = Real.pi ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [TaylorLogMetric.discr, g2, g3, eisG_of_cyclic ha h two_ne_zero, eisG_of_cyclic ha h three_ne_zero]
  norm_num only [riemannZeta_four, h6]
  simp only [← inv_pow]
  ring

lemma exists_periodPair_of_discr_ne_zero {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  have hd : DiscreteTopology Λ := by
    by_cases h2 : eisG Λ 2 = 0
    · refine discrete_of_eisG_ne_zero three_ne_zero fun h3 ↦ h ?_
      simp [TaylorLogMetric.discr, g2, g3, h2, h3]
    · exact discrete_of_eisG_ne_zero two_ne_zero h2
  let M : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule Λ
  have hM : DiscreteTopology M := hd
  by_cases hs : Submodule.span ℝ (M : Set ℂ) = ⊤
  · have hZ : IsZLattice ℝ M := ⟨hs⟩
    let b := Module.finBasisOfFinrankEq ℤ M ((ZLattice.rank ℝ M).trans Complex.finrank_real_complex)
    have hi := (b.ofZLatticeBasis ℝ M).linearIndependent
    have e : ⇑(b.ofZLatticeBasis ℝ M) = ![(b 0 : ℂ), b 1] := by
      ext i
      fin_cases i <;> simp
    refine ⟨⟨b 0, b 1, e ▸ hi⟩, fun z ↦ ?_⟩
    change z ∈ M ↔ z ∈ Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)}
    rw [← Matrix.range_cons_cons_empty _ _ ![], ← e, b.ofZLatticeBasis_span ℝ M]
  · have h1 : Module.finrank ℤ M ≤ 1 := by
      have e := Real.finrank_eq_int_finrank_of_discrete (s := (M : Set ℂ))
        (by rw [Submodule.span_eq]; exact hM)
      rw [Set.finrank, Set.finrank, Submodule.span_eq] at e
      have := Submodule.finrank_lt hs
      rw [Complex.finrank_real_complex] at this
      omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
    exact absurd (discr_of_cyclic (a := v) v.2 fun w hw ↦
      (hv ⟨w, hw⟩).imp fun m hm ↦ congrArg Subtype.val hm) h

lemma exists_periodPair_of_invariants {a b : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq (1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
  let L := periodPairOfTau τ
  have h1 := g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_periodPairOfTau τ)
  have h0 := g₂_cube_sub_g₃_sq_ne_zero L
  rw [modularJ_def, hτ, div_eq_div_iff h0 h] at h1
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq h0 h (by linear_combination h1 / 1728)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  refine ⟨scalePeriods L c hc0, ?_, ?_⟩
  · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
  · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp

theorem invariants_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  intro L Λ h
  have hΔ : TaylorLogMetric.discr Λ ≠ 0 := by
    rw [TaylorLogMetric.discr, g2_eq h, lattice_invariant_g3_eq h]
    exact g₂_cube_sub_g₃_sq_ne_zero L
  refine ⟨g2_eq h, lattice_invariant_g3_eq h, hΔ, area_eq h, fun z _ ↦ ⟨wpF_eq h z, wpD_eq h z⟩,
    fun Λ' h2 h3 ↦ ?_, fun a b ↦ exists_periodPair_of_invariants⟩
  obtain ⟨L', h'⟩ := exists_periodPair_of_discr_ne_zero (Λ := Λ')
    (by rwa [TaylorLogMetric.discr, h2, h3])
  rw [g2_eq h, g2_eq h'] at h2
  rw [lattice_invariant_g3_eq h, lattice_invariant_g3_eq h'] at h3
  ext z
  rw [h, h', lattice_eq_of_g₂_eq_of_g₃_eq h2 h3]

end GlobalTheory.LatticeInvariants
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalBasisLatticeIndexCoprime
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.LocIndex

theorem index_coprime_of_multiples {G : Type*} [AddCommGroup G] [AddGroup.FG G] (H : AddSubgroup G) (p : ℕ)
    (hp : p.Prime) (h : ∀ z : G, ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ H) : Nat.Coprime H.index p := by
  have hq : ∀ x : G ⧸ H, ∃ s : ℕ, Nat.Coprime s p ∧ s • x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨s, hs, hz⟩ := h z
    refine ⟨s, hs, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hz
  have htor : AddMonoid.IsTorsion (G ⧸ H) := by
    intro x
    obtain ⟨s, hs, hx⟩ := hq x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨s, Nat.pos_of_ne_zero ?_, hx⟩
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hs)
  haveI : Finite (G ⧸ H) := AddCommGroup.finite_of_fg_torsion _ htor
  haveI := Fact.mk hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G ⧸ H) p hd
  obtain ⟨s, hs, hs0⟩ := hq x
  have : p ∣ s := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hs0
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm this

theorem mul_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) {w : ℂ}
    (hw : w ∈ lamOf D cc δ) : w * D.host.φ₀ ((a : D.host.K) : D.host.E) ∈ lamOf D cc δ := by
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨c * a, cc.mul_mem_right a hc, ?_⟩
    rw [mul_assoc, ← map_mul]
    congr 2
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem exists_multiple_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) (hb : LocBasis D p (YYl D L L') b)
    (z : VC D N N') (hz : z ∈ La D (tor0 D cc δ) L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ LaB D (tor0 D cc δ) b := by
  unfold La at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 A hA
    refine ⟨s, hs, ?_⟩
    have key : s • w • embV D (tor0 D cc δ) A =
        ∑ i, (w * D.host.φ₀ ((c i : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) (b i) := by
      funext τ i j
      have h1 := congrArg (fun M => embT D τ (M i j)) hc
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.sum_apply, map_sum] at h1
      simp only [hD.1 τ] at h1
      simp only [Pi.smul_apply, Finset.sum_apply, embV, tor0, smul_eq_mul, nsmul_eq_mul]
      rw [mul_left_comm, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [key]
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, mul_mem_lamOf D cc δ (c i) hw, i, rfl⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx t
    · rw [mul_smul]; exact nsmul_mem hy s
  | neg x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, by rw [smul_neg]; exact neg_mem hx⟩

theorem index_coprime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ), p.Prime → (La D (tor0 D cc δ) L L').FG → LocBasis D p (YYl D L L') b → Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La D (tor0 D cc δ) L L')).index) p := by
  intro D hD cc δ N N' r L L' b p hp hfg hb
  haveI : AddGroup.FG (La D (tor0 D cc δ) L L') := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine index_coprime_of_multiples _ p hp fun z => ?_
  obtain ⟨s, hs, hz⟩ := exists_multiple_mem D hD cc δ L L' b p hb z.1 z.2
  exact ⟨s, hs, AddSubgroup.mem_addSubgroupOf.2 hz⟩

end GlobalTheory.NormSum.LocIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.BlochKatoBaseChangeLe

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem mem_HfD_gen {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    (L : Lattice (O := O) ρ) (w : G → V ⧸ L.T) :
    w ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ m : V, ∀ g, w g = Submodule.Quotient.mk (z g + (ρ g m - m)) := by
  constructor
  · intro h
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨z, hz, m, fun g => rfl⟩
  · rintro ⟨z, hz, m, h⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk m, rfl⟩, ?_⟩
    funext g
    exact (h g).symm

set_option synthInstance.maxHeartbeats 400000 in
omit [IsDomain O] in

theorem mem_HfD_iff (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (w : ↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) :
    w ∈ HfD (P.PD B.Kw) (Br.lat B M) ↔
      ∃ z ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)), ∃ m : Fin k → Br.LLw B, ∀ g,
        w g = Submodule.Quotient.mk (z g + ((Br.locM B M g).mulVec m - m)) :=
  mem_HfD_gen (P.PD B.Kw) (Br.lat B M) w

set_option synthInstance.maxHeartbeats 400000 in

def transport (B : LocBridge l E Ω Gw O) (k : ℕ) :
    (↥Gw → KOG O k) →ₛₗ[B.eO.toRingHom]
      (↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) where
  toFun c g := Br.phi B k (c (Br.ι B g))
  map_add' a b := by
    funext g
    exact (Br.phi B k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi B k).map_smulₛₗ c _

theorem locM_apply (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (i j : Fin k) :
    Br.locM B M g i j = Br.toLLK B (algebraMap O (FractionRing O) (M (Br.ι B g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS B k ((mapM (algebraMap O (FractionRing O)) M (Br.ι B g)).mulVec u) =
      (Br.locM B M g).mulVec (Br.vecS B k u) := by
  funext i
  change Br.toLLK B (∑ j, algebraMap O (FractionRing O) (M (Br.ι B g) i j) * u j) =
    ∑ j, Br.locM B M g i j * Br.toLLK B (u j)
  simp only [map_sum, map_mul, locM_apply]

set_option synthInstance.maxHeartbeats 400000 in

theorem phi_mem_of_mem_bkG (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (c : ↥(Z1 (WKG M))) (hc : Submodule.Quotient.mk c ∈ Br.bkG B P (WKG M) M) :
    Br.Phi B (WKG M) c ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
  obtain ⟨c₁, h₁, he⟩ := hc
  have he' : c₁ - c ∈ (ReciprocityTheory.Gal.B1 (WKG M)).comap (Z1 (WKG M)).subtype :=
    (Submodule.Quotient.eq _).1 he
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 he'
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hB : Br.Phi B (WKG M) (c₁ - c) ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
    refine (mem_HfD_iff P B M _).2 ⟨0, Submodule.zero_mem _, Br.vecS B k u, fun g => ?_⟩
    have := congrArg (Br.phi B k) (hx (Br.ι B g))
    refine this.trans ?_
    rw [Pi.zero_apply, zero_add, ← vecS_mulVec, ← map_sub]
    rfl
  have h2 : c = c₁ - (c₁ - c) := by abel
  rw [h2, map_sub]
  exact Submodule.sub_mem _ h₁ hB

set_option synthInstance.maxHeartbeats 400000 in

theorem push_mem (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c₀ : ↥Gw → KOG O₀ k)
    (hc : (fun g => Br.phi B₀ k (c₀ (Br.ι B₀ g))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀)) :
    (fun g => Br.phi B k (pushKO f hf k (c₀ (Br.ι B g)))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀)) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  obtain ⟨z, hzf, m, h⟩ := (mem_HfD_iff P B₀ M₀ _).1 hc
  let θ : ↥(GK B.Kw) →* ↥(GK B₀.Kw) := B₀.e.toMonoidHom.comp (Br.ι B)
  have hθι : ∀ g, Br.ι B₀ (θ g) = Br.ι B g := fun g => B₀.e.symm_apply_apply _
  have hθ : Continuous θ := B₀.e_cont.comp (Br.ι_cont B)
  have hσ' : ∀ g : ↥(GK B.Kw), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹ := fun g => by
    have := hσ (Br.ι B g)
    rwa [show B.e (Br.ι B g) = g from B.e.apply_symm_apply g] at this
  have hp : ∀ g (v : Fin k → ↥B₀.LL.1), (fun j => φ ((Br.locM B₀ M₀ (θ g)).mulVec v j)) =
      (Br.locM B (mapM f M₀) g).mulVec fun j => φ (v j) := by
    intro g v
    funext i
    change φ (∑ j, Br.locM B₀ M₀ (θ g) i j * v j) = ∑ j, Br.locM B (mapM f M₀) g i j * φ (v j)
    simp only [map_sum, map_mul, locM_apply, hφ, fracMap_alg, hθι]
    rfl
  refine (mem_HfD_iff P B _ _).2 ⟨_, crystallineCocycle_transport_conjugation P B₀.Kw B.Kw B₀.LL B.LL θ hθ σ hσ' _ _ φ.toLinearMap hp z hzf,
    fun j => φ (m j), fun g => ?_⟩
  have hg := h (θ g)
  simp only [hθι] at hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (c₀ (Br.ι B g))
  rw [← hu] at hg ⊢
  obtain ⟨n, hn⟩ : Br.vecS B₀ k u - (z (θ g) + ((Br.locM B₀ M₀ (θ g)).mulVec m - m)) ∈
      stdG (Br.Ow B₀) (Br.LLw B₀) k := (Submodule.Quotient.eq _).1 hg
  refine (Submodule.Quotient.eq (stdG (Br.Ow B) (Br.LLw B) k)).2
    ⟨fun j => B.eO (f (B₀.eO.symm (n j))), ?_⟩
  funext j
  have h1 := congrArg φ (congrFun hn j)
  have h2 : algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j) =
      Br.toLLK B₀ (algebraMap O₀ (FractionRing O₀) (B₀.eO.symm (n j))) := by
    rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  change φ (algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j)) =
    φ (Br.toLLK B₀ (u j) - (z (θ g) j + ((Br.locM B₀ M₀ (θ g)).mulVec m j - m j))) at h1
  rw [h2, hφ, fracMap_alg, Br.toLLK_alg, map_sub, map_add, map_sub, hφ, congrFun (hp g m) j] at h1
  exact h1

set_option synthInstance.maxHeartbeats 400000 in

theorem extCond_le_bkG : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l), (∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹) → ∀ (f : O₀ →+* O) (hf : Function.Injective f), (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) → ∀ (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀), extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) ≤ Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) := by
  intro l _ P E Ω _ _ _ Gw O₀ O _ _ _ _ _ _ _ _ _ _ _ _ B₀ B σ hσ f hf hz k M₀
  refine Submodule.map_mono ?_
  intro c hc
  have key : Submodule.span O {c : ↥Gw → KOG O k | ∃ c₀ : Z1 (WKG M₀),
      Submodule.Quotient.mk c₀ ∈ Br.bkG B₀ P (WKG M₀) M₀ ∧
      c = fun g => pushKO f hf k ((c₀ : ↥Gw → KOG O₀ k) g)} ≤
      (HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))).comap (transport B k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c₀, h₀, rfl⟩
    exact push_mem P B₀ B σ hσ f hf hz M₀ c₀ (phi_mem_of_mem_bkG P B₀ M₀ c₀ h₀)
  exact key hc

end GlobalTheory.BlochKatoBaseChangeLe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMap
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem aut_conj_comm (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E) :
    σ (D.host.conj x) = D.host.conj (σ x) := by
  have h : σ * D.host.conj = D.host.conj * σ :=
    (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg (fun f : D.host.E ≃ₐ[ℚ] D.host.E => f x) h

theorem hYY_map_aut (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (x.map σ) (y.map σ) = hYY D x y := by
  let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
  unfold hYY
  rw [← Algebra.trace_eq_of_algEquiv e (∑ i, ∑ j, x i j * D.host.conj (y i j))]
  congr 1
  show _ = σ _
  simp only [map_sum, map_mul, Matrix.map_apply, aut_conj_comm]

theorem onB_map_aut : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) →
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  intro D σ hσ N N' r b hb
  refine ⟨?_, ?_⟩
  · intro i j
    rw [hYY_map_aut D σ hσ]
    exact hb.1 i j
  · let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
    let L : Matrix (Fin N') (Fin N) D.host.E ≃ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E :=
      e.toLinearEquiv.mapMatrix
    have h : (fun j => (b j).map σ) = L.toLinearMap ∘ b := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, hb.2, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.NormSum
end

