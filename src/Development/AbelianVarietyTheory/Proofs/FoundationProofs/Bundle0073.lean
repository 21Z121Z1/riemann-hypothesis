import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0059
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
section
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_mem_span_of_trData : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C,
      (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  intro A S M _ _ _ _ _ B C tr n a b e ht D hD x hx
  set N : Submodule S M := Submodule.span S (D '' (B : Set S))
  have hD' : IsDerOn C (fun s => N.mkQ (D s)) :=
    { add := fun u hu v hv => by simp only [hD.add u hu v hv, map_add]
      mul := fun u hu v hv => by simp only [hD.mul u hu v hv, map_add, map_smul]
      alg := fun r => by simp only [hD.alg r, map_zero] }
  have hB : ∀ β ∈ B, N.mkQ (D β) = 0 := fun β hβ => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨β, hβ, rfl⟩
  have h := GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq A S (M ⧸ N) B C tr n a b e ht (fun s => N.mkQ (D s)) hD' hB x hx
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact h

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlane
section
open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ

theorem hs_isOpen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem hs_isPreconnected : IsPreconnected Hs :=
  (convex_halfSpace_im_gt (r := 0)).isPreconnected

theorem mero_eq_zero_of_eventually {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a Hs) {τ : ℂ} (hτ : τ ∈ Hs)
    (h : a =ᶠ[𝓝 τ] 0) : (a : Mero) = 0 := by
  have hE := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs_isPreconnected hτ h
  exact Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => hE hz)

theorem Tower.an_meromorphicAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K)
    (φ : ℂ → ℂ) (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero x
  have ha' : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd hs_isOpen
  have hb' : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd hs_isOpen

  rw [hφ] at hab
  have hrel : ∀ᶠ z in codiscreteWithin Hs, φ z * b z = a z := Filter.Germ.coe_eq.1 hab
  have hrel' : ∀ᶠ z in 𝓝[≠] τ, φ z * b z = a z := by
    have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hrel) τ hτ
    have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (hs_isOpen.mem_nhds hτ)
    filter_upwards [h1, h2] with z hz1 hz2
    rcases hz1 with hz1 | hz1
    · exact hz1
    · exact absurd hz2 hz1

  have hbne : ∀ᶠ z in 𝓝[≠] τ, b z ≠ 0 := by
    rcases (hb' τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (mero_eq_zero_of_eventually hb' hτ h) hb0
    · exact h
  have heq : (fun z => a z / b z) =ᶠ[𝓝[≠] τ] φ := by
    filter_upwards [hrel', hbne] with z h1 h2
    rw [← h1, mul_div_cancel_right₀ _ h2]
  have hmer : MeromorphicAt φ τ :=
    ((ha' τ hτ).meromorphicAt.div (hb' τ hτ).meromorphicAt).congr heq
  refine ⟨hmer, fun hx htop => ?_⟩
  have hφ0 : ∀ᶠ z in 𝓝[≠] τ, φ z = 0 := meromorphicOrderAt_eq_top_iff.1 htop
  have ha0 : ∀ᶠ z in 𝓝[≠] τ, a z = 0 := by
    filter_upwards [hrel', hφ0] with z h1 h2
    rw [← h1, h2, zero_mul]
  have ha00 : a =ᶠ[𝓝 τ] 0 := by
    rcases (ha' τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exact absurd ((ha0.and h).exists) (by rintro ⟨z, h1, h2⟩; exact h2 h1)
  have hA : (a : Mero) = 0 := mero_eq_zero_of_eventually ha' hτ ha00
  rw [← hφ, hA] at hab
  apply hb0
  have hu : X.an x⁻¹ * X.an x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  calc (b : Mero) = X.an x⁻¹ * X.an x * (b : Mero) := by rw [hu, one_mul]
    _ = X.an x⁻¹ * (X.an x * (b : Mero)) := by rw [mul_assoc]
    _ = 0 := by rw [hab, mul_zero]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongr
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem mono_sub_mem_of_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u v : Fin 2 → R)
    (h : ∀ i, u i - v i ∈ I) (a b : ℕ) : u 0 ^ a * u 1 ^ b - v 0 ^ a * v 1 ^ b ∈ I := by
  have h0 := Ideal.Quotient.eq.2 (h 0)
  have h1 := Ideal.Quotient.eq.2 (h 1)
  rw [← Ideal.Quotient.eq]
  simp only [map_mul, map_pow, h0, h1]

theorem Tower.B_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) (u v : Fin 2 → ℤ_[l])
    (huv : ∀ i, u i - v i ∈ (idl l) ^ n) :
    b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, hc⟩ := hx.1
    rw [hc u, hc v, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← sub_smul]
    exact Submodule.smul_mem_smul (mono_sub_mem_of_sub_mem _ u v huv _ _) Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simp only [Pi.add_apply]
    convert this using 1
    abel
  | smul r x _ hx =>
    simp only [Pi.smul_apply, ← smul_sub]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.KZ

example : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.B N l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, u i - v i ∈ (idl l) ^ n) → b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) :=
  fun X N l w _ b hb n u v h => Tower.B_sub_mem X N l w b hb n u v h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MonExp

noncomputable def ex (w : ℕ) (i : Fin (w + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))

theorem ex_zero (w : ℕ) (i : Fin (w + 1)) : ex w i 0 = i := by
  simp [ex]

theorem ex_one (w : ℕ) (i : Fin (w + 1)) : ex w i 1 = w - i := by
  simp [ex]

theorem ex_inj (w : ℕ) {i j : Fin (w + 1)} (h : ex w i = ex w j) : i = j := by
  apply Fin.ext
  have := congrArg (fun d => d 0) h
  simpa [ex_zero] using this

theorem mon_eq (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) :
    mon R w i = MvPolynomial.monomial (ex w i) 1 := by
  rw [mon, ex, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]

theorem C_mul_mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) (c : R) :
    MvPolynomial.C c * mon R w i = MvPolynomial.monomial (ex w i) c := by
  rw [mon_eq, MvPolynomial.C_mul_monomial, mul_one]

theorem coeff_sum_mon (R : Type) [CommRing R] (w : ℕ) (c : Fin (w + 1) → R) (j : Fin (w + 1)) :
    MvPolynomial.coeff (ex w j) (∑ i, MvPolynomial.C (c i) * mon R w i) = c j := by
  rw [MvPolynomial.coeff_sum]
  simp_rw [C_mul_mon, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h; exact hij (ex_inj w h)
  · simp

theorem mon_hom (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : (mon R w i).IsHomogeneous w := by
  have h := (MvPolynomial.isHomogeneous_X_pow (R := R) (0 : Fin 2) (i : ℕ)).mul
    (MvPolynomial.isHomogeneous_X_pow (R := R) (1 : Fin 2) (w - (i : ℕ)))
  have hi : (i : ℕ) + (w - (i : ℕ)) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.isLt)
  rw [hi] at h
  exact h

theorem hom_expand (R : Type) [CommRing R] (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    p = ∑ i : Fin (w + 1), MvPolynomial.C (MvPolynomial.coeff (ex w i) p) * mon R w i := by
  ext d
  by_cases hd : ∃ j : Fin (w + 1), ex w j = d
  · obtain ⟨j, rfl⟩ := hd
    rw [coeff_sum_mon]
  · have h0 : MvPolynomial.coeff d p = 0 := by
      apply hp.coeff_eq_zero
      intro hdeg
      apply hd
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      refine ⟨⟨d 0, by omega⟩, ?_⟩
      ext k
      fin_cases k
      · simp [ex_zero]
      · simp [ex_one]; omega
    rw [h0, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [C_mul_mon, MvPolynomial.coeff_monomial, if_neg]
    intro h; exact hd ⟨i, h⟩

theorem polySlash_monomial_isHomogeneous (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)) :
    (slP m (mon ℤ w k)).IsHomogeneous w := by
  have hl : ∀ j : Fin 2, ((m j 0 : ℤ) • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) +
      (m j 1 : ℤ) • MvPolynomial.X 1).IsHomogeneous 1 := by
    intro j
    have hs : ∀ (a : ℤ) (v : Fin 2), (a • (MvPolynomial.X v : MvPolynomial (Fin 2) ℤ)).IsHomogeneous 1 := by
      intro a v
      rw [MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) a).mul (MvPolynomial.isHomogeneous_X ℤ v)
    exact (hs _ 0).add (hs _ 1)
  have h := ((hl 0).pow (k : ℕ)).mul ((hl 1).pow (w - (k : ℕ)))
  have hi : 1 * (k : ℕ) + 1 * (w - (k : ℕ)) = w := by
    have := Nat.lt_succ_iff.mp k.isLt; omega
  rw [hi] at h
  simpa [slP, mon, map_mul, map_pow, MvPolynomial.aeval_X] using h

theorem map₃ (R : Type) [CommRing R] (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)) :
    MvPolynomial.map (Int.castRingHom R) (slP m (mon ℤ w k)) = slP m (mon R w k) := by
  simp [slP, mon, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.smul_eq_C_mul]

theorem map_mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map (Int.castRingHom R) (mon ℤ w i) = mon R w i := by
  simp [mon]

end GlobalTheory.KZ.MonExp

open GlobalTheory.KZ.MonExp in

theorem GlobalTheory.KZ.H3.mon_expand : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) p) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  intro R _ w
  refine ⟨?_, fun p hp => hom_expand R w p hp, mon_hom R w, ?_, ?_⟩
  · intro m k
    have hz := hom_expand ℤ w _ (polySlash_monomial_isHomogeneous w m k)
    rw [← map₃, hz, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.map_C, map_mon]
    rfl
  · intro u i
    simp [mon]
  · intro c hc
    funext j
    have := coeff_sum_mon R w c j
    rw [hc, MvPolynomial.coeff_zero] at this
    exact this.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSp
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_zero' (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ h
  rw [map_zero] at h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm h zero_le'
  rw [(valuation k).zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  rw [this, map_one]

section Blocks

variable {r t : ℕ}

theorem castAdd_eq_stdSum (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by
  ext; simp

theorem natAdd_eq_stdSum (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by
  ext; simp

theorem emb₂_std_apply (a : GL (Fin r) k) (b : GL (Fin t) k) (x y : Fin r ⊕ Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (stdSum rfl x) (stdSum rfl y) =
      fromBlocks a.val 0 0 b.val x y := by
  rw [val_emb₂]; simp

theorem emb₂_std_inv (a : GL (Fin r) k) (b : GL (Fin t) k) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))⁻¹ = emb₂ k (stdSum (rfl : r + t = r + t)) (a⁻¹, b⁻¹) := by
  rw [← map_inv]; rfl

theorem emb₂_mem_KO_iff (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ KO k (Fin (r + t)) ↔
      a ∈ KO k (Fin r) ∧ b ∈ KO k (Fin t) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, emb₂_std_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · have := h1 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h2 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h1 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
    · have := h2 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    refine ⟨fun p q => ?_, fun p q => ?_⟩
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a1 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b1 x y
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a2 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b2 x y

theorem ordered_castAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin r => ψ (Fin.castAdd t i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.castAdd t i) (Fin.castAdd t a) (Fin.castAdd t b) (Fin.castAdd t j)
    (Fin.le_def.2 (Fin.le_def.1 hia)) (Fin.le_def.2 (Fin.le_def.1 hab)) (Fin.le_def.2 (Fin.le_def.1 hbj)) x hx

theorem ordered_natAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin t => ψ (Fin.natAdd r i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.natAdd r i) (Fin.natAdd r a) (Fin.natAdd r b) (Fin.natAdd r j)
    ((Fin.natAdd_le_natAdd_iff r).2 hia) ((Fin.natAdd_le_natAdd_iff r).2 hab) ((Fin.natAdd_le_natAdd_iff r).2 hbj) x hx

theorem emb₂_mem_grp_iff (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔
      a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  unfold grp
  simp only [Set.mem_setOf_eq]
  rw [emb₂_mem_KO_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨⟨ha, fun i j hij => ?_⟩, ⟨hb, fun i j hij => ?_⟩⟩
    · have := h (Fin.castAdd t i) (Fin.castAdd t j) (Fin.lt_def.2 (Fin.lt_def.1 hij))
      rwa [castAdd_eq_stdSum i, castAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h (Fin.natAdd r i) (Fin.natAdd r j) ((Fin.natAdd_lt_natAdd_iff r).2 hij)
      rwa [natAdd_eq_stdSum i, natAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩
    refine ⟨⟨ha, hb⟩, fun p q hpq => ?_⟩
    obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
    obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
    rw [emb₂_std_apply]
    rcases x with x | x <;> rcases y with y | y
    · rw [fromBlocks_apply₁₁]
      have hxy : x < y := by
        rw [← castAdd_eq_stdSum, ← castAdd_eq_stdSum] at hpq
        exact Fin.lt_def.2 (Fin.lt_def.1 hpq)
      have := ha' x y hxy
      rwa [castAdd_eq_stdSum x, castAdd_eq_stdSum y] at this
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact triv_zero' _
    · exfalso
      have := Fin.lt_def.1 hpq
      rw [stdSum_inr, stdSum_inl] at this
      omega
    · rw [fromBlocks_apply₂₂]
      have hxy : x < y := by
        rw [← natAdd_eq_stdSum, ← natAdd_eq_stdSum] at hpq
        exact (Fin.natAdd_lt_natAdd_iff r).1 hpq
      have := hb' x y hxy
      rwa [natAdd_eq_stdSum x, natAdd_eq_stdSum y] at this

end Blocks

theorem block_diag_mem_grp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) :=
  fun _ _ _ _ _ _ _ ψ hψ _ => ⟨ordered_castAdd hψ, ordered_natAdd hψ, emb₂_mem_grp_iff ψ⟩

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
  ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  first | exact @GlobalTheory.norm_surjective_of_is_c1 | exact GlobalTheory.norm_surjective_of_is_c1 | (intros; apply GlobalTheory.norm_surjective_of_is_c1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeField
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem prod_pow_sub_pow_eq (g N : ℕ) :
    ∏ i ∈ Finset.range N, (g ^ N - g ^ i)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  have h1 : ∀ i ∈ Finset.range N, g ^ N - g ^ i = g ^ i * (g ^ (N - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Finset.prod_range_reflect (fun i => g ^ (i + 1) - 1) N]

theorem card_GG_eq (g : ℕ) [Fact g.Prime] (N : ℕ) :
    Fintype.card (GG g N)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  rw [← prod_pow_sub_pow_eq, ← Nat.card_eq_fintype_card]
  have h := Matrix.card_GL_field (𝔽 := ZMod g) N
  rw [ZMod.card] at h
  rw [← Fin.prod_univ_eq_prod_range (fun i => g ^ N - g ^ i) N]
  exact h

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardIrreducibleSamePrimeToPartRootsLeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_irreducible_samePrimeToPart_roots_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by
  first | exact @GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le | exact GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le | (intros; apply GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMonicSquarefreeUnitConstPolysGeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N → (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  first | exact @GlobalTheory.BadShare.card_sqSet_ge | exact GlobalTheory.BadShare.card_sqSet_ge | (intros; apply GlobalTheory.BadShare.card_sqSet_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermPartitionPartsMulCentralizerStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_perm_partition_parts_mul_centralizer : ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N → (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card * ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  first | exact @GlobalTheory.BadShare.card_perm_partition_parts_mul | exact GlobalTheory.BadShare.card_perm_partition_parts_mul | (intros; apply GlobalTheory.BadShare.card_perm_partition_parts_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleIsCoboundaryOfNegCentralElement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem cocycle_isCoboundary_of_neg_central : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ z : G → V, (∀ g, z g ∈ S) → (∀ g h, z (g * h) = ρ h (z g) + z h) → (∀ δ ∈ Δ, z δ = 0) → ∃ p ∈ S, ∀ g, z g = ρ g p - p := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔρ c hc hcomm z hzS hz hzΔ
  obtain ⟨u, hu⟩ := h2
  refine ⟨-((↑u⁻¹ : R) • z c), S.neg_mem (S.smul_mem _ (hzS c)), fun g => ?_⟩
  have key : ρ g (z c) + z g = -z g + z c := by
    have e1 : z (c * g) = z (g * c) := by
      have : c * g = (c * g * c⁻¹ * g⁻¹) * (g * c) := by group
      rw [this, hz, hzΔ _ (hcomm g), map_zero, zero_add]
    rw [hz, hz, hc _ (hzS g)] at e1
    exact e1
  have h2z : (2 : R) • z g = z c - ρ g (z c) := by
    rw [two_smul, ← sub_eq_zero]
    calc z g + z g - (z c - ρ g (z c)) = (ρ g (z c) + z g) - (-z g + z c) := by abel
      _ = 0 := sub_eq_zero.mpr key
  calc z g = ((↑u⁻¹ : R) * 2) • z g := by rw [← hu, Units.inv_mul, one_smul]
    _ = ρ g (-((↑u⁻¹ : R) • z c)) - -((↑u⁻¹ : R) • z c) := by
      rw [mul_smul, h2z, map_neg, map_smul, smul_sub]; abel

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapCommStatement
section
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R), normOp p (smap σ h) = smap σ (normOp p h) := by
  first | exact @GlobalTheory.Col.NormCoeff.normOp_smap | exact GlobalTheory.Col.NormCoeff.normOp_smap | (intros; apply GlobalTheory.Col.NormCoeff.normOp_smap <;> assumption)
end

