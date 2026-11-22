import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

-- bundled from Development.AutomorphicArithmetic.PrimeDiscriminants.BadPrimes
section
open NumberField

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem bad_subset : Nat.primeFactors (2 * (discr H.E).natAbs) ⊆ H.small ∪ {H.q, H.d} := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hc : p ∣ H.condN := by
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h2 | h2
    · rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h2]
      exact H.two_dvd_condN
    · exact H.der.discr_primes.1 p hpp (Int.natCast_dvd.2 h2)
  rcases (H.dvd_condN_iff_small hpp).1 hc with h | h | h
  · exact Finset.mem_union_left _ h
  · simp [h]
  · simp [h]

theorem card_small_gt_le_one {B : ℝ} (hB : (R.n : ℝ) ≤ B) : (H.small.filter fun p : ℕ => B < (p : ℝ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  rw [Finset.mem_filter, H.mem_small_iff] at hp hp'
  by_contra hne
  have hpn : R.n < p := by exact_mod_cast hB.trans_lt hp.2
  have hpn' : R.n < p' := by exact_mod_cast hB.trans_lt hp'.2
  have hdvd : p * p' ∣ H.QS :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp.1.1 hp'.1.1).2 hne) hp.1.2 hp'.1.2
  have hle := Nat.le_of_dvd H.QS_pos hdvd
  have hq := H.QS_le
  have hm : R.n * R.n < p * p' := Nat.mul_lt_mul'' hpn hpn'
  rw [sq] at hq
  linarith

theorem card_gt_le_card_sdiff (S : Finset ℕ) {B : ℝ} (hB : (R.n : ℝ) ≤ B) :
    (S.filter fun p : ℕ => B < (p : ℝ)).card ≤ (S \ H.small).card + 1 := by
  calc (S.filter fun p : ℕ => B < (p : ℝ)).card
      ≤ ((S \ H.small) ∪ H.small.filter fun p : ℕ => B < (p : ℝ)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_filter] at hp
        by_cases hs : p ∈ H.small
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hs, hp.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hp.1, hs⟩)
    _ ≤ (S \ H.small).card + (H.small.filter fun p : ℕ => B < (p : ℝ)).card :=
        Finset.card_union_le _ _
    _ ≤ (S \ H.small).card + 1 := by
        have h1 := card_small_gt_le_one H hB
        omega

theorem card_bad_sdiff_le (S : Finset ℕ) :
    ((Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S) \ H.small).card ≤ S.card + 2 := by
  calc _ ≤ (S ∪ {H.q, H.d}).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_sdiff, Finset.mem_union] at hp
        rcases hp.1 with h | h
        · have hb := bad_subset H h
          rw [Finset.mem_union] at hb
          rcases hb with h' | h'
          · exact absurd h' hp.2
          · exact Finset.mem_union_right _ h'
        · exact Finset.mem_union_left _ h
    _ ≤ S.card + ({H.q, H.d} : Finset ℕ).card := Finset.card_union_le _ _
    _ ≤ S.card + 2 := by
        have h2 : ({H.q, H.d} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        omega

theorem card_bad_gt_le (S : Finset ℕ) {B : ℝ} (hB : (R.n : ℝ) ≤ B) :
    ((Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S).filter fun p : ℕ => B < (p : ℝ)).card ≤ S.card + 3 := by
  have := H.card_gt_le_card_sdiff (Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S) hB
  have := H.card_bad_sdiff_le S
  omega

theorem log_n_le_two_log_rdE : Real.log (R.n : ℝ) ≤ 2 * Real.log H.rdE := by
  have h1 : (4 : ℝ) * (R.n : ℝ) ≤ H.rdE ^ 2 := H.der.rd_sq_ge
  have hn : (0 : ℝ) < R.n := by exact_mod_cast R.toFrame.ord_pos
  have h2 : (R.n : ℝ) ≤ H.rdE ^ 2 := by linarith
  calc Real.log R.n ≤ Real.log (H.rdE ^ 2) := Real.log_le_log hn h2
    _ = 2 * Real.log H.rdE := by
      rw [Real.log_pow]
      push_cast
      ring

theorem sum_small_log_le : ∑ p ∈ H.small, Real.log p ≤ 4 * Real.log H.rdE := by
  have hprod : ∏ p ∈ H.small, p ≤ H.QS := Nat.le_of_dvd H.QS_pos (Nat.prod_primeFactors_dvd _)
  have hpos : ∀ p ∈ H.small, (0 : ℝ) < p := fun p hp => by
    have hp' := ((H.mem_small_iff).1 hp).1.pos
    exact_mod_cast hp'
  rw [← Real.log_prod (s := H.small) (f := fun p : ℕ => (p : ℝ)) (fun p hp => (hpos p hp).ne')]
  have hP : (0 : ℝ) < ∏ p ∈ H.small, (p : ℝ) := Finset.prod_pos hpos
  calc Real.log (∏ p ∈ H.small, (p : ℝ)) ≤ Real.log ((R.n : ℝ) ^ 2) := by
        apply Real.log_le_log hP
        have h' : (∏ p ∈ H.small, p : ℕ) ≤ R.n ^ 2 := hprod.trans H.QS_le
        have h'' := (Nat.cast_le (α := ℝ)).2 h'
        push_cast at h''
        exact h''
    _ = 2 * Real.log R.n := by
        rw [Real.log_pow]
        push_cast
        ring
    _ ≤ 4 * Real.log H.rdE := by
        have h6 := log_n_le_two_log_rdE H
        linarith

end Formalism.BasicNotions.Host
end

-- bundled from Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
section
open NumberField

noncomputable section

namespace UpperTheory

section field

variable (E : Type) [Field E] [NumberField E]

theorem exists_primitiveRoot_torsionOrder : ∃ ζ : E, IsPrimitiveRoot ζ (Units.torsionOrder E) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Units.torsion E, orderOf μ = Units.torsionOrder E :=
    IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion E)
  refine ⟨(((μ : (𝓞 E)ˣ) : 𝓞 E) : E), ?_⟩
  have h1 : IsPrimitiveRoot μ (Units.torsionOrder E) := hμ ▸ IsPrimitiveRoot.orderOf μ
  have h2 : IsPrimitiveRoot (μ : (𝓞 E)ˣ) (Units.torsionOrder E) := IsPrimitiveRoot.coe_submonoidClass_iff.2 h1
  exact (IsPrimitiveRoot.coe_units_iff.2 h2).map_of_injective (f := algebraMap (𝓞 E) E) RingOfIntegers.coe_injective

variable {E}

theorem root_iff_pow_torsionOrder (x : E) : (∃ m : ℕ, 0 < m ∧ x ^ m = 1) ↔ x ^ Units.torsionOrder E = 1 := by
  refine ⟨fun h => ?_, fun h => ⟨_, Units.torsionOrder_pos E, h⟩⟩
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 h
  have : NeZero (orderOf x) := ⟨(orderOf_pos_iff.2 hfin).ne'⟩
  exact orderOf_dvd_iff_pow_eq_one.1 (Units.dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf x))

theorem two_dvd_torsionOrder : 2 ∣ Units.torsionOrder E := (Units.even_torsionOrder E).two_dvd

theorem torsionOrder_dvd_of_algHom (N : ℕ) (hN : Even N) (hN0 : 0 < N) (ψ : E →ₐ[ℚ] CyclotomicField N ℚ) :
    Units.torsionOrder E ∣ N := by
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero (Units.torsionOrder E) := ⟨(Units.torsionOrder_pos E).ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
  have h := Units.dvd_torsionOrder_of_isPrimitiveRoot (hζ.map_of_injective (f := ψ) ψ.toRingHom.injective)
  rwa [IsCyclotomicExtension.Rat.torsionOrder_eq (n := N) (K := CyclotomicField N ℚ), if_pos hN] at h

theorem roots_pm_iff : (∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1) ↔ Units.torsionOrder E = 2 := by
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
    refine Nat.dvd_antisymm (hζ.dvd_of_pow_eq_one 2 ?_) two_dvd_torsionOrder
    rcases h ζ ⟨_, Units.torsionOrder_pos E, hζ.pow_eq_one⟩ with rfl | rfl <;> norm_num
  · intro h x hx
    rw [root_iff_pow_torsionOrder, h] at hx
    exact mul_self_eq_one_iff.1 (by rwa [← sq])

end field

end UpperTheory

namespace Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def w : ℕ := Units.torsionOrder H.E

def nuW (l : ℕ) : ℕ := H.w.factorization l

def IsMu (x : H.E) : Prop := ∃ m : ℕ, 0 < m ∧ x ^ m = 1

theorem w_pos : 0 < H.w := Units.torsionOrder_pos H.E

theorem two_dvd_w : 2 ∣ H.w := UpperTheory.two_dvd_torsionOrder

theorem two_le_w : 2 ≤ H.w := Nat.le_of_dvd H.w_pos H.two_dvd_w

theorem isMu_iff (x : H.E) : H.IsMu x ↔ x ^ H.w = 1 := UpperTheory.root_iff_pow_torsionOrder x

theorem exists_primitiveRoot_w : ∃ ζ : H.E, IsPrimitiveRoot ζ H.w := UpperTheory.exists_primitiveRoot_torsionOrder H.E

theorem muPM_iff : H.MuPM ↔ H.w = 2 := UpperTheory.roots_pm_iff

theorem MuPM.nuW (h : H.MuPM) (l : ℕ) : H.nuW l = if l = 2 then 1 else 0 := by
  unfold HostRaw.nuW
  rw [H.muPM_iff.1 h, Nat.prime_two.factorization, Finsupp.single_apply]
  simp only [eq_comm]

theorem w_dvd_condN : H.w ∣ H.condN :=
  UpperTheory.torsionOrder_dvd_of_algHom H.condN (even_iff_two_dvd.2 H.two_dvd_condN) (Nat.pos_of_ne_zero H.condN_ne_zero) H.cycEmb

theorem sum_nuW_mul_log_le (S : Finset ℕ) : ∑ l ∈ S, (H.nuW l : ℝ) * Real.log l ≤ Real.log H.w := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have h0 : ∀ l : ℕ, 0 ≤ (H.w.factorization l : ℝ) * Real.log l := fun l => by positivity
  calc ∑ l ∈ S, (H.nuW l : ℝ) * Real.log l
      = ∑ l ∈ S ∩ H.w.factorization.support, (H.w.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.inter_subset_left fun l hl hl' => ?_).symm
        have : H.w.factorization l = 0 := by
          by_contra h
          exact hl' (Finset.mem_inter.2 ⟨hl, Finsupp.mem_support_iff.2 h⟩)
        simp [HostRaw.nuW, this]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun l _ _ => h0 l

end Formalism.HC.HostRaw

end
end

-- bundled from Development.AutomorphicArithmetic.PrimeDiscriminants.MuParallel
section
noncomputable section

namespace UpperTheory.Host

open Formalism.BasicNotions NumberField

variable {R : Ranks} (H : Host R)

def psiEquiv : R.Psi ≃ (H.E ≃ₐ[H.K] H.E) where
  toFun g :=
    { (H.sigmaOf (g : R.GG) : H.E ≃+* H.E) with
      commutes' := fun x => by
        have h1 : H.sigmaOf (g : R.GG) H.sqd = H.sqd :=
          (H.galE_mem_Psi_iff _).1 (by rw [show H.galE (H.sigmaOf (g : R.GG)) = g from H.gal.apply_symm_apply _]; exact g.2)
        have h2 : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf (g : R.GG))) := by
          refine IntermediateField.adjoin_simple_le_iff.2 ?_
          rw [IntermediateField.mem_fixedField_iff]
          intro f hf
          exact (Subgroup.zpowers_le.2 (show H.sigmaOf (g : R.GG) ∈ MulAction.stabilizer _ H.sqd from h1)) hf
        exact (IntermediateField.mem_fixedField_iff _ _).1 (h2 x.2) _ (Subgroup.mem_zpowers _) }
  invFun σ := ⟨H.gal (σ.restrictScalars ℚ), (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, H.sqd_mem_K⟩)⟩
  left_inv g := Subtype.ext (H.gal.apply_symm_apply (g : R.GG))
  right_inv σ := AlgEquiv.ext fun x => by
    show H.gal.symm (H.gal (σ.restrictScalars ℚ)) x = σ x
    rw [MulEquiv.symm_apply_apply]
    rfl

theorem prod_sigmaOf [Fintype R.Psi] (x : H.E) :
    ∏ g : R.Psi, H.sigmaOf (g : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.hostE_isGalois
  rw [Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_equiv (psiEquiv H) _ _ fun g => rfl

theorem mu_one [Fintype R.Psi] : UpperTheory.MU (fun g : R.Psi => H.emb (g : R.GG)) (fun _ => 1) := by
  intro z hz
  have h1 : ∀ g : R.Psi, H.emb (g : R.GG) z ^ (1 : ℤ) = H.φ₀ (H.sigmaOf (g : R.GG) z) := fun g => zpow_one _
  simp only [h1]
  rw [← map_prod, prod_sigmaOf, H.der.norm_mu z hz, map_one, map_one]

theorem muQ_const [Fintype R.Psi] {e : R.Psi → ℚ} {c : ℤ} (h : ∀ g, e g = c) :
    UpperTheory.MUQ (fun g : R.Psi => H.emb (g : R.GG)) e :=
  ⟨fun _ => c, h, (mu_one H).const c⟩

end UpperTheory.Host

end
end

-- bundled from Development.AutomorphicArithmetic.PrimeDiscriminants.SmallRam
section
open NumberField IsDedekindDomain Ideal

noncomputable section

namespace Formalism.HC.HostAx

variable {φ : Frame} (H : HostAx φ)

theorem mem_sq_of_dvd_QS (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) (P : Ideal (𝓞 H.E)) [hP : P.IsPrime]
    (hm : (l : 𝓞 H.E) ∈ P) : (l : 𝓞 H.E) ∈ P ^ 2 := by
  have hEgal := H.galois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have : Fact l.Prime := ⟨hl⟩
  have hlz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have hsp : (span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlz.ne_zero).2 hlz
  have hne : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hlz.ne_zero
  have hlo : P.LiesOver (span {(l : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hlz).2 (by simpa using hm)
  obtain ⟨u, hu, hu1⟩ := hE l hl hd
  have hN : l ∣ H.condN := hd.trans H.QS_dvd_condN
  have hdiv : ordCompl[l] H.condN ∣ H.condN / l := by
    have h1 : 1 ≤ H.condN.factorization l := (hl.dvd_iff_one_le_factorization H.condN_ne_zero).1 hN
    exact Nat.div_dvd_div_left (Nat.ordProj_dvd _ _) (by simpa using pow_dvd_pow l h1)
  have hin : ∀ x : 𝓞 H.E, H.gal.symm (H.art u) • x - x ∈ P :=
    (H.der.inertia l P _).2 ⟨u, hu.of_dvd hdiv, H.gal.apply_symm_apply _⟩
  have hnt : 1 < Nat.card (P.inertia Gal(H.E/ℚ)) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨⟨⟨_, AddSubgroup.mem_inertia.2 hin⟩, 1, fun h1 => hu1 ?_⟩⟩
    have h2 : H.gal.symm (H.art u) = 1 := congrArg Subtype.val h1
    simpa using congrArg H.gal h2
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ),
    ← ramificationIdx'_eq_ramificationIdx (span {(l : ℤ)}) P hne] at hnt
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (span {(l : ℤ)}) ≤ P ^ 2 := le_pow_of_le_ramificationIdx' hnt
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at hle
  simpa using hle

theorem QS_notMem (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) : (H.QS : 𝓞 H.E) ∉ P.asIdeal := by
  have hP := P.isPrime
  have hpm : (p : 𝓞 H.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
    exact card_nsmul_eq_zero'
  intro hm
  by_cases hd : p ∣ H.QS
  · exact h2 (H.mem_sq_of_dvd_QS hE hp hd P.asIdeal hpm)
  · have hcop : IsCoprime ((p : ℕ) : 𝓞 H.E) ((H.QS : ℕ) : 𝓞 H.E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hd).cast
    obtain ⟨a, b, hab⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left a hpm) (P.asIdeal.mul_mem_left b hm)))

theorem condN_mul_notMem (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) {T : ℕ}
    (h : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by
  intro hm
  have e : ((H.condN * T : ℕ) : 𝓞 H.E) = (H.QS : 𝓞 H.E) * ((H.q * H.d * T : ℕ) : 𝓞 H.E) := by
    simp only [HostRaw.condN]; push_cast; ring
  rw [e] at hm
  rcases P.isPrime.mem_or_mem hm with h1 | h1
  · exact H.QS_notMem hE P hp hc h2 h1
  · refine h ?_
    have e' : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) = 2 * ((H.q * H.d * T : ℕ) : 𝓞 H.E) := by push_cast; ring
    rw [e']
    exact P.asIdeal.mul_mem_left _ h1

theorem two_mul_notMem_of_condN (P : HeightOneSpectrum (𝓞 H.E)) {T : ℕ}
    (h : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨c, hc⟩ := H.two_dvd_QS
  refine h ?_
  have e : ((H.condN * T : ℕ) : 𝓞 H.E) = (c : 𝓞 H.E) * ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) := by
    simp only [HostRaw.condN]; rw [hc]; push_cast; ring
  rw [e]
  exact P.asIdeal.mul_mem_left _ hm

end Formalism.HC.HostAx

end
end

