import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0173
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0179
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0110
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0177
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0143
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReduction
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfAlg

theorem pow_mul_mem_span_iff {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (n m : ℕ) (x : R) :
    a ^ n * x ∈ Ideal.span {a ^ (n + m)} ↔ x ∈ Ideal.span {a ^ m} := by
  have hn : a ^ n ∈ nonZeroDivisors R := pow_mem ha n
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    have e : a ^ n * (c * a ^ m) = a ^ n * x := by rw [← hc, pow_add]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 hn (c * a ^ m - x) (by rw [mul_sub, e, sub_self]))
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
    exact Ideal.mem_span_singleton'.2 ⟨c, by rw [pow_add]; ring⟩

theorem lseq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  intro l _ A n m
  have hl : (l : A.Acr0) ∈ nonZeroDivisors A.Acr0 := A.acris_torsion_free l (Fact.out : l.Prime).ne_zero
  have mk0 : ∀ (k : ℕ) (y : A.Acr0), A.mkAcr k y = 0 ↔ y ∈ Ideal.span {(l : A.Acr0) ^ k} :=
    fun k y => Ideal.Quotient.eq_zero_iff_mem
  refine ⟨?_, ?_, ?_, fun x => pow_mul_mem_span_iff (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1 n m x⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨A.mkAcr _ y, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.red _ (A.mkAcr _ y) = 0 ↔ A.mkAcr _ y ∈ _
    rw [red_mk, mk0]
    constructor
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      refine Ideal.mem_span_singleton'.2 ⟨A.mkAcr _ c, ?_⟩
      rw [map_mul, map_pow, map_natCast]
    · intro h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective c
      have e : A.mkAcr (n + m) (d * (l : A.Acr0) ^ n - y) = 0 := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        exact sub_eq_zero.2 hc
      have e2 := (mk0 _ _).1 e
      have e3 : Ideal.span {(l : A.Acr0) ^ (n + m)} ≤ Ideal.span {(l : A.Acr0) ^ n} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right n m))
      have e4 := Ideal.sub_mem _ (Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ((l : A.Acr0) ^ n))) (e3 e2)
      rwa [sub_sub_cancel] at e4
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _ * A.mkAcr _ y = 0 ↔ A.red _ (A.mkAcr _ y) = 0
    rw [red_mk, mk0, ← pow_mul_mem_span_iff hl n m y, ← mk0, map_mul, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.PerfAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpMapCongruenceProperties
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_sub_mem_span_l_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : A.A) :
    A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi} := by
  have key : ∀ x y : A.U, (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) x =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) y) ↔ x - y ∈ Ideal.span {(l : A.U)} := by
    intro x y
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, pow_one]
  rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, sub_eq_zero,
    CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq]
  exact (key _ _).symm

theorem idem_pow {R : Type*} [CommRing R] {x : R} (h : IsIdempotentElem x) {k : ℕ} (hk : k ≠ 0) :
    x ^ k = x := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n =>
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ih (Nat.succ_ne_zero _), h.eq]

private theorem eq_zero_of_isIdempotentElem_of_mem_span_prime {l : ℕ} [Fact l.Prime] (A : PAlg l) {w : A.U}
    (hw : IsIdempotentElem w) (hl : w ∈ Ideal.span {(l : A.U)}) : w = 0 := by
  apply IsHausdorff.haus (GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U A).toIsHausdorff w
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ m =>
    have hp := Ideal.pow_mem_pow hl (m + 1)
    rwa [idem_pow hw (Nat.succ_ne_zero m)] at hp

theorem sharp_one_sub {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) :
    A.sharp (1 - e) = 1 - A.sharp e := by
  have h0 : A.sharp 0 = 0 := by
    apply eq_zero_of_isIdempotentElem_of_mem_span_prime A
    · show A.sharp 0 * A.sharp 0 = A.sharp 0
      rw [← map_mul, mul_zero]
    · rw [Ideal.mem_span_singleton]
      refine ⟨A.sharp 0, ?_⟩
      rw [← CrystallineSemistableComparison.PAlg.sharp_pi A, ← map_mul A.sharp, mul_zero]
  have hu : IsIdempotentElem (A.sharp e) := by
    show A.sharp e * A.sharp e = A.sharp e
    rw [← map_mul, he.eq]
  have hv : IsIdempotentElem (A.sharp (1 - e)) := by
    have h1e : (1 - e) * (1 - e) = 1 - e := by linear_combination he.eq
    show A.sharp (1 - e) * A.sharp (1 - e) = A.sharp (1 - e)
    rw [← map_mul, h1e]
  have huv : A.sharp e * A.sharp (1 - e) = 0 := by
    rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, h0]
  have hw : IsIdempotentElem (1 - A.sharp e - A.sharp (1 - e)) := by
    show (1 - A.sharp e - A.sharp (1 - e)) * (1 - A.sharp e - A.sharp (1 - e)) =
      1 - A.sharp e - A.sharp (1 - e)
    linear_combination hu.eq + hv.eq + 2 * huv
  have hl : 1 - A.sharp e - A.sharp (1 - e) ∈ Ideal.span {(l : A.U)} := by
    have h1 : A.aToU1 1 - A.aToU1 e - A.aToU1 (1 - e) = 0 := by
      rw [← map_sub, sub_self]
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, map_one] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (1 - A.sharp e - A.sharp (1 - e)) = 0 := by
      rw [map_sub, map_sub]
      exact h1
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at h2
    exact h2
  have hw0 := eq_zero_of_isIdempotentElem_of_mem_span_prime A hw hl
  linear_combination -hw0

theorem sharp_congruences : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} →
      A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧
    (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧
    ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := by
  intro l _ A
  refine ⟨?_, fun a b => sharp_sub_mem_span_l_iff A a b, fun e he => sharp_one_sub A e he⟩
  intro a b n hab
  have h1 : A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} := (sharp_sub_mem_span_l_iff A a b).mpr hab
  rw [Ideal.mem_span_singleton] at h1 ⊢
  rw [map_pow, map_pow]
  exact dvd_sub_pow_of_dvd_sub h1 n

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarefreeDimensionFormula
section
open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

theorem prod_Icc_one_eq (f : ℕ → ℤ) (d : ℕ) (h : 1 ≤ d) :
    ∏ i ∈ Finset.Icc 1 d, f i = (∏ i ∈ Finset.Ico 1 d, f i) * f d := by
  have e : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e, Finset.prod_Ico_succ_top h]

theorem sqfreeDimAll : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  intro K _ _ _ n s b lam hb hd
  have hq1 : (1 : ℤ) < (Fintype.card K : ℤ) := by
    have := Fintype.one_lt_card (α := K)
    exact_mod_cast this
  have hne : ∀ i : ℕ, 1 ≤ i → (Fintype.card K : ℤ) ^ i - 1 ≠ 0 := by
    intro i hi h
    have : (1 : ℤ) < (Fintype.card K : ℤ) ^ i := one_lt_pow₀ hq1 (by omega)
    linarith
  have hdim := GlobalTheory.T.harish_chandra_dimension K (Fin n) s b lam
  obtain ⟨hGL, hP⟩ := GlobalTheory.T.card_parabolic_subgroup K (Fin n)
  obtain ⟨hPc, hch⟩ := hP s b
  rw [Fintype.card_fin] at hGL hch
  have hblk : ∀ c, (Nat.card (GL {i // b i = c} K) : ℤ) =
      (Fintype.card K : ℤ) ^ (Fintype.card {i // b i = c}).choose 2 *
        ((∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
          ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1)) := by
    intro c
    have hpos : 1 ≤ Fintype.card {i // b i = c} := by
      obtain ⟨i, hi⟩ := hb c
      exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
    rw [(GlobalTheory.T.card_parabolic_subgroup K {i // b i = c}).1,
      prod_Icc_one_eq (fun i => (Fintype.card K : ℤ) ^ i - 1) _ hpos]
  have hZ : (Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) : ℤ) *
      (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Nat.card (GL (Fin n) K) : ℤ) * ∏ c, (Module.finrank ℂ (lam c) : ℤ) := by
    exact_mod_cast hdim
  have hPz : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
        ((Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
          ((∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
            ∏ c, ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1))) := by
    rw [hPc]
    push_cast
    rw [Finset.prod_congr rfl (fun c _ => hblk c), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hPz, hGL, hch, Finset.prod_congr rfl (fun c _ => hd c), pow_add] at hZ
  have hA : (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}),
      ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c _ => Finset.prod_ne_zero_iff.2 fun i hi =>
      hne i (Finset.mem_Ico.1 hi).1
  have hq0 : (Fintype.card K : ℤ) ≠ 0 := by linarith
  have hc : (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
      (Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
      (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)) hA
  apply mul_left_cancel₀ hc
  linear_combination hZ

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableFamilyPropertiesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_family_properties : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  first | exact @GlobalTheory.CompanionTheory.StFam.st_all | exact GlobalTheory.CompanionTheory.StFam.st_all | (intros; apply GlobalTheory.CompanionTheory.StFam.st_all <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w' w₁ w₂ w₃ w₄ w₅ t₁ t₂ t₃ t₄ t₅

section Alg

theorem five_add {A₁ : Type w₁} {A₂ : Type w₂} {A₃ : Type w₃} {A₄ : Type w₄} {A₅ : Type w₅}
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : A₁ →+ A₂) (u₂ : A₂ →+ A₃) (u₃ : A₃ →+ A₄) (u₄ : A₄ →+ A₅)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (g₁ : A₁ →+ L₁) (g₂ : A₂ →+ L₂) (g₃ : A₃ →+ L₃) (g₄ : A₄ →+ L₄) (g₅ : A₅ →+ L₅)
    (c₁ : ∀ x, g₂ (u₁ x) = v₁ (g₁ x)) (c₂ : ∀ x, g₃ (u₂ x) = v₂ (g₂ x))
    (c₃ : ∀ x, g₄ (u₃ x) = v₃ (g₃ x)) (c₄ : ∀ x, g₅ (u₄ x) = v₄ (g₄ x))
    (eA₂ : Function.Exact u₁ u₂) (eA₃ : Function.Exact u₂ u₃) (eA₄ : Function.Exact u₃ u₄)
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (s₁ : Function.Surjective g₁) (b₂ : Function.Bijective g₂) (b₄ : Function.Bijective g₄)
    (i₅ : Function.Injective g₅) : Function.Bijective g₃ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : u₃ x = 0 := b₄.1 (by rw [c₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (eA₃ x).1 h1
    have h2 : v₂ (g₂ y) = 0 := by rw [← c₂, hx]
    obtain ⟨z, hz⟩ := (eL₂ _).1 h2
    obtain ⟨t, rfl⟩ := s₁ z
    have h3 : u₁ t = y := b₂.1 (by rw [c₁, hz])
    exact (eA₂ _).2 ⟨t, h3⟩
  · intro t
    obtain ⟨p, hp⟩ := b₄.2 (v₃ t)
    have h1 : u₄ p = 0 := i₅ (by
      rw [c₄, hp, map_zero]
      exact (eL₄ _).2 ⟨t, rfl⟩)
    obtain ⟨q, rfl⟩ := (eA₄ p).1 h1
    have h2 : v₃ (t - g₃ q) = 0 := by rw [map_sub, ← c₃, hp, sub_self]
    obtain ⟨y', hy'⟩ := (eL₃ _).1 h2
    obtain ⟨y, rfl⟩ := b₂.2 y'
    refine ⟨q + u₂ y, ?_⟩
    rw [map_add, c₂, hy']
    abel

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_ext {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type w'} [AddCommGroup P]
    (g h : (∀ i, N i ⊗[R] M i) →+ P) (H : ∀ i n x, g (Pi.single i (n ⊗ₜ x)) = h (Pi.single i (n ⊗ₜ x))) : g = h := by
  refine AddMonoidHom.functions_ext _ g h fun i t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x => exact H i n x
  | add x y hx hy => rw [Pi.single_add, map_add, map_add, hx, hy]

def piT {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) :
    (∀ i, N i ⊗[R] M i) →+ (∀ i, N i ⊗[R] M' i) where
  toFun t i := (u i).lTensor (N i) (t i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem piT_single {M : ι → Type w} {M' : ι → Type w'} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (u : ∀ i, M i →ₗ[R] M' i) (i : ι) (n : N i) (x : M i) :
    piT (N := N) u (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ u i x) := by
  funext k
  by_cases h : k = i
  · subst h
    simp [piT]
  · simp [piT, Pi.single_eq_of_ne h]

theorem piT_exact [∀ i, Module.Flat R (N i)] {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] (u : ∀ i, M₁ i →ₗ[R] M₂ i) (v : ∀ i, M₂ i →ₗ[R] M₃ i)
    (h : ∀ i, Function.Exact (u i) (v i)) : Function.Exact (piT (N := N) u) (piT (N := N) v) := by
  intro t
  constructor
  · intro ht
    have h1 : ∀ i, ∃ s, (u i).lTensor (N i) s = t i := fun i =>
      (Module.Flat.lTensor_exact (N i) (h i) (t i)).1 (congrFun ht i)
    choose s hs using h1
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext i
    exact (Module.Flat.lTensor_exact (N i) (h i) _).2 ⟨s i, rfl⟩

theorem tens_zero {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {M' : Type w'} [AddCommGroup M']
    (hM : ∀ i, Subsingleton (M i)) (hM' : Subsingleton M') (f : ∀ i, N i → M i → M') :
    Tens R (N := N) (M := M) (M' := M') f := by
  have h0 : ∀ i, Subsingleton (N i ⊗[R] M i) := fun i => by
    refine ⟨fun x y => ?_⟩
    have : ∀ z : N i ⊗[R] M i, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [this x, this y]
  refine ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩, fun _ _ => by simp⟩,
    fun i n x => Subsingleton.elim _ _⟩

theorem tens_transfer {M : ι → Type w₁} {L : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)] {M' : Type t₁} {L' : Type t₂} [AddCommGroup M'] [AddCommGroup L']
    (u : ∀ i, M i ≃ₗ[R] L i) (u' : M' ≃+ L') (f : ∀ i, N i → M i → M') (h : ∀ i, N i → L i → L')
    (hc : ∀ i n x, h i n (u i x) = u' (f i n x))
    (hf : Tens R (N := N) (M := M) (M' := M') f) : Tens R (N := N) (M := L) (M' := L') h := by
  obtain ⟨g, hg⟩ := hf
  let e : (∀ i, N i ⊗[R] L i) ≃+ (∀ i, N i ⊗[R] M i) :=
    { toFun := piT (N := N) fun i => ((u i).symm : L i →ₗ[R] M i)
      invFun := piT (N := N) fun i => ((u i) : M i →ₗ[R] L i)
      left_inv := fun t => by
        funext i
        change (((u i) : M i →ₗ[R] L i).lTensor (N i)) ((((u i).symm : L i →ₗ[R] M i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      right_inv := fun t => by
        funext i
        change (((u i).symm : L i →ₗ[R] M i).lTensor (N i)) ((((u i) : M i →ₗ[R] L i).lTensor (N i)) (t i)) = t i
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        simp
      map_add' := map_add _ }
  refine ⟨(e.trans g).trans u', fun i n x => ?_⟩
  obtain ⟨y, rfl⟩ := (u i).surjective x
  have : e (Pi.single i (n ⊗ₜ u i y)) = Pi.single i (n ⊗ₜ y) := by
    change piT (N := N) (fun i => ((u i).symm : L i →ₗ[R] M i)) _ = _
    rw [piT_single]
    simp
  simp only [AddEquiv.trans_apply, this, hg, hc]

theorem tens_five [∀ i, Module.Flat R (N i)]
    {M₁ : ι → Type w₁} {M₂ : ι → Type w₂} {M₃ : ι → Type w₃} {M₄ : ι → Type w₄} {M₅ : ι → Type w₅}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] [∀ i, AddCommGroup (M₄ i)] [∀ i, Module R (M₄ i)]
    [∀ i, AddCommGroup (M₅ i)] [∀ i, Module R (M₅ i)]
    {L₁ : Type t₁} {L₂ : Type t₂} {L₃ : Type t₃} {L₄ : Type t₄} {L₅ : Type t₅}
    [AddCommGroup L₁] [AddCommGroup L₂] [AddCommGroup L₃] [AddCommGroup L₄] [AddCommGroup L₅]
    (u₁ : ∀ i, M₁ i →ₗ[R] M₂ i) (u₂ : ∀ i, M₂ i →ₗ[R] M₃ i) (u₃ : ∀ i, M₃ i →ₗ[R] M₄ i) (u₄ : ∀ i, M₄ i →ₗ[R] M₅ i)
    (v₁ : L₁ →+ L₂) (v₂ : L₂ →+ L₃) (v₃ : L₃ →+ L₄) (v₄ : L₄ →+ L₅)
    (f₁ : ∀ i, N i → M₁ i → L₁) (f₂ : ∀ i, N i → M₂ i → L₂) (f₃ : ∀ i, N i → M₃ i → L₃)
    (f₄ : ∀ i, N i → M₄ i → L₄) (f₅ : ∀ i, N i → M₅ i → L₅)
    (c₁ : ∀ i n x, f₂ i n (u₁ i x) = v₁ (f₁ i n x)) (c₂ : ∀ i n x, f₃ i n (u₂ i x) = v₂ (f₂ i n x))
    (c₃ : ∀ i n x, f₄ i n (u₃ i x) = v₃ (f₃ i n x)) (c₄ : ∀ i n x, f₅ i n (u₄ i x) = v₄ (f₄ i n x))
    (eM₂ : ∀ i, Function.Exact (u₁ i) (u₂ i)) (eM₃ : ∀ i, Function.Exact (u₂ i) (u₃ i))
    (eM₄ : ∀ i, Function.Exact (u₃ i) (u₄ i))
    (eL₂ : Function.Exact v₁ v₂) (eL₃ : Function.Exact v₂ v₃) (eL₄ : Function.Exact v₃ v₄)
    (h₁ : Tens R (N := N) (M := M₁) (M' := L₁) f₁) (h₂ : Tens R (N := N) (M := M₂) (M' := L₂) f₂)
    (h₄ : Tens R (N := N) (M := M₄) (M' := L₄) f₄) (h₅ : Tens R (N := N) (M := M₅) (M' := L₅) f₅)
    (hadd : ∀ i, ∃ F : N i ⊗[R] M₃ i →+ L₃, ∀ n x, F (n ⊗ₜ x) = f₃ i n x) :
    Tens R (N := N) (M := M₃) (M' := L₃) f₃ := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  obtain ⟨g₄, hg₄⟩ := h₄
  obtain ⟨g₅, hg₅⟩ := h₅
  choose F hF using hadd
  let g₃ : (∀ i, N i ⊗[R] M₃ i) →+ L₃ := ∑ i, (F i).comp (Pi.evalAddMonoidHom _ i)
  have hg₃ : ∀ i n x, g₃ (Pi.single i (n ⊗ₜ x)) = f₃ i n x := by
    intro i n x
    simp only [g₃, AddMonoidHom.finset_sum_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    rw [Finset.sum_eq_single i]
    · simp [hF]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  have b := five_add (piT (N := N) u₁) (piT (N := N) u₂) (piT (N := N) u₃) (piT (N := N) u₄) v₁ v₂ v₃ v₄
    g₁.toAddMonoidHom g₂.toAddMonoidHom g₃ g₄.toAddMonoidHom g₅.toAddMonoidHom
    (fun x => DFunLike.congr_fun (tens_ext (g₂.toAddMonoidHom.comp (piT (N := N) u₁)) (v₁.comp g₁.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₁, hg₂, c₁]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₃.comp (piT (N := N) u₂)) (v₂.comp g₂.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₂, hg₃, c₂]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₄.toAddMonoidHom.comp (piT (N := N) u₃)) (v₃.comp g₃)
      fun i n x => by simp [piT_single, hg₃, hg₄, c₃]) x)
    (fun x => DFunLike.congr_fun (tens_ext (g₅.toAddMonoidHom.comp (piT (N := N) u₄)) (v₄.comp g₄.toAddMonoidHom)
      fun i n x => by simp [piT_single, hg₄, hg₅, c₄]) x)
    (piT_exact u₁ u₂ eM₂) (piT_exact u₂ u₃ eM₃) (piT_exact u₃ u₄ eM₄) eL₂ eL₃ eL₄
    g₁.surjective g₂.bijective g₄.bijective g₅.injective
  exact ⟨AddEquiv.ofBijective g₃ b, hg₃⟩

end Alg

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TiltSequenceDeterminedBySharpStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_sequence_determined_by_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A), (∀ i, a (i + 1) ^ l = a i) → (∀ i, b (i + 1) ^ l = b i) → (∀ i, A.sharp (a i) = A.sharp (b i)) → a = b := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.tilt_inj | exact GlobalTheory.CompanionTheory.Untilt.tilt_inj | (intros; apply GlobalTheory.CompanionTheory.Untilt.tilt_inj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicCompleteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untilt_adic_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | exact GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | (intros; apply GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U <;> assumption)
end

