import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChange
section
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr

open Filter Topology in

theorem _root_.GlobalTheory.VolBr.encard_ball_pow_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ),
    1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite →
    (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  intro G _ Λ B hB R Q e hR hQ hfin
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hR)
  have hQ2 : (2 : ℝ) ≤ Q := by linarith
  have hB1 : (B 1).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.1 ⟨0, hB.zero_mem 1 zero_le_one⟩
  by_cases hbig : (B (R * Q ^ e)).Finite
  swap
  · rw [Set.Infinite.encard_eq hbig, ENat.mul_top (pow_ne_zero _ hB1)]
    exact le_top
  set s : ℕ → ℝ := fun j ↦ ∑ i ∈ Finset.range j, (Q : ℝ) ^ i with hs
  have hs_succ : ∀ j, s (j + 1) = Q * s j + 1 := by
    intro j
    simp only [hs, Finset.sum_range_succ', pow_succ, pow_zero, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ Finset.sum_nonneg fun i _ ↦ by positivity
  have hs_le : ∀ j, s j + 1 ≤ (Q : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp [hs]
    | succ j ih =>
      rw [hs_succ, pow_succ]
      nlinarith [hs_nonneg j]
  have hclaim : ∀ j ≤ e, (B R).encard ^ j ≤ (B 1).encard ^ j * (B (R * s j)).encard := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hs, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem 0 le_rfl⟩
    | succ j ih =>
      intro hj
      have hRs : R * s j ≤ R * Q ^ e := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc s j ≤ (Q : ℝ) ^ j := by linarith [hs_le j]
          _ ≤ (Q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      have hfs : (B (R * s j)).Finite := hbig.subset (isBallFam_mono hB hRs)
      have hQpos : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
      have step := encard_mul_encard_le_isBallFam hB (a := R * s j) (b := R) hQpos (by linarith)
        hfs hfin h1
      have hrad : (Q : ℝ) * (R * s j) + R = R * s (j + 1) := by rw [hs_succ]; ring
      rw [hrad] at step
      calc (B R).encard ^ (j + 1) = (B R).encard ^ j * (B R).encard := pow_succ _ _
        _ ≤ (B 1).encard ^ j * (B (R * s j)).encard * (B R).encard := by
            gcongr; exact ih (by omega)
        _ = (B 1).encard ^ j * ((B (R * s j)).encard * (B R).encard) := mul_assoc _ _ _
        _ ≤ (B 1).encard ^ j * ((B 1).encard * (B (R * s (j + 1))).encard) := by gcongr
        _ = (B 1).encard ^ (j + 1) * (B (R * s (j + 1))).encard := by rw [pow_succ, mul_assoc]
  calc (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * s e)).encard := hclaim e le_rfl
    _ ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
        gcongr
        exact isBallFam_mono hB (mul_le_mul_of_nonneg_left (by linarith [hs_le e]) (by linarith))

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjOfIntegralConjGenerator
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ConjInt

section Coords

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isIntB_sum {ι : Type} (s : Finset ι) (f : ι → v.adicCompletion ℚ ⊗[ℚ] M)
    (h : ∀ i ∈ s, IsIntB v b (f i)) : IsIntB v b (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isIntB_zero v b
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntB_add v b (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isIntB_tmul_iff (c : M) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) ↔
    ∀ i, algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ := by
  unfold IsIntB
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem eventually_isIntB_tmul [Finite κ] (c : M) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := by
  have h : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (b.repr c i)).2
  exact h.mono fun v hv => (isIntB_tmul_iff v b c).2 hv

theorem eq_sum_basis [Fintype κ] (x : v.adicCompletion ℚ ⊗[ℚ] M) :
    x = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr x i •
      ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr x]
  simp only [Algebra.TensorProduct.basis_apply]

end Coords

section Alg

variable (v : HeightOneSpectrum ℤ) {A : Type} [Ring A] [Algebra ℚ A] {κ : Type} (b : Module.Basis κ ℚ A)

theorem isIntB_mul [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    {x y : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (hy : IsIntB v b y) : IsIntB v b (x * y) := by
  haveI := Fintype.ofFinite κ
  rw [eq_sum_basis v b x, eq_sum_basis v b y, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine isIntB_sum v b _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact isIntB_smul v b (mul_mem (hx i) (hy j)) (hb i j)

theorem isIntB_pow [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    (h1 : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : A)))
    {x : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (k : ℕ) : IsIntB v b (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact h1
  | succ k ih => rw [pow_succ]; exact isIntB_mul v b hb ih hx

theorem tmul_central_comm {R : Type} [CommRing R] [Algebra ℚ R] (z : A) (hz : ∀ c, z * c = c * z)
    (y : R ⊗[ℚ] A) : ((1 : R) ⊗ₜ[ℚ] z) * y = y * ((1 : R) ⊗ₜ[ℚ] z) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul, hz c]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end Alg

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem mem_adjoin_of_centralizer (G : HTGroup p) (γ : G.C) (hdeg : (minpoly G.F γ).natDegree = G.n)
    (L : Type) [Field L] (ι : L →+* G.C) (hι : Function.Injective ι)
    (hc : ∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) (w : L) :
    ι w ∈ Algebra.adjoin G.F ({γ} : Set G.C) := by
  set B := Algebra.adjoin G.F ({γ} : Set G.C) with hB
  have hBc : B ≤ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
    refine Algebra.adjoin_le ?_
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff] at hg; rw [hg]
  have hof : ∀ x : B, ∃ w, ι w = (x : G.C) := by
    intro x
    have hx := hBc x.2
    rw [Subalgebra.mem_centralizer_iff] at hx
    exact (hc x).1 (hx γ (Set.mem_singleton γ)).symm
  haveI : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨wx, hwx⟩ := hof x
    obtain ⟨wy, hwy⟩ := hof y
    have h0 : ι (wx * wy) = 0 := by
      rw [map_mul, hwx, hwy]; exact congrArg Subtype.val hxy
    rcases mul_eq_zero.1 (hι (h0.trans (map_zero ι).symm)) with h | h
    · left; apply Subtype.ext; rw [← hwx, h, map_zero]; rfl
    · right; apply Subtype.ext; rw [← hwy, h, map_zero]; rfl
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  have hγB : γ ∈ B := Algebra.self_mem_adjoin_singleton G.F γ
  have hint : IsIntegral G.F (⟨γ, hγB⟩ : B) := Algebra.IsIntegral.isIntegral _
  have hirr : Irreducible (minpoly G.F γ) := by
    have e := minpoly.algHom_eq B.val Subtype.val_injective ⟨γ, hγB⟩
    rw [show B.val ⟨γ, hγB⟩ = γ from rfl] at e
    rw [e]; exact minpoly.irreducible hint
  have hcom : Commute (ι w) γ := (hc (ι w)).2 ⟨w, rfl⟩
  exact (GlobalTheory.CentIrr.commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC γ hirr hdeg (ι w)).1 hcom

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem conj_tmul_smul_pow (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (X : (R ⊗[ℚ] G.C)ˣ)
    (c : G.F) (γ : G.C) (k : ℕ) :
    (X : R ⊗[ℚ] G.C) * ((1 : R) ⊗ₜ[ℚ] (c • γ ^ k)) * ↑X⁻¹ =
      ((1 : R) ⊗ₜ[ℚ] algebraMap G.F G.C c) * (↑X * ((1 : R) ⊗ₜ[ℚ] γ) * ↑X⁻¹) ^ k := by
  have hz : ∀ y : G.C, algebraMap G.F G.C c * y = y * algebraMap G.F G.C c := fun y => Algebra.commutes c y
  rw [Units.conj_pow, Algebra.smul_def, ← one_mul (1 : R), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.tmul_pow, one_pow, ← mul_assoc, ← mul_assoc,
    ← tmul_central_comm _ hz (X : R ⊗[ℚ] G.C)]
  simp only [mul_assoc]

theorem isIntB_conj_map_of_isIntB_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  intro p _ G γ hdeg L _ _ ι hι hc κ b κ' ℓ
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI : Finite κ' := Module.Finite.finite_basis ℓ
  haveI := Fintype.ofFinite κ'
  have hq : ∀ a, ∃ q : Polynomial G.F, Polynomial.aeval (γ : G.C) q = ι (ℓ a) := by
    intro a
    have h := mem_adjoin_of_centralizer G (γ : G.C) hdeg L ι.toRingHom hι hc (ℓ a)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  choose q hq using hq
  have hev : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      (∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j))) ∧
      IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : G.C)) ∧
      ∀ a, ∀ k ∈ Finset.range ((q a).natDegree + 1),
        IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] algebraMap G.F G.C ((q a).coeff k)) :=
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_isIntB_tmul b _).and
      ((eventually_isIntB_tmul b _).and
        (Filter.eventually_all.2 fun a => (Filter.eventually_all_finset _).2 fun k _ =>
          eventually_isIntB_tmul b _))
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv X hX ρ hρ => ?_⟩
  have hP := hv
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hP
  obtain ⟨hb, h1, hcoef⟩ := hP
  set ιv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have hmap : ∀ (r : v.adicCompletion ℚ) (m : L),
      ιv (r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] m)) = r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι m) := by
    intro r m
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']
    rfl
  have hterm : ∀ a, IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι (ℓ a)) * ↑X⁻¹) := by
    intro a
    rw [← hq a, Polynomial.aeval_eq_sum_range, TensorProduct.tmul_sum, Finset.mul_sum, Finset.sum_mul]
    refine isIntB_sum v b _ _ fun k hk => ?_
    rw [conj_tmul_smul_pow]
    exact isIntB_mul v b hb (hcoef a k hk) (isIntB_pow v b hb h1 hX k)
  rw [eq_sum_basis v ℓ ρ, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun a _ => ?_
  rw [hmap, mul_smul_comm, smul_mul_assoc]
  exact isIntB_smul v b (hρ a) (hterm a)

end GlobalTheory.ConjInt

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) :=
  GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensor
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain

theorem eventually_rat_mem_adicCompletionIntegers (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_isIntegral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧
      (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C with hb
  have hev : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k j l,
      algebraMap ℚ (w.1.adicCompletion ℚ) (b.repr (b k * b j) l) ∈ w.1.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro j
    rw [Filter.eventually_all]; intro l
    exact Subtype.val_injective.tendsto_cofinite.eventually (eventually_rat_mem_adicCompletionIntegers _)
  filter_upwards [hev] with w hw
  intro x hx
  set B := Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) b with hB
  have hent : ∀ i j, Algebra.leftMulMatrix B x i j ∈ w.1.adicCompletionIntegers ℚ := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← B.sum_repr x]
    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have e : B k * B j = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (b k * b j) := by
      simp [hB, Algebra.TensorProduct.basis_apply]
    rw [e, Algebra.TensorProduct.basis_repr_tmul]
    simp only [one_smul, Finsupp.mapRange_apply]
    exact mul_mem (hx k) (hw k j i)
  refine ⟨(Algebra.leftMulMatrix B x).charpoly, Matrix.charpoly_monic _, ?_, ?_⟩
  · intro n
    let M : Matrix (Fin (Module.finrank ℚ G.C)) (Fin (Module.finrank ℚ G.C)) (w.1.adicCompletionIntegers ℚ) :=
      fun i j => ⟨_, hent i j⟩
    have hM : Algebra.leftMulMatrix B x = M.map (algebraMap (w.1.adicCompletionIntegers ℚ) (w.1.adicCompletion ℚ)) := by
      ext i j; rfl
    rw [hM, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff n).2
  · apply Algebra.leftMulMatrix_injective B
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSubgroup

theorem exists_finite_subgroup_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : LB A.left) (H : Over (Sp K)) (_ : GrpObj H) (j : H ⟶ A), L.IsLB ∧ IsProjBy A.hom ∧ (∃ t : LB.Gen (Theta A L), t.IsGen) ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧ IsFinite H.hom ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro K _ _ A _ hA
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  obtain ⟨H₀, m, s, hH₀, hva, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple K A hA
  have hP : IsProjBy A.hom := ⟨H₀, hH₀, m, s, hva⟩
  obtain ⟨L, hL, hR⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy hP
  obtain ⟨H, j, hj, hf, hH⟩ := GlobalTheory.KernelRep.exists_finite_closed_kernel hG K A hA L hL hR
  haveI : Mono j.left := inferInstance
  haveI : Mono j := (Over.forget _).mono_of_mono_map this
  have hjK : GlobalTheory.MemKL A L j := (hH H j).2 ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (hH _ (1 : 𝟙_ (Over (Sp K)) ⟶ A)).1 (GlobalTheory.memKL_one hL _)
  have hm := (hH _ ((fst H H ≫ j) * (snd H H ≫ j))).1
    (GlobalTheory.UU.InK.mul hL (hjK.comp (fst H H)) (hjK.comp (snd H H)))
  have hn := (hH _ j⁻¹).1 (GlobalTheory.UU.InK.inv hL hjK)
  obtain ⟨g, hg⟩ := GlobalTheory.PointQuot.exists_grpObj_of_mono j h1.choose hm.choose hn.choose
    h1.choose_spec hm.choose_spec hn.choose_spec
  exact ⟨L, H, g, j, hL, hP, GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA L hL, hg, hj, hf, hH⟩

end GlobalTheory.KernelSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValueStatement
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ), ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  first | exact @GlobalTheory.PolRangeInf.exists_at_inf_values | exact GlobalTheory.PolRangeInf.exists_at_inf_values | (intros; apply GlobalTheory.PolRangeInf.exists_at_inf_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseFieldGeneratorLocalDifferentInertPlaceStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  first | exact @GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | exact GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | (intros; apply GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.UnitaryBC

namespace GlobalTheory.PolChar

theorem exists_compNorm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {χ : Formalism.L2.Host.HChar E} {u : ℝ},
    χ.IsAbsPow u → ∃ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E),
      GlobalTheory.GalOfCusp.compNorm E ψ = χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹ ∧
        ∀ v : InfinitePlace (maximalRealSubfield E), ψ.locInf v (-1) = 1 := by
  intro E _ _ _ χ u h
  refine ⟨resReal χ, Subtype.ext (MonoidHom.ext fun x => ?_), resReal_locInf_neg_one h⟩
  change χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
    χ.1 x * ((χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹)⁻¹
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, ideleConj_eq, inv_inv]

end GlobalTheory.PolChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunction
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem support_subset_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨S, hS⟩ := hf.2.2.2
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => q.1 * s * q.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => ?_
    exact (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory.FinClsLoc
end

