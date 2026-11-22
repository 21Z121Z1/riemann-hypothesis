import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace HyperplaneQuotientBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}

omit [∀ k, Fintype (ι k)] in

theorem mul_mem {b b' : K → ℤ} {s t : Ω} (hs : s ∈ chartLatQ y b 1) (ht : t ∈ chartLatQ y b' 1) :
    s * t ∈ chartLatQ y (b + b') 1 := by
  intro c hc
  have h := Subalgebra.mul_mem _ (hs c hc) (ht c hc)
  have heq : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + b') k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact h

omit [∀ k, Fintype (ι k)] in

theorem pow_mem {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1) (n : ℕ) :
    σ ^ n ∈ chartLatQ y ((n : ℤ) • e) 1 := by
  induction n with
  | zero =>
    intro c _
    simp
  | succ n ih =>
    have h := mul_mem ih hσ
    have hb : (n : ℤ) • e + e = ((n + 1 : ℕ) : ℤ) • e := by
      push_cast
      rw [add_smul, one_smul]
    rw [hb] at h
    rw [pow_succ]
    exact h

omit [∀ k, Fintype (ι k)] in

theorem pow_regular {c : ∀ k, ι k} {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1)
    (hreg : ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
      σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + e - 1) 1 → s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    (n : ℕ) (b : K → ℤ) (s : Ω) (hs : s ∈ chartLatQ y b 1)
    (h : σ ^ n * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (n : ℤ) • e - 1) 1) :
    s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  induction n generalizing b s with
  | zero => simpa using h
  | succ n ih =>
    have hσs : σ * s ∈ chartLatQ y (b + e) 1 := by
      have h' := mul_mem hσ hs
      rwa [add_comm e b] at h'
    refine hreg b s hs (ih (b + e) (σ * s) hσs ?_)
    have hb : b + ((n + 1 : ℕ) : ℤ) • e - 1 = b + e + (n : ℤ) • e - 1 := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [hb, pow_succ, mul_assoc] at h
    exact h

theorem finiteDimensional (hF : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (b : K → ℤ) :
    FiniteDimensional ℚ (chartLatQ y b 1) := by
  classical
  obtain ⟨G, hG⟩ := hF K ι Ω y b 1 hy
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (G : Set Ω)) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  have hmem : (N : Ω) * s ∈ Submodule.span ℚ (G : Set Ω) := by
    rw [← hG] at hNs
    exact (AddSubgroup.closure_le (Submodule.span ℚ (G : Set Ω)).toAddSubgroup).mpr Submodule.subset_span hNs
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hmem

theorem mem_chartDivSec {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (s : chartLatQ y b 1) :
    s ∈ chartDivSec y c b ↔ (s : Ω) / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  simp only [chartDivSec, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map,
    LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [← hts, mul_div_cancel_left₀ _ hm0]
    exact ht
  · intro h
    exact ⟨_, h, mul_div_cancel₀ _ hm0⟩

theorem finrank_quot_add_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ)
    [FiniteDimensional ℚ (chartLatQ y b 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) + Module.finrank ℚ (chartLatQ y (b - 1) 1) ≤
      Module.finrank ℚ (chartLatQ y b 1) := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hmem : ∀ t ∈ chartLatQ y (b - 1) 1, (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 :=
    fun t ht => mul_mem_chartLatQ b ht
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, hmem t t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Submodule.finrank_quotient_add_finrank (chartDivSec y c b)
  omega

theorem finrank_quot_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {b d b' : K → ℤ} (hbd : b + d = b') {τ : Ω}
    (hτ : τ ∈ chartLatQ y d 1)
    (hreg : ∀ s ∈ chartLatQ y b 1, τ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b' - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    [FiniteDimensional ℚ (chartLatQ y b' 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) ≤
      Module.finrank ℚ (chartLatQ y b' 1 ⧸ chartDivSec y c b') := by
  subst hbd
  have hmem : ∀ s ∈ chartLatQ y b 1, τ * s ∈ chartLatQ y (b + d) 1 := fun s hs => by
    have h := mul_mem hτ hs
    rwa [add_comm d b] at h
  let φ : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y (b + d) 1 :=
    { toFun := fun s => ⟨τ * s, hmem s s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r τ (s : Ω)) }
  have hle : chartDivSec y c b ≤ (chartDivSec y c (b + d)).comap φ := by
    intro s hs
    rw [Submodule.mem_comap, mem_chartDivSec hc]
    rw [mem_chartDivSec hc] at hs
    have h := mul_mem hτ hs
    rw [show d + (b - 1) = b + d - 1 by abel] at h
    show τ * (s : Ω) / _ ∈ _
    rw [mul_div_assoc]
    exact h
  have hinj : Function.Injective (Submodule.mapQ _ _ φ hle) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H s =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc]
      exact hreg s s.2 hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

end HyperplaneQuotientBound

open HyperplaneQuotientBound in

theorem HyperplaneQuotientBound.proof (hR : HyperplaneRegularSection.Statement)
    (hS : DiagonalSectionDifference.Statement) (hF : SectionLatticeFinite.Statement) :
    HyperplaneQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a c hD hV _ hc
  obtain ⟨M, hM1, hMa⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, a k ≤ M := by
    refine ⟨(∑ k, (a k).toNat) + 1, Nat.le_add_left _ _, fun k => ?_⟩
    have h1 : (a k).toNat ≤ ∑ k, (a k).toNat :=
      Finset.single_le_sum (f := fun k => (a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (a k)
    have h3 : ((a k).toNat : ℤ) ≤ ((∑ k, (a k).toNat : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 ⊢
    omega
  set e : K → ℕ := fun k => ((M : ℤ) - a k).toNat with he
  have hek : ∀ k, (e k : ℤ) = M - a k := fun k => Int.toNat_of_nonneg (sub_nonneg.mpr (hMa k))
  obtain ⟨σ, -, hσ, hreg⟩ := hR K ι Ω y c e hc
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  obtain ⟨C, hC⟩ := hS K ι Ω y D hD hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  refine ⟨C * (M : ℝ) ^ (D - 1), eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have hbd : (n : ℤ) • a + (n : ℤ) • (fun k => (e k : ℤ)) = ((n * M : ℕ) : ℤ) • (1 : K → ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hek, Pi.one_apply]
    push_cast
    ring
  have := finiteDimensional hF hy (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h1 := finrank_quot_le hc hbd (pow_mem hσ n) (fun s hs h => pow_regular hσ hreg n _ s hs (by rwa [← hbd] at h))
  have h2 := finrank_quot_add_le hc (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h3 := hN (n * M) (le_trans hn (Nat.le_mul_of_pos_right n hM1))
  have h1' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) := by exact_mod_cast h1
  have h2' : (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) +
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1) : ℝ) := by exact_mod_cast h2
  have hpow : ((n * M : ℕ) : ℝ) ^ (D - 1) = (M : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by
    push_cast
    ring
  rw [hpow] at h3
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneRegularSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HyperplaneRegularSection

theorem exists_notMem_of_finite {V : Type*} [AddCommGroup V] [Module ℚ V] (S : Set (Submodule ℚ V))
    (hS : S.Finite) (htop : ∀ W ∈ S, W ≠ ⊤) : ∃ v : V, ∀ W ∈ S, v ∉ W := by
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := ℚ) (E := V) (s := hS.toFinset)
    (by rw [Set.Finite.mem_toFinset]; exact fun h => htop ⊤ h rfl)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨v, fun W hW hvW => hv ?_⟩
  exact Set.mem_biUnion ((Set.Finite.mem_toFinset hS).mpr hW) hvW

theorem mem_span_of_mul_mem {A : Type*} [CommRing A] [IsNoetherianRing A] (f w u : A)
    (hw : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {f}), w ∉ p) (h : w * u ∈ Ideal.span {f}) :
    u ∈ Ideal.span {f} := by
  by_contra hu
  have hx : (Ideal.Quotient.mk (Ideal.span {f}) u) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmem : w ∈ {r : A | ∃ x : A ⧸ Ideal.span {f}, x ≠ 0 ∧ r • x = 0} :=
    ⟨_, hx, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]; exact h⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hmem
  obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hmem
  exact hw p hp hwp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isNoetherianRing_chartRingQ (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) :
    IsNoetherianRing (chartRingQ y c') := by
  classical
  refine isNoetherianRing_of_fg ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

def gen (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (i : ι k) : chartRingQ y c' :=
  ⟨y ⟨k, i⟩ / y ⟨k, c' k⟩, Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩⟩

def eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) : chartRingQ y c' :=
  ∏ k, gen y c' k (c k)

def avoidSub (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (p : Ideal (chartRingQ y c')) :
    Submodule ℚ (ι k → ℚ) :=
  (p.restrictScalars ℚ).comap (Fintype.linearCombination ℚ (gen y c' k))

def twist (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))

omit [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem twist_add (y : (Σ k, ι k) → Ω) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) :
    twist y c' (a + a') = twist y c' a * twist y c' a' := by
  simp only [twist, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc' k)]
  congr 1
  simp only [Pi.add_apply]
  ring

omit [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem twist_zero (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) : twist y c' 0 = 1 := by
  simp [twist]

omit [∀ k, Fintype (ι k)] in

theorem coe_eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) :
    (eqn y c c' : Ω) = (∏ k, y ⟨k, c k⟩) * twist y c' 1 := by
  simp only [eqn, gen, twist, Pi.one_apply]
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end HyperplaneRegularSection

set_option synthInstance.maxHeartbeats 400000 in
open HyperplaneRegularSection in

theorem HyperplaneRegularSection.proof : HyperplaneRegularSection.Statement := by
  intro K _ ι _ Ω _ _ y c e hc
  classical
  have hnoeth : ∀ c' : ∀ k, ι k, IsNoetherianRing (chartRingQ y c') := isNoetherianRing_chartRingQ y

  have hlam : ∀ k, ∃ v : ι k → ℚ, ∑ i, v i • y ⟨k, i⟩ ≠ 0 ∧
      ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
        ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}),
          Fintype.linearCombination ℚ (gen y c' k) v ∉ p := by
    intro k
    let S : Set (Submodule ℚ (ι k → ℚ)) :=
      {LinearMap.ker (Fintype.linearCombination ℚ fun i => y ⟨k, i⟩)} ∪
        ⋃ c' : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0},
          avoidSub y c'.1 k '' associatedPrimes (chartRingQ y c'.1)
            (chartRingQ y c'.1 ⧸ Ideal.span {eqn y c c'.1})
    have hS : S.Finite := (Set.finite_singleton _).union
      (Set.finite_iUnion fun c' => (associatedPrimes.finite _ _).image _)
    have htop : ∀ W ∈ S, W ≠ ⊤ := by
      intro W hW hWtop
      rcases hW with hW | hW
      · rw [Set.mem_singleton_iff] at hW
        have h1 : Pi.single (c k) (1 : ℚ) ∈ W := hWtop ▸ Submodule.mem_top
        rw [hW, LinearMap.mem_ker, Fintype.linearCombination_apply_single, one_smul] at h1
        exact hc k h1
      · obtain ⟨c', p, hp, rfl⟩ := Set.mem_iUnion.mp hW
        have h1 : Pi.single (c'.1 k) (1 : ℚ) ∈ avoidSub y c'.1 k p := hWtop ▸ Submodule.mem_top
        rw [avoidSub, Submodule.mem_comap, Submodule.restrictScalars_mem,
          Fintype.linearCombination_apply_single, one_smul,
          show gen y c'.1 k (c'.1 k) = 1 from Subtype.ext (div_self (c'.2 k))] at h1
        exact (IsAssociatedPrime.isPrime hp).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨v, hv⟩ := exists_notMem_of_finite S hS htop
    refine ⟨v, fun h0 => hv _ (Or.inl rfl) ?_, fun c' hc' p hp hvp =>
      hv _ (Or.inr (Set.mem_iUnion.mpr ⟨⟨c', hc'⟩, p, hp, rfl⟩)) hvp⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact h0
  choose v hv0 hvp using hlam
  set m := ∏ k, y ⟨k, c k⟩ with hm_def
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  set l : K → Ω := fun k => ∑ i, v k i • y ⟨k, i⟩ with hl
  set σ : Ω := ∏ k, l k ^ e k with hσ

  have hφ : ∀ (c' : ∀ k, ι k) (k : K),
      ((Fintype.linearCombination ℚ (gen y c' k) (v k) : chartRingQ y c') : Ω) = l k / y ⟨k, c' k⟩ := by
    intro c' k
    simp [Fintype.linearCombination_apply, gen, hl, Finset.sum_div, smul_div_assoc]
  let w : ∀ c' : ∀ k, ι k, chartRingQ y c' := fun c' =>
    ∏ k, Fintype.linearCombination ℚ (gen y c' k) (v k) ^ e k
  have hw : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (w c' : Ω) = σ * twist y c' (fun k => (e k : ℤ)) := by
    intro c' hc'
    simp only [w, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, hφ, twist, hσ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, zpow_neg, Nat.cast_one, one_mul, zpow_natCast, div_eq_mul_inv]
  have hwp : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}), w c' ∉ p := by
    intro c' hc' p hp hwp
    have := IsAssociatedPrime.isPrime hp
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hwp
    exact hvp k c' hc' p hp (this.mem_of_pow_mem _ hk)
  refine ⟨σ, Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hv0 k), ?_, ?_⟩
  · intro c' hc'
    show σ * twist y c' (fun k => (e k : ℤ)) ∈ chartRingQ y c'
    rw [← hw c' hc']
    exact (w c').2
  · intro b s hs h c' hc'
    have hnc := hnoeth c'
    have hT : twist y c' 1 * twist y c' (-1) = 1 := by
      rw [← twist_add y hc', add_neg_cancel, twist_zero]
    have hM : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    let u : chartRingQ y c' := ⟨s * twist y c' b, hs c' hc'⟩
    let u' : chartRingQ y c' :=
      ⟨σ * s / m * twist y c' (b + (fun k => (e k : ℤ)) - 1), h c' hc'⟩
    have key : w c' * u = eqn y c c' * u' := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, u, u']
      rw [hw c' hc', coe_eqn, ← hm_def, sub_eq_add_neg, twist_add y hc', twist_add y hc']
      linear_combination (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ)))) * hM +
        (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ))) * (m * m⁻¹)) * hT
    have hu : u ∈ Ideal.span {eqn y c c'} :=
      mem_span_of_mul_mem _ _ _ (hwp c' hc') (by
        rw [key]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
    have ha' : (a : Ω) * (m * twist y c' 1) = s * twist y c' b := by
      rw [← coe_eqn]
      exact congrArg Subtype.val ha
    show s / m * twist y c' (b - 1) ∈ chartRingQ y c'
    have heq : s / m * twist y c' (b - 1) = a := by
      rw [sub_eq_add_neg, twist_add y hc', div_eq_mul_inv]
      linear_combination (-(m⁻¹ * twist y c' (-1))) * ha' + ((a : Ω) * (twist y c' 1 * twist y c' (-1))) * hM +
        (a : Ω) * hT
    rw [heq]
    exact a.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem LiftAtPrime.proof (hC : GeneratedPow.Statement) (hA : FibreSectionLift.Statement)
    (hB : FibreRelLift.Statement) : LiftAtPrime.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N p hY hp hN
  obtain ⟨q, hq, hgen, hvan⟩ := hN
  obtain ⟨t₀, ht₀⟩ := hvan 0
  refine ⟨q, t₀, hq, fun t ht => ?_⟩
  have hga : KH.GeneratedV (ZMod p) (fibreIdeal p y) ((t * q) • N) := by
    have h := hC (ZMod p) K ι (fibreIdeal p y) (q • N) t hgen
    rwa [smul_smul] at h
  have hH1 : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) ((t * q) • N) 1) := by
    have h := ht₀ t ht
    rwa [zero_add] at h
  have hfi : fibreIdeal p y = GenOnFibres.idealOver y (ZMod p) := rfl
  rw [hfi] at hga hH1
  choose r z u hz hu hrel using hga
  have hlift : ∀ I j, ∃ s ∈ chartLat y ((t * q) • N) 1,
      GenOnFibres.secCoch y (ZMod p) s ((t * q) • N) = z I j :=
    fun I j => hA K ι Ω y D p ((t * q) • N) hY hp hH1 (z I j) (hz I j)
  choose s hs hsz using hlift
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  have : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Σ I, Fin (r I))).symm
  refine ⟨Fintype.card (Σ I, Fin (r I)), fun j => s (e j).1 (e j).2, fun j => hs _ _, fun c hc => ?_⟩
  let J : KH.Cell K ι 0 := ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hJ : GenOnFibres.cellChart J = c :=
    funext fun k => Finset.mem_singleton.mp (GenOnFibres.cellChart_mem J k)
  have hrelJ : ∑ j, u J j * GenOnFibres.secCoch y (ZMod p) (s J j) ((t * q) • N) J = 1 := by
    rw [← hrel J]
    exact Finset.sum_congr rfl fun j _ => by rw [hsz J j]
  obtain ⟨u', v, hu', hv, hsum⟩ :=
    hB K ι Ω y p ((t * q) • N) (r J) (s J) J (u J) (hs J) (by rw [hJ]; exact hc) (hu J) hrelJ
  rw [hJ] at hu' hv hsum
  let U : (Σ I, Fin (r I)) → Ω := fun x => if h : x.1 = J then u' (Fin.cast (congrArg r h) x.2) else 0
  refine ⟨fun j => U (e j), v, fun j => ?_, hv, ?_⟩
  · simp only [U]
    split_ifs
    · exact hu' _
    · exact zero_mem _
  · rw [← hsum]
    congr 1
    rw [e.sum_comp (fun x => U x * (s x.1 x.2 * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))),
      Fintype.sum_sigma, Finset.sum_eq_single J]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [U]
    · intro I _ hI
      exact Finset.sum_eq_zero fun j _ => by simp [U, hI]
    · intro h
      exact absurd (Finset.mem_univ J) h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricTransportSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ChangeOfLattice

noncomputable section

namespace MetricTransportSmooth

theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  have h := matActC_smul_one (J := J) (1 : ℚ) z
  simpa using h

theorem matActC_zero {J : Type} [Fintype J] (A : Matrix J J ℚ) : matActC A 0 = 0 := by
  funext i
  simp [matActC]

theorem proof : MetricTransportSmooth.Statement := by
  intro κ _ B m m' hB hm hm'
  classical
  obtain ⟨B', hBB', hB'B⟩ := isInvMat_mul hB
  have hinv : ∀ w, matActC B (matActC B' w) = w := fun w => by
    rw [matActC_mul, hBB', matActC_one]
  have heq : ∀ w, m'.ρ w = m.ρ (matActC B' w) := fun w => by
    rw [← hm' (matActC B' w), hinv]
  have hmaps : Set.MapsTo (matActC B') {z : Ix κ → ℂ | z ≠ 0} {z | z ≠ 0} := fun w hw h0 => by
    apply hw
    rw [← hinv w, h0, matActC_zero]
  exact (hm.comp (contDiff_matActC B').contDiffOn hmaps).congr fun w _ => heq w

end MetricTransportSmooth

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

