import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinJumpsSubsetOfSplitMono
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomialStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_gauss_norm_eventually_monomial : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  first | exact @GlobalTheory.MemLoc.gauss_slope | exact GlobalTheory.MemLoc.gauss_slope | (intros; apply GlobalTheory.MemLoc.gauss_slope <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicallyCompleteLatticeReductionActionStatement
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_subsingleton_H2 : ∀ (O G T M : Type) [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M] (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M), IsAdicComplete (Ideal.span {lam}) T → (∀ t : T, lam • t = 0 → t = 0) → Function.Surjective q → (∀ t, q t = 0 ↔ ∃ y, t = lam • y) → (∀ g t, q (π g t) = π' g (q t)) → (∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y) → Subsingleton (ReciprocityTheory.Def.H2 π' ⊤) → ∀ z ∈ ReciprocityTheory.Def.Z1 π' ⊤, ∃ c : G → T, (∀ g h, c (g * h) = c g + π g (c h)) ∧ (∀ g, q (c g) = z g) ∧ ∀ (a : ℕ) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, c g - c g₀ = lam ^ a • y := by
  first | exact @GlobalTheory.CocycleLift.exists_lift | exact GlobalTheory.CocycleLift.exists_lift | (intros; apply GlobalTheory.CocycleLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.WindowArith

theorem sg_ineq (l n : ℕ) [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    h i + sg l h i + 1 ≤ l * (sg l h (i - 1) + 1) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hshift : ∀ j : ℕ, (h (i - 1 + ((j + 1 + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1 + 1)
      = (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) / l := by
    intro j
    have e : i - 1 + ((j + 1 + 1 : ℕ) : ZMod n) = i + ((j + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    rw [e, pow_succ, div_div]
  have e0 : i - 1 + ((0 + 1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hrec : (l : ℝ) * (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
      = h i + ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
    rw [(summable_sg hl h (i - 1)).tsum_eq_zero_add, e0]
    simp only [hshift, tsum_div_const]
    field_simp
    ring
  have hS0 : 0 ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  have h1 := Nat.floor_le hS0
  have h2 := Nat.lt_floor_add_one
    (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
  have h3 := mul_lt_mul_of_pos_left h2 hl0
  have key : (h i : ℝ) + (⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ)
      < (l : ℝ) * ((⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ) + 1) := by
    linarith
  have key' : h i + ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊
      < l * (⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ + 1) := by
    exact_mod_cast key
  simp only [sg]
  omega

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ u - y := ((CharP.intCast_eq_intCast k l).mp h).symm.dvd
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith, h1⟩)
  linarith

private theorem cast_ne_of_mem_cloud_of_typeG {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hG : Dt.ty i = LType.G) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ y) (hy2 : y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) :
    (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu y hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hG]
  exact hm

private theorem natCast_ne_of_mem_cloud_of_bd_of_mem_range {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hB : Dt.ty i = LType.Bd) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ (Dt.h i : ℤ) - y)
    (hy2 : (Dt.h i : ℤ) - y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) : (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu ((Dt.h i : ℤ) - y) hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hB]
  exact Int.ModEq.sub (Int.ModEq.refl _) hm

theorem windows : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  intro k _ l n r _ _ _ Dt hT1 hT2 hT3 i
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hT1i := hT1 i
  have ht := Dt.one_le_letterBlockLength
  have hwB : Dt.w i ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩))
  have heB : Dt.w i + Dt.t - 1 ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩))
  have factsG : Dt.ty i = LType.G → (∀ u ∈ Dt.lows i, 1 ≤ u ∧ u ≤ (Dt.η i : ℤ)) ∧
      1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i := fun hG =>
    ⟨fun u hu => Dt.lowG i hG u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowG i hG _ hwB).1,
      (Dt.lowG i hG _ heB).2⟩
  have factsBd : Dt.ty i = LType.Bd → (∀ u ∈ Dt.lows i, (Dt.h i : ℤ) - Dt.η i ≤ u ∧ u ≤ (Dt.h i : ℤ) - 1) ∧
      (Dt.h i : ℤ) - Dt.η i ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ (Dt.h i : ℤ) - 1 := fun hB =>
    ⟨fun u hu => Dt.lowBd i hB u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowBd i hB _ hwB).1,
      (Dt.lowBd i hB _ heB).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsg := sg_ineq l n hl2 Dt.h i
    have e1 : Dt.sg l i = sg l Dt.h i := rfl
    have e2 : Dt.sg l (i - 1) = sg l Dt.h (i - 1) := rfl
    rw [e1, e2]
    zify at hsg
    linarith
  · intro u hu y hy1 hy2 he
    rcases Multiset.mem_add.1 hu with hu | hu
    · have huy : u = y := by
        cases hty : Dt.ty i
        · obtain ⟨hL, hw1, hw2⟩ := factsG hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
        · obtain ⟨hL, hw1, hw2⟩ := factsBd hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
      have key : ∃ β ∈ Dt.B i, |u - β| ≤ (Dt.sg l i : ℤ) + 2 := by
        by_cases hyw : y < Dt.w i
        · exact ⟨Dt.w i, mem_block.2 ⟨le_rfl, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        by_cases hye : Dt.w i + Dt.t - 1 < y
        · exact ⟨Dt.w i + Dt.t - 1, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        · exact ⟨y, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
      obtain ⟨β, hβ, hb⟩ := key
      have := hT2 i u hu β hβ
      linarith
    · cases hty : Dt.ty i
      · obtain ⟨-, hw1, hw2⟩ := factsG hty
        exact cast_ne_of_mem_cloud_of_typeG hT3 hty hu y (by omega) (by omega) he
      · obtain ⟨-, hw1, hw2⟩ := factsBd hty
        exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hty hu y (by omega) (by omega) he
  · intro hG
    obtain ⟨hL, hw1, hw2⟩ := factsG hG
    refine ⟨?_, ?_, hw1, hw2⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
  · intro hB
    obtain ⟨hL, hw1, hw2⟩ := factsBd hB
    have ew : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    refine ⟨?_, ?_, by rw [ew]; omega, by rw [ew]; omega⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he

end GlobalTheory.WindowArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatedTraceSystemLocallyCauchy
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem polyApprox_trc_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  intro l _ Γ _ _ _ _ a J x θ C hC hA ε hε g
  obtain ⟨s, c, hs, hP⟩ := hA (ε / 2) (by linarith)
  have hmem : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! R hRC hRη using hmem
  set F : Γ → PadicAlgCl l := fun h => ∑ η ∈ s, c η * trc (R η) h with hF
  have hFc : Continuous F := by
    refine continuous_finset_sum _ fun η hη => continuous_const.mul ?_
    have h1 : Continuous fun h => ((R η h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) :=
      Units.continuous_val.comp (hC _ (hRC η hη))
    exact (continuous_id.matrix_trace).comp h1
  refine ⟨F ⁻¹' Metric.ball (F g) (ε / 4), hFc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith)), ?_⟩
  intro i j hi hj
  have key := hP (MvPolynomial.X i - MvPolynomial.X j)
  simp only [map_sub, MvPolynomial.aeval_X] at key
  have hsum : ∑ η ∈ s, c η * (η i - η j) = F (x i) - F (x j) := by
    rw [hF]; simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η hη => ?_
    have hi2 : η i = trc (R η) (x i) := (congrFun (hRη η hη) i).symm
    have hj2 : η j = trc (R η) (x j) := (congrFun (hRη η hη) j).symm
    rw [hi2, hj2]; ring
  rw [hsum] at key
  have hi' : ‖F (x i) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hi
  have hj' : ‖F (x j) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hj
  have hd : ‖F (x i) - F (x j)‖ ≤ ε / 2 := by
    have e : F (x i) - F (x j) = (F (x i) - F g) - (F (x j) - F g) := by ring
    rw [e]; linarith [norm_sub_le (F (x i) - F g) (F (x j) - F g)]
  have e2 : θ i - θ j = (θ i - θ j - (F (x i) - F (x j))) + (F (x i) - F (x j)) := by ring
  rw [e2]; linarith [norm_add_le (θ i - θ j - (F (x i) - F (x j))) (F (x i) - F (x j))]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputation
section
open PowerSeries GlobalTheory.BK Matrix

noncomputable section

namespace GlobalTheory.IntegralityComp

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem S_eq_A_add_Fil {j : ℕ} (hj : j < l) {f : K⟦X⟧} (hf : f ∈ S O K e) :
    ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := GlobalTheory.T.breuilRing_eq_integral_add_eisensteinFiltration O K l e j hj f hf

theorem Fil_le_E_pow (j : ℕ) {φ : S O K e} (hφ : φ ∈ Fil O K l e j) :
    ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc O K l e j φ hφ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def colVec (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : Vec K a ι := Pi.single τ ((P.mx τ).col i)

theorem colVec_mem_MM (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : colVec P τ i ∈ P.MM := by
  refine mem_tot.2 fun σ => ?_
  by_cases h : σ = τ
  · subst h
    simp only [colVec, Pi.single_eq_same]
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp only [colVec, Pi.single_eq_of_ne h]
    exact zero_mem _

theorem sum_colVec (P : PhiMod O K l e a ι) (c : ZMod a → ι → K⟦X⟧) :
    (∑ τ, ∑ i, c τ i • colVec P τ i) = fun τ => P.mx τ *ᵥ c τ := by
  ext τ k
  simp only [Finset.sum_apply, Pi.smul_apply, colVec, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct, mul_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem MM_eq_L_add_FilMM (P : PhiMod O K l e a ι) {j : ℕ} (hj : j < l) {m : Vec K a ι}
    (hm : m ∈ P.MM) : ∃ p ∈ P.L, ∃ f ∈ P.FilMM j, m = p + f := by
  have hs (τ : ZMod a) (i : ι) : (P.mxInv τ *ᵥ m τ) i ∈ S O K e :=
    P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  choose g hg φ hφ hgφ using fun τ i => S_eq_A_add_Fil (O := O) (l := l) hj (hs τ i)
  have hm' (τ : ZMod a) : m τ = P.mx τ *ᵥ (P.mxInv τ *ᵥ m τ) := by
    rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]
  refine ⟨fun τ => P.mx τ *ᵥ g τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨g τ, fun i => hg τ i, rfl⟩,
    ∑ τ, ∑ i, φ τ i • colVec P τ i, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hφ τ i) (colVec_mem_MM P τ i)
  · have : (∑ τ, ∑ i, φ τ i • colVec P τ i) = ∑ τ, ∑ i, (φ τ i : K⟦X⟧) • colVec P τ i := rfl
    rw [this, sum_colVec]
    ext1 τ
    rw [Pi.add_apply, ← Matrix.mulVec_add, hm' τ]
    congr 1
    ext1 i
    exact hgφ τ i

section Dat

variable [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem Ezpow_smul_FilMM_mem (hηH : η < H) {f : Vec K a ι} (hf : f ∈ D.FilMM (10 * H)) :
    Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man := by
  refine Submodule.smul_induction_on hf (fun φ hφ m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨q, hq, hφq⟩ := Fil_le_E_pow (O := O) (10 * H) hφ
    have hEm := D.smul_mem_Mext (A_le_S l e) hm
    have key : Ezpow K l e (-(2 * H : ℤ)) • φ • m =
        (E K l e ^ (8 * H - η) * q) • (E K l e ^ η • m) := by
      have h1 : Ezpow K l e (-(2 * H : ℤ)) * E K l e ^ (10 * H) = E K l e ^ (8 * H - η) * E K l e ^ η := by
        rw [← pow_add, show 8 * H - η + η = 8 * H by omega, ← Ezpow_natCast, ← Ezpow_natCast,
          ← Ezpow_add]
        congr 1
        push_cast
        ring
      rw [show φ • m = (φ : K⟦X⟧) • m from rfl, hφq, smul_smul, smul_smul, ← mul_assoc, h1]
      congr 1
      ring
    rw [key]
    exact D.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) _) hq)
      (D.Mext_mono (S_le_R l e) hEm)
  · rw [smul_add]
    exact add_mem hx hy

theorem E_pow_smul_EN_mem (hηH : η < H) (hl : 10 * H + 2 ≤ l) {y : Vec K a ι} (hy : y ∈ D.EM η) :
    ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), E K l e ^ (2 * H) • D.EN y = p + f := by
  have hl0 : E K l e ^ (H + η) • y ∈ D.L := by
    rw [pow_add, mul_smul]
    exact D.lower _ hy
  have hMM : E K l e ^ (H + η) • y ∈ D.MM := D.ext_mono (A_le_S l e) hl0
  have hc : D.conn (E K l e ^ (H + η) • y) ∈ D.MM := D.conn_mem_MM hMM
  have hA : E K l e ^ (H - η) * E K l e ∈ S O K e := mul_mem (pow_mem (E_mem l e _) _) (E_mem l e _)
  obtain ⟨p, hp, f, hf, hpf⟩ := MM_eq_L_add_FilMM D.toPhiMod (j := 10 * H) (by omega)
    (D.MM.smul_mem ⟨_, hA⟩ hc)
  have hB : E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e)) ∈ A O K :=
    mul_mem (pow_mem (E_mem l e _) _) (mul_mem (natCast_mem _ _) (by
      rw [N_E]; exact mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _)))
  refine ⟨p - (E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e))) • (E K l e ^ (H + η) • y),
    sub_mem hp (D.L.smul_mem ⟨_, hB⟩ hl0), f, hf, ?_⟩
  have h1 : E K l e ^ (2 * H) • D.EN y = E K l e ^ (H - η) • (E K l e ^ (H + η) • D.EN y) := by
    rw [smul_smul, ← pow_add, show H - η + (H + η) = 2 * H by omega]
  rw [h1, PhiMod.E_pow_smul_EN, PhiMod.EN_apply, smul_sub, smul_smul, smul_smul]
  have h2 : (E K l e ^ (H - η) * E K l e) • D.conn (E K l e ^ (H + η) • y) = p + f := hpf
  rw [h2]
  abel

end Dat

end GlobalTheory.IntegralityComp

theorem GlobalTheory.IntegralityComp.integralityComputation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralityComputation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  exact ⟨fun m hm => GlobalTheory.IntegralityComp.MM_eq_L_add_FilMM D.toPhiMod (by omega) hm,
    fun f hf => GlobalTheory.IntegralityComp.Ezpow_smul_FilMM_mem D hηH hf,
    fun y hy => GlobalTheory.IntegralityComp.E_pow_smul_EN_mem D hηH hl hy⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinJumpsSubsetOfSplitMonoStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_jumps_subset_of_split_mono : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : GlobalTheory.BK.Hom D₀.toPhiMod D₁.toPhiMod) (n : ℕ), (∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) → D₀.jumps ⊆ D₁.jumps := by
  first | exact @GlobalTheory.BK.jumps_subset_of_split_mono | exact GlobalTheory.BK.jumps_subset_of_split_mono | (intros; apply GlobalTheory.BK.jumps_subset_of_split_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  first | exact @GlobalTheory.BK.xiExt_mem_Lk_iff | exact GlobalTheory.BK.xiExt_mem_Lk_iff | (intros; apply GlobalTheory.BK.xiExt_mem_Lk_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfPowerTraces
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CharpolyNewton

open Polynomial Finset

variable {k : Type} [Field k]

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → k) (j : ℕ) :
    (j : k) * (univ.val.map f).esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ k j)
  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset k) (j : ℕ) :
    (j : k) * s.esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) j
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq [CharZero k] (s t : Multiset k)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) : ∀ j, s.esymm j = t.esymm j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hj0 : (j : k) ≠ 0 := by exact_mod_cast hj.ne'
      apply mul_left_cancel₀ hj0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq [CharZero k] (s t : Multiset k) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext j
  by_cases hj : j ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hj, Multiset.prod_X_sub_C_coeff t (hc ▸ hj), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hj
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

theorem charpoly_eq_prod_of_trace_pow : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (B : Multiset k), Multiset.card B = a → (∀ n : ℕ, 1 ≤ n → (M ^ n).trace = (B.map (· ^ n)).sum) → M.charpoly = (B.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro k _ _ _ a M B hB h
  have hR : Multiset.card M.charpoly.roots = a := GlobalTheory.CharpolyPow.card_roots_charpoly M
  have hsplit : M.charpoly = (M.charpoly.roots.map fun b => X - C b).prod := by
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq M.charpoly_monic
      (by rw [hR, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
    exact this.symm
  rw [hsplit]
  refine prod_eq_of_psum_eq _ _ (by rw [hR, hB]) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hR, hB]
  · rw [← h n hn, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]

end GlobalTheory.CharpolyNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.TrFormNd

theorem eq_zero_of_trace_mul_eq_zero : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  intro k Γ _ _ _ a r hr M hM hg
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ a r hr
  refine hnd M ((GlobalTheory.SSCont.mem_imAlg_iff r M).2 hM) fun y hy => ?_
  have hy' := (GlobalTheory.SSCont.mem_imAlg_iff r y).1 hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact hg g
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]

end GlobalTheory.TrFormNd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmoduleStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  first | exact @GlobalTheory.CokerL.Tsub_conn | exact GlobalTheory.CokerL.Tsub_conn | (intros; apply GlobalTheory.CokerL.Tsub_conn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombinationStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧ ∀ x : Fl l, ‖sh x‖ < 1 → HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  first | exact @GlobalTheory.PSer.exists_coef_hasSum_lam | exact GlobalTheory.PSer.exists_coef_hasSum_lam | (intros; apply GlobalTheory.PSer.exists_coef_hasSum_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeriStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo] [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 := by
  first | exact @GlobalTheory.PowKill.main | exact GlobalTheory.PowKill.main | (intros; apply GlobalTheory.PowKill.main <;> assumption)
end

