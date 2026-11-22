import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveJetsUnramifiedHolds
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementB

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.JetsLin
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.C
open Formalism.L2.Th1.G
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace JL

theorem norm_sum_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {α : Type} (s : Finset α)
    (f : α → K) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem norm_mul_le_one {K : Type} [NormedField K] {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

section Lin

variable {K : Type} [Field K]

theorem linSub_linSub {n m p : Type} [Fintype n] [Fintype m] [Fintype p] (A : n → m → K)
    (B : m → p → K) (f : MvPowerSeries n K) :
    linSub B (linSub A f) = linSub (fun i x => ∑ j, A i j * B j x) f := by
  have e : ∀ i : n, linSub B (∑ j, MvPowerSeries.C (A i j) * MvPowerSeries.X j) =
      ∑ x, MvPowerSeries.C (∑ j, A i j * B j x) * MvPowerSeries.X x := by
    intro i
    rw [← linSubHom_apply, map_sum]
    simp only [map_mul, linSubHom_apply, linSub_C, linSub_X, map_sum, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
  unfold linSub at e ⊢
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_lin A) (hasSubst_lin B)]
  congr 1
  funext i
  exact e i

theorem hasSubst_block {n B : Type} [Finite n] (k : B) :
    MvPowerSeries.HasSubst (fun i : n => (MvPowerSeries.X (k, i) : MvPowerSeries (B × n) K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

def four {n ν : Type} (M : n → ν → K) : Fin 4 × n → Fin 4 × ν → K :=
  fun w x => if w.1 = x.1 then M w.2 x.2 else 0

theorem four_form {n ν : Type} [Fintype ν] (M : n → ν → K) (k : Fin 4) (i : n) :
    (∑ y, MvPowerSeries.C (four M (k, i) y) * MvPowerSeries.X y : MvPowerSeries (Fin 4 × ν) K) =
      ∑ x, MvPowerSeries.C (M i x) * MvPowerSeries.X (k, x) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp [four]
  · intro b _ hb
    simp [four, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem linSub_inBlock {n ν : Type} [Fintype n] [Fintype ν] (M : n → ν → K) (k : Fin 4)
    (T : MvPowerSeries n K) : linSub (four M) (inBlock k T) = inBlock k (linSub M T) := by
  unfold linSub inBlock
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_block k) (hasSubst_lin (four M)),
    MvPowerSeries.subst_comp_subst_apply (hasSubst_lin M) (hasSubst_block k)]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X (hasSubst_lin (four M)), four_form,
    ← MvPowerSeries.coe_substAlgHom (hasSubst_block k), map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X (hasSubst_block k)]

theorem linSub_tens4 {n ν : Type} [Fintype n] [Fintype ν] (M : n → ν → K)
    (T : MvPowerSeries n K) : linSub (four M) (tens4 T) = tens4 (linSub M T) := by
  unfold tens4
  rw [← linSubHom_apply, map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [linSubHom_apply, linSub_inBlock]

end Lin

theorem fourth_root_mem {K : Type} [NormedField K] [IsUltrametricDist K] (c : K)
    (h : c ^ 4 ∈ unitBall K) : c ∈ unitBall K := by
  change ‖c‖ ≤ 1
  have h' : ‖c ^ 4‖ ≤ 1 := h
  rw [norm_pow] at h'
  exact (pow_le_one_iff_of_nonneg (norm_nonneg c) (by norm_num)).1 h'

end JL

open JL

theorem FrameCompose_proof : FrameCompose := by
  intro K _ _ m n J X _ _ _ γ D V W th0 q0 A hD hq hA hγ hG
  refine ⟨fun w x => ∑ j, D w (x.1, j) * A j x.2,
    fun x y => ∑ j, ∑ k, A j x.2 * q0 (x.1, j) (y.1, k) * A k y.2, ?_, ?_, ?_, ?_⟩
  · intro w x
    exact norm_sum_le_one _ _ fun j _ => norm_mul_le_one (hD _ _) (hA _ _)
  · intro x y
    exact norm_sum_le_one _ _ fun j _ => norm_sum_le_one _ _ fun k _ =>
      norm_mul_le_one (norm_mul_le_one (hA _ _) (hq _ _)) (hA _ _)
  · intro a i b x
    have e : ∑ w, γ (a, i) w * ∑ j, D w (b, j) * A j x =
        ∑ j, (∑ w, γ (a, i) w * D w (b, j)) * A j x := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      rw [mul_assoc]
    change ∑ w, γ (a, i) w * ∑ j, D w (b, j) * A j x = _
    rw [e]
    simp only [hγ]
    split_ifs with h
    · rfl
    · simp
  · intro x y
    have e : ∑ w, (∑ j, D w (x.1, j) * A j x.2) * (∑ k, D w (y.1, k) * A k y.2) =
        ∑ j, ∑ k, A j x.2 * (∑ w, D w (x.1, j) * D w (y.1, k)) * A k y.2 := by
      have e1 : ∀ w, (∑ j, D w (x.1, j) * A j x.2) * (∑ k, D w (y.1, k) * A k y.2) =
          ∑ j, ∑ k, (D w (x.1, j) * A j x.2) * (D w (y.1, k) * A k y.2) := fun w =>
        Finset.sum_mul_sum _ _ _ _
      have e2 : ∀ j k, A j x.2 * (∑ w, D w (x.1, j) * D w (y.1, k)) * A k y.2 =
          ∑ w, (D w (x.1, j) * A j x.2) * (D w (y.1, k) * A k y.2) := fun j k => by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun w _ => by ring
      simp only [e1, e2]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    change ∑ w, (∑ j, D w (x.1, j) * A j x.2) * (∑ k, D w (y.1, k) * A k y.2) = _
    rw [e]
    simp only [hG, Finset.mul_sum]
    split_ifs with h
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · rw [zero_add]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring

theorem JetsLin_proof : JetsLin := by
  intro K _ _ _ l linv ph hlp hu hph hj h2 n _ T γ G hG hT ν _ M Cm hC hM
  obtain ⟨J, hJ, hJe⟩ := shape_orthogonal_holds K l linv ph 1 hlp hu hph (InflationOneCocycles.shapeAt_one hlp hph hj)
    (Fin 4 × n) (fun _ => (1 : K)) (fun _ => by rw [norm_one]) G hG
  have hq : JetsIn (unitBall K)
      (MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun _ : Fin 4 × n => (1 : K))) :=
    InflationOneCocycles.jetsIn_half_sqSum (hj 2 (by norm_num)) fun _ => (unitBall K).one_mem
  have c0 : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (jet l ph 2 / 2) * sqSum (fun _ : Fin 4 × n => (1 : K)))) = 0 := by
    rw [map_neg, map_mul, cc_sqSum, mul_zero, neg_zero]
  have k1 : JetsIn (unitBall K) (linSub γ (tens4 T)) := by
    rw [hT, hJe]
    exact jetsIn_mul (jetsIn_mvExp c0 (jetsIn_neg hq)) hJ
  have k2 : JetsIn (unitBall K) (linSub Cm (linSub γ (tens4 T))) := jetsIn_linSub hC k1
  have e : (fun (w : Fin 4 × n) (x : Fin 4 × ν) => ∑ w', γ w w' * Cm w' x) = four M := by
    funext w x
    exact hM w.1 w.2 x.1 x.2
  rw [linSub_linSub, e, linSub_tens4] at k2
  exact jets_fourth_holds K (unitBall K) ν (linSub M T) fourth_root_mem k2

end Formalism.L2.Th1.GD
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.MulRing
section
noncomputable section

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK)
open Formalism.L2.Th1.CM (omegaK)

namespace GramFrameMultiplicativityLemmas

theorem indep_sqrt {d : ℕ} (hd : 0 < d) (P Q : ℤ)
    (h : (P : ℂ) + (Q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = 0) : P = 0 ∧ Q = 0 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  refine ⟨hre, ?_⟩
  rcases him with h1 | h1
  · exact h1
  · exact absurd h1 (by positivity)

theorem sqrt_sq (d : ℕ) :
    (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  linear_combination Complex.I * Complex.I * h + (d : ℂ) * Complex.I_mul_I

theorem odd_b {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) : Odd b := by
  have h1 := hOK.1
  have h8 := hOK.2.2.1
  rcases Int.even_or_odd b with ⟨k, hk⟩ | h
  · exfalso
    have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
      rw [hk] at h1
      linear_combination (-1 : ℤ) * h1
    generalize (a : ℤ) * c - k * k = X at h2
    omega
  · exact h

theorem gcd_one {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) :
    Int.gcd (a : ℤ) (Int.gcd b c : ℤ) = 1 := by
  by_contra hne
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hne
  have hg : (r : ℤ) ∣ (Int.gcd (a : ℤ) (Int.gcd b c : ℤ) : ℤ) := by exact_mod_cast hrg
  have h1 : (r : ℤ) ∣ (a : ℤ) := hg.trans (Int.gcd_dvd_left _ _)
  have h2 : (r : ℤ) ∣ (Int.gcd b c : ℤ) := hg.trans (Int.gcd_dvd_right _ _)
  have h3 : (r : ℤ) ∣ b := h2.trans (Int.gcd_dvd_left _ _)
  have h4 : (r : ℤ) ∣ c := h2.trans (Int.gcd_dvd_right _ _)
  obtain ⟨a', ha'⟩ := h1
  obtain ⟨b', hb'⟩ := h3
  obtain ⟨c', hc'⟩ := h4
  have h0 := hOK.1
  have hdv : ((r * r : ℕ) : ℤ) ∣ (d : ℤ) := by
    refine ⟨4 * a' * c' - b' * b', ?_⟩
    rw [ha', hb', hc'] at h0
    push_cast
    linear_combination (-1 : ℤ) * h0
  have hdv' : r * r ∣ d := by exact_mod_cast hdv
  have hu := (Irreducible.squarefree hOK.2.2.2) r hdv'
  exact hr.one_lt.ne' (Nat.isUnit_iff.mp hu)

theorem dvd_of_prim {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) (y : ℤ)
    (hb : (a : ℤ) ∣ y * b) (hc : (a : ℤ) ∣ y * c) : (a : ℤ) ∣ y := by
  have e1 := Int.gcd_eq_gcd_ab b c
  have e2 := Int.gcd_eq_gcd_ab (a : ℤ) (Int.gcd b c : ℤ)
  rw [gcd_one hOK] at e2
  set u := Int.gcdA b c
  set v := Int.gcdB b c
  set u' := Int.gcdA (a : ℤ) (Int.gcd b c : ℤ)
  set v' := Int.gcdB (a : ℤ) (Int.gcd b c : ℤ)
  have hy : y = (a : ℤ) * (y * u') + (y * b) * (u * v') + (y * c) * (v * v') := by
    push_cast at e2
    linear_combination y * e2 + y * v' * e1
  rw [hy]
  exact dvd_add (dvd_add (dvd_mul_right _ _) (hb.mul_right _)) (hc.mul_right _)

end GramFrameMultiplicativityLemmas

open GramFrameMultiplicativityLemmas in
theorem MulRing_proof : MulRing := by
  intro a b c d ha hd lam hlam hOK z hz
  have hw1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ) := rfl
  have hw2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d := rfl
  obtain ⟨x, y, e1⟩ := PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₁_mem_lattice)
  obtain ⟨x', y', e2⟩ := PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₂_mem_lattice)
  rw [hw1, hw2] at e1 e2
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hS := sqrt_sq d
  unfold Formalism.L2.Th1.F.cmTheta at e1 e2
  set S : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hSdef
  have f1 : (x : ℂ) * a + y * (((b : ℂ) + S) / 2) = z * a := by
    apply mul_left_cancel₀ hlam
    linear_combination e1
  have f2 : (x' : ℂ) * a + y' * (((b : ℂ) + S) / 2) = z * (((b : ℂ) + S) / 2) := by
    apply mul_left_cancel₀ hlam
    linear_combination e2
  have key : (((4 * a * a * x' + 2 * a * y' * b - 2 * x * a * b - y * (b * b - d) : ℤ)) : ℂ)
      + ((2 * a * y' - 2 * x * a - 2 * y * b : ℤ) : ℂ) * S = 0 := by
    push_cast
    linear_combination 4 * (a : ℂ) * f2 - 2 * ((b : ℂ) + S) * f1 + (y : ℂ) * hS
  obtain ⟨k1, k2⟩ := indep_sqrt hd _ _ key
  have h0 := hOK.1
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb : (a : ℤ) ∣ y * b := by
    refine ⟨y' - x, ?_⟩
    have h2 : (2 : ℤ) * (y * b) = 2 * ((a : ℤ) * (y' - x)) := by linear_combination (-1 : ℤ) * k2
    exact mul_left_cancel₀ two_ne_zero h2
  have hc : (a : ℤ) ∣ y * c := by
    refine ⟨-x', ?_⟩
    have h2 : (4 * (a : ℤ)) * (y * c) = (4 * (a : ℤ)) * ((a : ℤ) * (-x')) := by
      linear_combination k1 - b * k2 + y * h0
    exact mul_left_cancel₀ (mul_ne_zero four_ne_zero haZ) h2
  obtain ⟨y₀, hy₀⟩ := dvd_of_prim hOK y hb hc
  obtain ⟨k, hk⟩ := odd_b hOK
  have hom : omegaK d = (1 + S) / 2 := rfl
  refine ⟨x + y₀ * k, y₀, ?_⟩
  rw [hom]
  apply mul_right_cancel₀ haC
  rw [← f1, hy₀, hk]
  push_cast
  ring

end Formalism.L2.Th1.GD
end
end

