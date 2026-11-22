import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0010
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0001
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstAssoc
section
open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

theorem tendsto_cofinite_double {K α β : Type*} [NormedField K] (c : α → β → K) (d : β → K)
    (C : ℝ) (hC : ∀ a b, ‖c a b‖ ≤ C) (hc : ∀ b, Tendsto (fun a => c a b) cofinite (𝓝 0))
    (hd : Tendsto d cofinite (𝓝 0)) :
    Tendsto (fun p : α × β => c p.1 p.2 * d p.2) cofinite (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have h1 : Tendsto (fun b => C * ‖d b‖) cofinite (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hd).const_mul C
  have h2 : {b | ¬ C * ‖d b‖ < ε}.Finite :=
    eventually_cofinite.1 (h1.eventually (gt_mem_nhds hε))
  have h3 : ∀ b, {a | ¬ ‖c a b * d b‖ < ε}.Finite := by
    intro b
    have : Tendsto (fun a => c a b * d b) cofinite (𝓝 0) := by
      simpa using (hc b).mul_const (d b)
    exact eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 this ε hε)
  rw [eventually_cofinite]
  refine (h2.biUnion (t := fun b => (fun a => (a, b)) '' {a | ¬ ‖c a b * d b‖ < ε})
    (fun b _ => (h3 b).image _)).subset ?_
  rintro ⟨a, b⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Set.mem_iUnion]
  refine ⟨b, ?_, a, hp, rfl⟩
  intro hlt
  apply hp
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hC a b) (norm_nonneg _)) hlt

theorem small_csub_of_small (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ τ : Type) [Fintype σ] (t : σ → MvPowerSeries τ K) (ht : ∀ i, Small (t i))
    (u : MvPowerSeries σ K) (hu : Small u) : Small (csub t u) := by
  obtain ⟨hI, hB, hP, hC, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  set c := MvPowerSeries.constantCoeff u with hc
  have hCi : Intg (MvPowerSeries.C c : MvPowerSeries σ K) := (hC c).2.1 hu.2.le
  have h1 : Intg (u - MvPowerSeries.C c) := (hI _ _ hu.1 hCi).2.1
  have hb1 : Bdd (u - MvPowerSeries.C c) := (hP _ 0).2.2 h1
  have hbu : Bdd u := (hP _ 0).2.2 hu.1
  have h2 : Small (csub t (u - MvPowerSeries.C c)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hb1).2.2.2 h1 (by simp [hc])
  obtain ⟨hR, hRC, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have h3 : csub t u = csub t (u - MvPowerSeries.C c) + MvPowerSeries.C c := by
    rw [(hR _ _ hbu (hC c).1).2.1, hRC]; ring
  refine ⟨(GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hbu).2.2.1 hu.1, ?_⟩
  rw [h3, map_add, MvPowerSeries.constantCoeff_C]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2.2 hu.2)

theorem csub_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K)
    (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) →
    (∀ i, Small (t i)) → Bdd S →
    (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  intro K _ _ _ ρ σ τ _ _ s t S hs ht hS
  have hst : ∀ j, Small (csub t (s j)) := fun j => small_csub_of_small K σ τ t ht _ (hs j)
  refine ⟨hst, ?_⟩
  obtain ⟨hI, hB, hP, hC, -, hF, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  obtain ⟨-, -, -, hRP, hRF, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have hint : ∀ ν : ρ →₀ ℕ, Intg (∏ j, s j ^ ν j) := fun ν =>
    ((hF ρ Finset.univ _).1 fun j _ => (hP _ _).1 (hs j).1).1
  have hbd : ∀ ν : ρ →₀ ℕ, Bdd (∏ j, s j ^ ν j) := fun ν => (hP _ 0).2.2 (hint ν)
  have hprod : ∀ ν : ρ →₀ ℕ, csub t (∏ j, s j ^ ν j) = ∏ j, csub t (s j) ^ ν j := by
    intro ν
    rw [hRF ρ Finset.univ _ fun j _ => (hP _ 0).2.2 ((hP _ _).1 (hs j).1)]
    exact Finset.prod_congr rfl fun j _ => hRP _ _ ((hP _ 0).2.2 (hs j).1)
  ext μ
  obtain ⟨C, hCS⟩ := id hS
  let c : (ρ →₀ ℕ) → (σ →₀ ℕ) → K := fun ν l =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff l (∏ j, s j ^ ν j)
  let d : (σ →₀ ℕ) → K := fun l => MvPowerSeries.coeff μ (∏ i, t i ^ l i)
  have hcs : ∀ l, HasSum (fun ν => c ν l) (MvPowerSeries.coeff l (csub s S)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K ρ σ s S hs hS).1
  have hd : Tendsto d cofinite (𝓝 0) := by
    let U : MvPowerSeries σ K := fun _ => 1
    have hU : ∀ l, MvPowerSeries.coeff l U = 1 := fun _ => rfl
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t U ht ⟨1, fun l => by simp [hU]⟩).1 μ).summable.tendsto_cofinite_zero
    simpa only [hU, one_mul] using this
  have hsum : Summable (fun p : (ρ →₀ ℕ) × (σ →₀ ℕ) => c p.1 p.2 * d p.2) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    refine tendsto_cofinite_double c d C ?_ (fun l => (hcs l).summable.tendsto_cofinite_zero) hd
    intro ν l
    simp only [c, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hint ν l)).trans (hCS ν)
  have hA : HasSum (fun ν : ρ →₀ ℕ => MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ j, csub t (s j) ^ ν j))
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine hsum.hasSum.prod_fiberwise fun ν => ?_
    rw [← hprod]
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht (hbd ν)).1 μ).mul_left (MvPowerSeries.coeff ν S)
    simpa only [c, d, mul_assoc] using this
  have hB' : HasSum (fun l : σ →₀ ℕ => MvPowerSeries.coeff l (csub s S) * d l)
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine ((Equiv.prodComm _ _).hasSum_iff.2 hsum.hasSum).prod_fiberwise fun l => ?_
    exact (hcs l).mul_right (d l)
  exact hB'.tsum_eq.trans hA.tsum_eq.symm

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NodeGapNoncompact
section
namespace GlobalTheory.Proof.NodeGapNoncompact

open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem lam_eq (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    lam48 k r v b = param r k hk v b := by
  funext s
  unfold lam48
  by_cases h : s.val < k - 1
  · rw [dif_pos h]
    exact (param_cloud r k hk v b ⟨s.val, h⟩).symm
  · rw [dif_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, param_node]

theorem sign_eq (k r : ℕ) (hk : 1 ≤ k) : eps48 k r = sign r k hk := by
  funext s
  unfold eps48
  by_cases h : s.val < k - 1
  · rw [if_pos h]
    exact (sign_cloud r k hk ⟨s.val, h⟩).symm
  · rw [if_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, sign_node]
    simp only [Nat.even_iff]

theorem interlace_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u := by
  have hc : ∀ (i : ℕ) (hi : i < k - 1) (hi' : i < 2 * r + k + 1),
      param r k hk v b ⟨i, hi'⟩ = v ⟨i, hi⟩ := fun i hi _ => param_cloud r k hk v b ⟨i, hi⟩
  have hn : ∀ (hi' : k - 1 < 2 * r + k + 1),
      param r k hk v b ⟨k - 1, hi'⟩ = -b ⟨0, by omega⟩ :=
    fun _ => param_node r k hk v b ⟨0, by omega⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_cases h : i.val < k - 1
      · rw [hc i.val h]
        exact (h1 ⟨i.val, h⟩).1
      · obtain ⟨i, hi⟩ := i
        obtain rfl : i = k - 1 := by simp only at h; omega
        rw [hn]
        exact h2 hk
    · rw [hc i (by omega)]
      exact (h1 ⟨i, by omega⟩).2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun h => ?_⟩
    · have := h1 ⟨i.val, by have := i.isLt; omega⟩
      rwa [hc i.val i.isLt] at this
    · have := h2 i.val (by have := i.isLt; omega)
      rwa [hc i.val i.isLt] at this
    · have := h1 ⟨k - 1, by omega⟩
      rwa [hn] at this

theorem parity_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u := by
  unfold HalfIntegralDifference Parity
  rw [lam_eq k r hk]
  constructor
  · intro h s i
    obtain ⟨j, hj⟩ := h i s
    exact ⟨-j - 1, by push_cast; linarith⟩
  · intro h i s
    obtain ⟨j, hj⟩ := h s i
    exact ⟨-j - 1, by push_cast; linarith⟩

theorem gap_iff (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) :
    LowGapGe h r b ↔ NodeGapGe r b h := by
  constructor
  · intro H i hi
    have := H ⟨i, by omega⟩ hi
    simp only at this
    linarith
  · intro H j hj
    have := H j.val hj
    simp only [Fin.eta] at this
    linarith

theorem le_sub_of_nodeGapGe (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) (hg : NodeGapGe r b h)
    (s t : Fin (2 * r + k + 1)) (hst : s < t) (hne : sign r k hk s ≠ sign r k hk t) :
    h ≤ param r k hk v b s - param r k hk v b t := by
  have hlt : s.val < t.val := hst
  have ht : k ≤ t.val := by
    by_contra hc
    apply hne
    rw [← sign_eq]
    unfold eps48
    have h1 : s.val < k - 1 := by omega
    rw [if_pos h1]
    by_cases h2 : t.val < k - 1
    · rw [if_pos h2]
    · rw [if_neg h2]
      have : t.val - (k - 1) = 0 := by omega
      simp [this]
  have htl := t.isLt
  have hi : t.val - k + 1 < 2 * r + 2 := by omega
  have h1 := hg (t.val - k) hi
  have e1 : t = nodeIdx r k hk ⟨t.val - k + 1, hi⟩ := by
    apply Fin.ext
    simp only [nodeIdx]
    omega
  have e2 : s ≤ nodeIdx r k hk ⟨t.val - k, by omega⟩ := by
    simp only [nodeIdx, Fin.le_def]
    omega
  have h2 := hd.antitone e2
  have h3 : param r k hk v b t = -b ⟨t.val - k + 1, hi⟩ := by
    conv_lhs => rw [e1, param_node]
  rw [param_node] at h2
  linarith

theorem gap_iff_noncompact (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) :
    LowGapGe h r b ↔ NoncompactGapGe r k hk (param r k hk v b) h := by
  rw [gap_iff]
  refine ⟨fun hg s t hne => ?_, nodeGapGe_of_noncompactGapGe r k hk v b h hd⟩
  rcases lt_trichotomy s t with hst | hst | hst
  · exact (le_sub_of_nodeGapGe r k hk v b h hd hg s t hst hne).trans (le_abs_self _)
  · exact absurd (congrArg _ hst) hne
  · rw [abs_sub_comm]
    exact (le_sub_of_nodeGapGe r k hk v b h hd hg t s hst hne.symm).trans (le_abs_self _)

theorem isHCParam_iff (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ↔
      IsDecreasing r k hk v b ∧ IsShiftedIntegral (param r k hk v b) := by
  unfold Formalism.QuantumDeterminants.IsHCParam IsDecreasing IsShiftedIntegral
  rw [lam_eq k r hk]
  refine and_congr Iff.rfl (forall_congr' fun s => exists_congr fun z => ?_)
  constructor <;> intro h <;> linarith

theorem gapAtLeast_iff (k r : ℕ) (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) :
    Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) lam h ↔ NoncompactGapGe r k hk lam h := by
  rw [sign_eq k r hk]
  rfl

theorem typings_equiv (k r : ℕ) (hk : 1 ≤ k) :
    (∀ (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), lam48 k r v b = param r k hk v b) ∧
    eps48 k r = sign r k hk ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u) ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u) ∧
    (∀ (h : ℝ) (b : Fin (2 * r + 2) → ℝ), LowGapGe h r b ↔ NodeGapGe r b h) :=
  ⟨lam_eq k r hk, sign_eq k r hk, interlace_iff k r hk, parity_iff k r hk,
    fun h b => gap_iff h r b⟩

end GlobalTheory.Proof.NodeGapNoncompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
section
open Formalism.REAL Finset
namespace GlobalTheory

theorem ofFn_prod_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : W →ₗ[ℂ] V) : ∀ (t : ℕ) (f : Fin t → Module.End ℂ V)
    (g : Fin t → Module.End ℂ W), (∀ k w, ι (g k w) = f k (ι w)) →
    ∀ w, ι ((List.ofFn g).prod w) = (List.ofFn f).prod (ι w) := by
  intro t
  induction t with
  | zero => intro f g _ w; simp
  | succ t ih =>
    intro f g h w
    simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    rw [h, ih (fun i => f i.succ) (fun i => g i.succ) (fun k => h k.succ)]

theorem qminor_intertwine : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  intro V W _ _ _ _ n t E E' ι h a b u w
  have hT : ∀ (u : ℂ) (a b : Fin n) (w : W), ι (Tm E' u a b w) = Tm E u a b (ι w) := by
    intro u a b w
    unfold Tm
    split_ifs <;> simp [h, Module.algebraMap_end_apply]
  unfold qminor
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul]
  congr 1
  exact ofFn_prod_intertwine ι t _ _ (fun k w => hT _ _ _ w) w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
section
open Formalism.REAL Finset

namespace GlobalTheory

open Finset in

theorem _root_.GlobalTheory.qminor_polyMap (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (s : ℂ) :
    ∃ c : ℕ → A, ∀ u : ℂ, _root_.Formalism.REAL.qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  classical
  let F : Equiv.Perm (Fin t) → Fin t → Polynomial A := fun σ k =>
    Polynomial.C (if a (σ k) = b k then (1 : A) else 0) * Polynomial.X +
      Polynomial.C ((if a (σ k) = b k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) +
        E (a (σ k)) (b k))
  let P : Polynomial A :=
    ∑ σ, Polynomial.C (((Equiv.Perm.sign σ : ℤ) : A)) * (List.ofFn (F σ)).prod
  have hdeg : P.natDegree < t + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    have h1 : ∀ k, (F σ k).natDegree ≤ 1 := fun k =>
      (Polynomial.natDegree_add_le _ _).trans
        (max_le ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by simp))
    rw [List.map_ofFn, List.sum_ofFn]
    calc ∑ k, (Polynomial.natDegree ∘ F σ) k ≤ ∑ _k : Fin t, 1 := Finset.sum_le_sum fun k _ => h1 k
      _ = t := by simp
  refine ⟨fun i => P.coeff i, fun u => ?_⟩
  have hcomm : ∀ (p : Polynomial A) (k : ℕ),
      Commute ((RingHom.id A) (p.coeff k)) (algebraMap ℂ A u) := fun p k =>
    Algebra.commute_algebraMap_right u _
  have hF : ∀ σ k, Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) (F σ k) =
      _root_.Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (a (σ k)) (b k) := by
    intro σ k
    unfold _root_.Formalism.REAL.Tm
    simp only [F, Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      RingHom.id_apply]
    split_ifs with h
    · rw [one_mul, ← add_assoc, ← map_add]
      congr 2
      ring
    · simp
  have hP : Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) P = _root_.Formalism.REAL.qminor E a b (u - s) := by
    unfold _root_.Formalism.REAL.qminor
    simp only [P, Polynomial.eval₂_finset_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Polynomial.eval₂_mul_noncomm _ _ (hcomm _), Polynomial.eval₂_C,
      Polynomial.eval₂_list_prod_noncomm _ _ _ (fun p _ => hcomm p), List.map_ofFn]
    simp only [Function.comp_def, hF, RingHom.id_apply]
  rw [← hP, Polynomial.eval₂_eq_sum_range' _ hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasEigenvalueSummand
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

private lemma dualTens_casimir_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (x : Fin n → M) :
    ∑ a, ∑ b, dualTens E a b (dualTens E b a x)
      = (fun i => Cas E (x i)) + (n : ℂ) • x + (2 : ℂ) • splitCas E x := by
  funext i
  have h1 : ∀ a b, dualTens E a b (dualTens E b a x) i
      = E a b (E b a (x i)) - (if i = a then E a b (x b) else 0)
        - (if i = b then E b a (x a) else 0) + (if i = b then x b else 0) := by
    intro a b
    simp only [dualTens, map_sub, if_true]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  simp only [Finset.sum_apply, h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, splitCas, Cas,
    LinearMap.sum_apply, Module.End.mul_apply]
  rw [Finset.sum_comm (f := fun a b => if i = a then E a b (x b) else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel

private lemma casG_sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    casG (μ - Pi.single s 1) = casG μ - 2 * μ s + 1 := by
  unfold casG
  have : ∀ a, (μ - Pi.single s 1 : Fin n → ℝ) a ^ 2 = μ a ^ 2 + (if s = a then (-2 * μ s + 1) else 0) := by
    intro a
    by_cases h : s = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem splitCas_eigenvalue_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → ∀ s (y : N s), splitCas E (io s y) = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io s y := by
  intro M _ _ n ε E N _ _ F io pr μ hE hF hT s y
  have h1 : io s (Cas (F s) y) = ∑ a, ∑ b, dualTens E a b (dualTens E b a (io s y)) := by
    simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hT.io_comm]
  rw [dualTens_casimir_sum, (hF s).2.2, map_smul, casG_sub_single] at h1
  have h2 : (fun i => Cas E (io s y i)) = (casG μ : ℂ) • io s y := by
    funext i; rw [hE.2.2]; rfl
  rw [h2] at h1
  have h3 : splitCas E (io s y) = (1 / 2 : ℂ) • (((casG μ - 2 * μ s + 1 : ℝ) : ℂ) • io s y
      - (casG μ : ℂ) • io s y - (n : ℂ) • io s y) := by
    rw [h1]; module
  rw [h3]; push_cast; module

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormHhJSelfLe
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

section
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}

lemma hhJ_self_norm_le_sum_sq (ε : Fin n → Bool) (x : Fin n → M) :
    ‖hhJ ε x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  unfold hhJ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, inner_self_eq_norm_sq_to_K]
  split_ifs <;> simp

lemma hhJ_self_im_eq_zero (ε : Fin n → Bool) (x : Fin n → M) :
    (hhJ ε x x).im = 0 := by
  unfold hhJ
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h : (⟪x c, x c⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (x c)
  split_ifs <;> simp [-inner_self_eq_norm_sq_to_K, h]

lemma hhJ_finsum_finsum {ι : Type} (ε : Fin n → Bool) (y : ι → Fin n → M) (In : Finset ι) :
    hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, ∑ t ∈ In, hhJ ε (y s) (y t) := by
  unfold hhJ
  simp only [Finset.sum_apply, sum_inner, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]

end

theorem sum_norm_hhJ_self_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  intro M _ _ n ε y In Cc Cs Nn horth hpos hIn hout
  rw [← Finset.sum_add_sum_compl In]
  have h1 : hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, hhJ ε (y s) (y s) := by
    rw [hhJ_finsum_finsum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact Finset.sum_eq_single_of_mem s hs fun t _ hts => horth s t (Ne.symm hts)
  have h2 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ = (∑ s ∈ In, hhJ ε (y s) (y s)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Complex.abs_re_eq_norm.mpr (hhJ_self_im_eq_zero ε (y s)), abs_of_nonneg (hpos s hs)]
  have h3 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ ≤ Cc ^ 2 * Nn := by
    rw [h2, ← h1]
    exact (Complex.re_le_norm _).trans ((hhJ_self_norm_le_sum_sq ε _).trans hIn)
  have h4 : ∑ s ∈ Inᶜ, ‖hhJ ε (y s) (y s)‖ ≤ (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    exact (hhJ_self_norm_le_sum_sq ε _).trans (hout s (Finset.mem_compl.mp hs))
  calc _ ≤ Cc ^ 2 * Nn + (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := add_le_add h3 h4
    _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearLeOfAddDistLe
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem wtNear_le_of_add_dist_le :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (Λ Λ' : Fin n → ℝ) (t t' : ℝ),
      t + ∑ a, |Λ a - Λ' a| ≤ t' → WtNear E Λ t ≤ WtNear E Λ' t' := by
  intro M _ _ n _ E Λ Λ' t t' h
  unfold WtNear
  apply Submodule.span_mono
  rintro x ⟨ω, hω, hx⟩
  refine ⟨ω, ?_, hx⟩
  have h1 : ∑ a, |ω a - Λ' a| ≤ ∑ a, (|ω a - Λ a| + |Λ a - Λ' a|) :=
    Finset.sum_le_sum fun a _ => abs_sub_le _ _ _
  rw [Finset.sum_add_distrib] at h1
  linarith

end GlobalTheory
end

