import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmulSucc
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.MapNMul

theorem cc_subst {R : Type} [CommRing R] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (k : ℕ) :
    nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem cc_nmul {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) : ∀ (k : ℕ) (i : Fin d), constantCoeff (nmul μ k i) = 0 := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    simp only [op, at2]
    rw [cc_subst (fun s => by cases s <;> simp [ih]), hμ]

theorem map_nmul (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    ∀ (k : ℕ) (i : Fin d), map φ (nmul μ k i) = nmul (fun j => map φ (μ j)) k i := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ, nmul_succ]
    simp only [op, at2]
    have hs : HasSubst (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [cc_nmul μ hμ]
    rw [map_subst hs]
    congr 1
    funext s
    cases s <;> simp [ih]

end GlobalTheory.MapNMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCover
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem nonempty_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), Nonempty (Cover A) := by
  intro n Y _ _ _ _ _ _ ι La _ A
  classical
  have hε : ∀ x : Y, ∃ ε > 0, ball (A.chart (A.pick x) x) ε ⊆ (A.chart (A.pick x)).target :=
    fun x => Metric.isOpen_iff.1 (A.chart (A.pick x)).open_target _
      ((A.chart (A.pick x)).map_source (A.mem_pick x))
  choose ε hε0 hεb using hε
  let b : ∀ x : Y, ContDiffBump (A.chart (A.pick x) x) := fun x =>
    ⟨ε x / 4, ε x / 2, by linarith [hε0 x], by linarith [hε0 x]⟩
  let β : Y → Y → ℝ := fun x => A.chiC (A.pick x) (b x)
  let K0 : Y → Set (V n) := fun x => closedBall (A.chart (A.pick x) x) (ε x / 2)
  have hK0t : ∀ x, K0 x ⊆ (A.chart (A.pick x)).target := fun x =>
    (closedBall_subset_ball (by linarith [hε0 x])).trans (hεb x)
  have hbs : ∀ x u, (b x) u ≠ 0 → u ∈ K0 x := by
    intro x u hu
    have : u ∈ Function.support (b x) := hu
    rw [(b x).support_eq] at this
    exact ball_subset_closedBall this
  have hβs : ∀ x, A.SmoothFn (β x) := fun x =>
    A.chiC_smooth (b x).contDiff (hbs x) (isCompact_closedBall _ _) (hK0t x)
  have hβ0 : ∀ x y, 0 ≤ β x y := by
    intro x y
    show 0 ≤ A.chiC _ _ y
    unfold WeightedAtlas.chiC
    split_ifs
    · exact (b x).nonneg
    · exact le_rfl
  let U : Y → Set Y := fun x =>
    (A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹' ball (A.chart (A.pick x) x) (ε x / 2)
  have hUo : ∀ x, IsOpen (U x) := fun x =>
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source
      isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => ⟨A.mem_pick x, mem_ball_self (by linarith [hε0 x])⟩
  have hUpos : ∀ x y, y ∈ U x → 0 < β x y := by
    rintro x y ⟨hy, hyb⟩
    show 0 < A.chiC _ _ y
    rw [A.chiC_of_mem hy]
    exact (b x).pos_of_mem_ball hyb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hUx y⟩)
  let pt : Fin t.card → Y := fun a => (t.equivFin.symm a).1
  let S : Y → ℝ := fun y => ∑ a, β (pt a) y
  have hS : ∀ y, 0 < S y := by
    intro y
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    have hpt : pt (t.equivFin ⟨x, hxt⟩) = x := by simp [pt]
    have h1 : β (pt (t.equivFin ⟨x, hxt⟩)) y ≤ S y :=
      Finset.single_le_sum (f := fun a => β (pt a) y) (fun a _ => hβ0 (pt a) y)
        (Finset.mem_univ _)
    rw [hpt] at h1
    linarith [hUpos x y hyx]
  have hSs : A.SmoothFn S := by
    intro j
    have : (S ∘ (A.chart j).symm) = fun v => ∑ a, β (pt a) ((A.chart j).symm v) := rfl
    rw [this]
    exact ContDiffOn.sum fun a _ => hβs (pt a) j
  refine ⟨{
    m := t.card
    idx := fun a => A.pick (pt a)
    c := fun a => A.chart (A.pick (pt a)) (pt a)
    r := fun a => 3 * ε (pt a) / 4
    chi := fun a y => β (pt a) y / S y
    r_pos := fun a => by have := hε0 (pt a); positivity
    sub := fun a => (closedBall_subset_ball (by linarith [hε0 (pt a)])).trans (hεb (pt a))
    smooth := ?_
    supp := ?_
    nonneg := fun a y => div_nonneg (hβ0 _ y) (hS y).le
    sum_one := fun y => by rw [← Finset.sum_div]; exact div_self (hS y).ne' }⟩
  · intro a j v hv
    exact ((hβs (pt a) j v hv).div (hSs j v hv) (hS _).ne')
  · intro a
    set x := pt a
    have hKc : IsClosed ((A.chart (A.pick x)).symm '' K0 x) :=
      (A.isCompact_chartImage (isCompact_closedBall _ _) (hK0t x)).isClosed
    refine (closure_minimal ?_ hKc).trans ?_
    · intro y hy
      have hy' : β x y ≠ 0 := fun h0 => hy (by simp only [h0, zero_div])
      by_contra hK
      exact hy' (A.chiC_eq_zero (hbs x) hK)
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(A.chart (A.pick x)).map_target (hK0t x hu), ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart (A.pick x)).right_inv (hK0t x hu)]
      exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu) (by linarith [hε0 x]))

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFderivLeOfBoundedGen
section
namespace GlobalTheory.FrechetDerivativeBound

theorem norm_fderiv_le_of_bounded_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {ρ R M : ℝ} (hρ : 0 < ρ) (hR : ρ < R) (u : E → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ := by
  have hp : p ∈ Metric.ball p R := Metric.mem_ball_self (hρ.trans hR)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM0 hρ.le) ?_
  intro v hv
  have hmem : ∀ t ∈ Metric.closedBall (0 : ℂ) ρ, p + t • v ∈ Metric.ball p R := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact ht.trans_lt hR
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => p + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hd : DifferentiableOn ℂ (fun t : ℂ => u (p + t • v)) (Metric.closedBall 0 ρ) :=
    hu.comp (fun t _ => (hline t).differentiableAt.differentiableWithinAt) hmem
  have hdc : DiffContOnCl ℂ (fun t : ℂ => u (p + t • v)) (Metric.ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ hρ.ne']
  have hup : DifferentiableAt ℂ u p := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hder : HasDerivAt (fun t : ℂ => u (p + t • v)) (fderiv ℂ u p v) 0 := by
    have h1 : HasFDerivAt u (fderiv ℂ u p) (p + (0 : ℂ) • v) := by
      simpa using hup.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hline 0)
  rw [← hder.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))

theorem norm_fderiv_le_of_bounded {n : ℕ} {p : ReciprocityTheory.L2DbarEstimates.V n} {ρ R M : ℝ}
    (hρ : (0 : ℝ) < ρ) (hR : ρ < R) (u : ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ :=
  norm_fderiv_le_of_bounded_gen hρ hR u hu hM

end GlobalTheory.FrechetDerivativeBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitCoeffOfCoboundarySmall
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

def yZero : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O := Sum.elim (fun i => X i) (fun _ => 0)

theorem yZero_const : ∀ s, constantCoeff (yZero (O := O) (d := d) s) = 0 := by
  intro s; cases s <;> simp [yZero]

theorem hasSubst_yZero : HasSubst (yZero (O := O) (d := d)) :=
  hasSubst_of_constantCoeff_zero yZero_const

theorem constantCoeff_subst_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ O}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ O) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ O) :
    constantCoeff (pderiv O i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]; simp

theorem subst_X_self {σ : Type} (f : MvPowerSeries σ O) : subst (fun i => (X i : MvPowerSeries σ O)) f = f := by
  rw [← map_algebraMap_eq_subst_X]
  simp [Algebra.algebraMap_self, map_id]

theorem pderiv_right_formalGroupLawCoboundaryOne (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (t : MvPowerSeries (Fin d) O) (j : Fin d) :
    pderiv O (Sum.inr j) (cob1 μ t) =
      (∑ s, subst μ (pderiv O s t) * pderiv O (Sum.inr j) (μ s)) - inR (pderiv O j t) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  unfold cob1 inL inR
  rw [map_sub, map_sub, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst μ hμ,
    ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hl, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hr]
  have e1 : ∑ s : Fin d, subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O s t) *
      pderiv O (Sum.inr j) (X (Sum.inl s)) = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [pderiv_X_of_ne (by simp), mul_zero]
  have e2 : ∑ s : Fin d, subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O s t) *
      pderiv O (Sum.inr j) (X (Sum.inr s)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O j t) := by
    rw [Finset.sum_eq_single j]
    · rw [pderiv_X_self, mul_one]
    · intro s _ hs; rw [pderiv_X_of_ne (by simpa using hs), mul_zero]
    · simp
  rw [e1, e2, sub_zero]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

theorem yZero_subst (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (g : MvPowerSeries (Fin d) O) :
    subst yZero (subst μ g) = g := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ.const) hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (μ s)) = fun i => X i := by
    have h := hμ.unit
    funext i
    have hi := congrFun h i
    simpa [op, at2, yZero] using hi
  rw [this, subst_X_self]

theorem yZero_inR (g : MvPowerSeries (Fin d) O) :
    subst yZero (inR g) = C (constantCoeff g) := by
  have hr : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  unfold inR
  rw [subst_comp_subst_apply hr hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O)) = 0 := by
    funext s; rw [subst_X hasSubst_yZero]; rfl
  rw [this, subst_zero_eq_C_constantCoeff]
  simp [Algebra.algebraMap_self, map_id]

theorem linear_coeff_law (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (s j : Fin d) :
    constantCoeff (pderiv O (Sum.inr j) (μ s)) = if s = j then 1 else 0 := by
  classical

  have hx : constantCoeff (pderiv O (Sum.inl j) (μ s)) = if s = j then 1 else 0 := by
    have h := congrFun hμ.unit s
    change subst yZero (μ s) = X s at h
    have h2 := congrArg (fun f => constantCoeff (pderiv O j f)) h
    rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ yZero_const, map_sum] at h2
    simp only [map_mul, constantCoeff_subst_of yZero_const] at h2
    simp only [Fintype.sum_sum_type, yZero,
      Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero, Finset.sum_const_zero, add_zero, pderiv_X, map_sum, map_mul] at h2
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    split_ifs at h2 ⊢ <;> exact h2
  have hsw : ∀ k : Fin d ⊕ Fin d, constantCoeff ((Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O))
      (fun i => X (Sum.inl i))) k) = 0 := by
    intro k; cases k <;> simp
  have h := hμ.comm s
  unfold swap at2 at h
  have h2 := congrArg (fun f => constantCoeff (pderiv O (Sum.inr j) f)) h
  rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hsw, map_sum] at h2
  simp only [map_mul, constantCoeff_subst_of hsw] at h2
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, pderiv_X, Pi.single_apply, Sum.inr.injEq,
    reduceCtorEq, if_false, map_zero, mul_zero, Finset.sum_const_zero, add_zero, apply_ite, map_one, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [← h2, hx]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

theorem isLocalRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

end GlobalTheory.Katz.SmallDeriv

open GlobalTheory.Katz.SmallDeriv in

theorem GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  intro p hpr C _ _ _ v O _ _ hpO _ _ hv d μ hμ t hlin hcob α ⟨i, hi⟩
  classical
  haveI : IsLocalRing O := isLocalRing_of_integers v O hv
  let π := IsLocalRing.residue O
  have hmem : ∀ a : O, π a = 0 ↔ ¬IsUnit a := by
    intro a
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast π, hmem]; exact hpO.out

  have hG : ∀ j, map π (pderiv O (Sum.inr j) (cob1 μ t)) = 0 := by
    intro j; ext n
    rw [coeff_map, coeff_pderiv, map_mul, coeff_zero]
    by_cases hn : p ∣ n (Sum.inr j) + 1
    · obtain ⟨m, hm⟩ := hn
      have e : π ((n (Sum.inr j) : O) + 1) = 0 := by
        have : ((n (Sum.inr j) : O) + 1) = ((n (Sum.inr j) + 1 : ℕ) : O) := by push_cast; ring
        rw [this, hm, Nat.cast_mul, map_mul, map_natCast, hp0, zero_mul]
      rw [e, mul_zero]
    · have := hcob (n + Finsupp.single (Sum.inr j) 1) ⟨Sum.inr j, by simpa using hn⟩
      rw [(hmem _).2 this, zero_mul]
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) (IsLocalRing.ResidueField O)) :=
    Matrix.of fun s j => map π (subst yZero (pderiv O (Sum.inr j) (μ s)))
  let w : Fin d → MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) := fun s => map π (pderiv O s t)
  have hvec : Matrix.vecMul w N = 0 := by
    funext j
    have e := congrArg (fun F => map π (subst yZero F)) (pderiv_right_formalGroupLawCoboundaryOne μ hμ.const t j)
    rw [map_subst hasSubst_yZero, hG j, ← coe_substAlgHom (hasSubst_yZero.map π), map_zero,
      ← coe_substAlgHom hasSubst_yZero, map_sub, map_sum] at e
    simp only [map_mul, coe_substAlgHom, yZero_subst μ hμ, yZero_inR, constantCoeff_pderiv, map_sub, map_sum,
      map_C] at e
    have hl : π (coeff (Finsupp.single j 1) t) = 0 := (hmem _).2 (hlin j)
    rw [hl, map_zero, sub_zero] at e
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, N, w, Matrix.of_apply]
    exact e.symm
  have hN0 : (constantCoeff : MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) →+* _).mapMatrix N = 1 := by
    ext s j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply, constantCoeff_map,
      constantCoeff_subst_of yZero_const, linear_coeff_law μ hμ, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit N.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, hN0, Matrix.det_one]
    exact isUnit_one
  have hw : w i = 0 := by
    have h1 := congrArg (fun u => Matrix.vecMul u N.adjugate) hvec
    simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.zero_vecMul] at h1
    have h2 := congrFun h1 i
    simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at h2
    exact (hdet.mul_right_eq_zero).1 (by rw [mul_comm]; exact h2)
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (fun h => hi (h ▸ dvd_zero p))
  have hsub : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hαi)
  have hc := congrArg (coeff (α - Finsupp.single i 1)) hw
  simp only [w] at hc
  rw [coeff_map, coeff_pderiv, coeff_zero, hsub, map_mul] at hc
  have hcast : (((α - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : O) + 1 = ((α i : ℕ) : O) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hαi]
  rw [hcast, map_natCast] at hc
  have hne : ((α i : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    obtain ⟨u, u', h⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpr.out).2 hi)
    have h' := congrArg (Int.cast : ℤ → IsLocalRing.ResidueField O) h
    push_cast at h'
    rw [hp0] at h'
    intro h0; rw [h0] at h'; simp at h'
  exact (hmem _).1 ((mul_eq_zero.1 hc).resolve_right hne)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneTmulQuotReduction
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem one_tmul_quot_reduction :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O),
      (∀ y : (O ⧸ I) ⊗[O] M, ∃ b : M, y = 1 ⊗ₜ b) ∧
      (∀ b : M, (1 : O ⧸ I) ⊗ₜ[O] b = 0 ↔ b ∈ I • (⊤ : Submodule O M)) ∧
      ∀ (a : O) (b : M), b ∈ Ideal.span {a} • (⊤ : Submodule O M) ↔ ∃ z, b = a • z := by
  intro O M _ _ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M))
      (TensorProduct.quotTensorEquivQuotSMul M I y)
    refine ⟨b, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]
  · intro b
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  · intro a b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Submodule.mem_top, rfl⟩

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryCommStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCech_cochainsOne_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 1), d1 F (e1 F c) = e2 F (δ F 1 c) := by
  first | exact @GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | exact GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | (intros; apply GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryCommStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCechToCatCochainsZero_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0), d0 F (e0 F c) = e1 F (δ F 0 c) := by
  first | exact @GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | exact GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | (intros; apply GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetTwoCocycleEqCechImageAddCoboundaryStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_sub_e2_eq_d1 : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := by
  first | exact @GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary | exact GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary | (intros; apply GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormal
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FormalCalc

theorem lin_formalLog (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q) :
    constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  intro hg i
  have h := congrArg (coeff (0 : Fin d →₀ ℕ)) (mul_pderiv_formalLog hg i)
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, hg, one_mul, ← coeff_zero_eq_constantCoeff_apply,
    coeff_pderiv, coeff_pderiv] at h
  simpa [lin] using h

end GlobalTheory.FormalCalc
end

