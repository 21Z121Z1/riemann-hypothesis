import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0003
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjPotDens
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace ProjPotDens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}

theorem affLift_analyticAt (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ∀ k, R.lift x.1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0 := by
  have hG := (ProjRegular.lift_analyticAt hB x hx).1
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hc : ∀ q, AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1 q) (BV.chart j x) :=
    fun q => analyticAt_pi_iff.1 hG q
  have hp' : ∀ k, R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ ≠ 0 := by
    rw [hsx]; exact hp
  refine ⟨?_, eventually_all.2 fun k => (hc ⟨k, p k⟩).continuousAt.eventually_ne (hp' k)⟩
  show AnalyticAt ℂ (fun u q => R.lift x.1 ((BV.chart j).symm u).1 q /
    R.lift x.1 ((BV.chart j).symm u).1 ⟨q.1, p q.1⟩) (BV.chart j x)
  exact AnalyticAt.pi fun q => (hc q).div (hc ⟨q.1, p q.1⟩) (hp' q.1)

theorem fderiv_affLift_self (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) (w : Fin n → ℂ) (k : K) :
    fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
      ⟨k, p k⟩ = 0 := by
  obtain ⟨hτa, hev⟩ := affLift_analyticAt hB x hx p hp
  have h1 := hasFDerivAt_pi'.1 hτa.differentiableAt.hasFDerivAt ⟨k, p k⟩
  have h2 : HasFDerivAt (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1) ⟨k, p k⟩)
      (0 : (Fin n → ℂ) →L[ℂ] ℂ) (BV.chart j x) :=
    (hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq (by
      filter_upwards [hev] with u hu
      exact div_self (hu k))
  have := congrArg (fun L => L w) (h1.unique h2)
  simpa using this

theorem injective_fderiv_affLift (hB : HoloMap BV R.A Subtype.val) (x : V) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) {j j' : Fin BV.n} (hj : x ∈ (BV.chart j).source)
    (hj' : x ∈ (BV.chart j').source)
    (hr : Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u => affCoord p (R.lift x.1 ((BV.chart j').symm u).1)) (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) = n) :
    Function.Injective (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1))
      (BV.chart j x)) := by
  set F : Fin BV.n → (Fin n → ℂ) → ((Σ k, ι k) → ℂ) :=
    fun i u => affCoord p (R.lift x.1 ((BV.chart i).symm u).1) with hF
  have hinj' : Function.Injective (fderiv ℂ (F j') (BV.chart j' x)) := by
    have hk := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℂ (F j') (BV.chart j' x) : (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))
    rw [hr, Module.finrank_fin_fun] at hk
    have h0 : LinearMap.ker (fderiv ℂ (F j') (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ)) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by omega)
    exact LinearMap.ker_eq_bot.1 h0
  have hu0 : BV.chart j x ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hv0 : BV.chart j' x ∈ (BV.chart j').target := (BV.chart j').map_source hj'
  have hsj : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hj
  have hsk : (BV.chart j').symm (BV.chart j' x) = x := (BV.chart j').left_inv hj'
  have hτu : (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x) = BV.chart j' x := by simp [hsj]
  have hτ : AnalyticAt ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x) :=
    BV.holo j j' _ ⟨hu0, by
      show (BV.chart j).symm (BV.chart j x) ∈ (BV.chart j').source; rw [hsj]; exact hj'⟩
  have hσ : AnalyticAt ℂ (BV.chart j ∘ (BV.chart j').symm)
      ((BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hτu]
    exact BV.holo j' j _ ⟨hv0, by
      show (BV.chart j').symm (BV.chart j' x) ∈ (BV.chart j).source; rw [hsk]; exact hj⟩
  have hev : ∀ᶠ u in 𝓝 (BV.chart j x), (BV.chart j).symm u ∈ (BV.chart j').source :=
    ((BV.chart j).continuousAt_symm hu0).preimage_mem_nhds (by
      show (BV.chart j').source ∈ 𝓝 ((BV.chart j).symm (BV.chart j x))
      rw [hsj]; exact (BV.chart j').open_source.mem_nhds hj')
  have hid : (BV.chart j ∘ (BV.chart j').symm) ∘ (BV.chart j' ∘ (BV.chart j).symm)
      =ᶠ[𝓝 (BV.chart j x)] id := by
    filter_upwards [hev, (BV.chart j).open_target.mem_nhds hu0] with u hu hut
    simp [(BV.chart j').left_inv hu, (BV.chart j).right_inv hut]
  have hq : F j =ᶠ[𝓝 (BV.chart j x)] F j' ∘ (BV.chart j' ∘ (BV.chart j).symm) := by
    filter_upwards [hev] with u hu
    simp [hF, (BV.chart j').left_inv hu]
  have hFa : AnalyticAt ℂ (F j') ((BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hτu]; exact (affLift_analyticAt hB x hj' p hp).1
  have hD : fderiv ℂ (F j) (BV.chart j x) = (fderiv ℂ (F j') (BV.chart j' x)).comp
      (fderiv ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hq.fderiv_eq, fderiv_comp _ hFa.differentiableAt hτ.differentiableAt, hτu]
  have hT : Function.LeftInverse (fderiv ℂ (BV.chart j ∘ (BV.chart j').symm) (BV.chart j' x))
      (fderiv ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    intro w
    have h1 := hid.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_comp _ hσ.differentiableAt hτ.differentiableAt, fderiv_id, hτu] at h1
    simpa using congrArg (fun L => L w) h1
  show Function.Injective (fderiv ℂ (F j) (BV.chart j x))
  rw [hD]
  exact hinj'.comp hT.injective

theorem hessC_chartPot (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    ReciprocityTheory.AnForm.hessC (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) (BV.chart j x) =
      ReciprocityTheory.AnForm.hessC
        (fsMultiPot ∘ fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by
  obtain ⟨hτa, hev⟩ := affLift_analyticAt hB x hx p hp
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  set G : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun u => R.lift x.1 ((BV.chart j).symm u).1 with hG
  set τ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun u => affCoord p (G u) with hτ
  have hGa : ∀ q, AnalyticAt ℂ (fun u => G u q) (BV.chart j x) :=
    fun q => analyticAt_pi_iff.1 (ProjRegular.lift_analyticAt hB x hx).1 q
  have hp' : ∀ k, G (BV.chart j x) ⟨k, p k⟩ ≠ 0 := by
    intro k; simp only [hG, hsx]; exact hp k
  have hτ1 : ∀ u, (∀ k, G u ⟨k, p k⟩ ≠ 0) → ∀ k, τ u ⟨k, p k⟩ = 1 :=
    fun u hu k => div_self (hu k)
  let g : (Fin n → ℂ) → ℂ := fun u => ∏ k, G u ⟨k, p k⟩ ^ 2
  have hga : AnalyticAt ℂ g (BV.chart j x) :=
    Finset.univ.analyticAt_fun_prod fun k _ => (hGa ⟨k, p k⟩).pow 2
  have hg0 : g (BV.chart j x) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero 2 (hp' k)
  have hC : ContDiffAt ℝ 2 fsMultiPot (τ (BV.chart j x)) :=
    (levi_fsMultiPot p (fun k => by rw [hτ1 _ hp' k]; exact one_ne_zero) 0).1
  have hgerm : (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) =ᶠ[𝓝 (BV.chart j x)]
      fun u => (fsMultiPot ∘ τ) u + Real.log ‖g u‖ := by
    filter_upwards [hev] with u hu
    show ∑ k, Real.log (∑ i, ‖G u ⟨k, i⟩‖ ^ 2) =
      ∑ k, Real.log (∑ i, ‖τ u ⟨k, i⟩‖ ^ 2) + Real.log ‖∏ k, G u ⟨k, p k⟩ ^ 2‖
    have hs : ∀ k, ∑ i, ‖G u ⟨k, i⟩‖ ^ 2 = ‖G u ⟨k, p k⟩‖ ^ 2 * ∑ i, ‖τ u ⟨k, i⟩‖ ^ 2 := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hn : ‖G u ⟨k, p k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hu k)
      simp only [hτ, affCoord, norm_div, div_pow]
      field_simp
    have hpos : ∀ k, 0 < ∑ i, ‖τ u ⟨k, i⟩‖ ^ 2 := fun k =>
      lt_of_lt_of_le (by rw [hτ1 u hu k]; norm_num)
        (Finset.single_le_sum (f := fun i => ‖τ u ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ (p k)))
    have hne : ∀ k ∈ (Finset.univ : Finset K), ‖G u ⟨k, p k⟩ ^ 2‖ ≠ 0 := fun k _ => by
      rw [norm_pow]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hu k))
    rw [norm_prod, Real.log_prod hne, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs k, norm_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu k))) (hpos k).ne',
      add_comm]
  rw [hessCGerm _ _ _ hgerm]
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g _
    (hC.comp _ (hτa.contDiffAt.restrict_scalars ℝ)) hga hg0

end ProjPotDens

theorem ProjPotDens.proof : ProjPotDens.Statement := by
  intro K _ ι _ P J n R V BV hB j y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x, x ∈ (BV.chart j).source ∧ BV.chart j x = y :=
    ⟨_, (BV.chart j).map_target hy, (BV.chart j).right_inv hy⟩
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx

  have hdens : ∀ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) →
      locDens BV (fun _ => multiprojPot R V) j (BV.chart j x) =
        ReciprocityTheory.AnForm.maDens (fun _ => ProjPotDens.fsMultiPot ∘
          fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by
    intro p hp
    unfold locDens
    rw [hsx]
    exact maDens_congr_hessC _ _ _ fun _ => ProjPotDens.hessC_chartPot hB x hx p hp
  have hlevi : ∀ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) →
      ContDiffAt ℝ 2 (ProjPotDens.fsMultiPot ∘
          fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
        ∀ w, 0 ≤ ReciprocityTheory.AnForm.levi (ProjPotDens.fsMultiPot ∘
            fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w ∧
          (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
              ≠ 0 →
            0 < ReciprocityTheory.AnForm.levi (ProjPotDens.fsMultiPot ∘
              fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w) := by
    intro p hp
    have hτa := (ProjPotDens.affLift_analyticAt hB x hx p hp).1
    have hτ1 : ∀ k, affCoord p (R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1) ⟨k, p k⟩ ≠ 0 := by
      intro k
      show R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ /
        R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ ≠ 0
      rw [hsx, div_self (hp k)]
      exact one_ne_zero
    have hC := (ProjPotDens.levi_fsMultiPot p hτ1 0).1
    refine ⟨hC.comp (f := fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x)
      (hτa.contDiffAt.restrict_scalars ℝ), fun w => ?_⟩
    rw [ReciprocityTheory.AnForm.levi_comp w hτa hC]
    obtain ⟨_, h1, h2⟩ := ProjPotDens.levi_fsMultiPot p hτ1
      (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w)
    exact ⟨h1, h2 fun k => ProjPotDens.fderiv_affLift_self hB x hx p hp w k⟩
  refine ⟨?_, fun hfull => ?_⟩
  · obtain ⟨p, hp⟩ : ∃ p : (k : K) → ι k, ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0 :=
      ⟨fun k => Classical.choose ((R.mem x.1 x.1 (R.mem_U x.1)).1 k),
        fun k => Classical.choose_spec ((R.mem x.1 x.1 (R.mem_U x.1)).1 k)⟩
    rw [hdens p hp]
    obtain ⟨hC, hl⟩ := hlevi p hp
    exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
      hessC_posSemidef _ _ hC fun w => (hl w).1
  · rw [hsx] at hfull
    obtain ⟨p, hp, j', hj', hr⟩ := hfull
    have hinj := ProjPotDens.injective_fderiv_affLift hB x p hp hx hj' hr
    rw [hdens p hp]
    obtain ⟨hC, hl⟩ := hlevi p hp
    unfold ReciprocityTheory.AnForm.maDens
    refine mul_pos (mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
      (pow_pos (div_pos two_pos Real.pi_pos) _))
      (ReciprocityTheory.AnForm.A.mdisc_pos_of_posDef _ fun _ => hessC_posDef _ _ hC fun w hw =>
        (hl w).2 fun h0 => hw (hinj (h0.trans (map_zero _).symm))).2

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjPotMassEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff

namespace ProjPotMassEq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}

omit [Fintype K] in

theorem blockSum_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hz k
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))

theorem sqSum_pos {m : ℕ} {v : Fin (m + 1) → ℂ} (hv : v ≠ 0) : 0 < ∑ l, ‖v l‖ ^ 2 := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hv
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hl) 2) (Finset.single_le_sum (f := fun l => ‖v l‖ ^ 2)
    (fun l _ => by positivity) (Finset.mem_univ l))

def uFun (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (z : V) : ℝ :=
  (projPot R Ψ V).φ z z - (multiprojPot R V).φ z z

theorem projPot_eq (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (b z : V)
    (hzb : z.1 ∈ R.U b.1) (hz : Ψ (segre (R.lift z.1 z.1)) ≠ 0) :
    (projPot R Ψ V).φ b z = (multiprojPot R V).φ b z + uFun R Ψ V z := by
  obtain ⟨c, hc, hcz⟩ := R.compat b.1 z.1 z.1 ⟨hzb, R.mem_U z.1⟩
  have hm := (R.mem z.1 z.1 (R.mem_U z.1)).1
  have hc2 : ∀ k, ‖c k‖ ^ 2 ≠ 0 := fun k => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  have hS : ∀ k, ∑ i, ‖R.lift b.1 z.1 ⟨k, i⟩‖ ^ 2 =
      ‖c k‖ ^ 2 * ∑ i, ‖R.lift z.1 z.1 ⟨k, i⟩‖ ^ 2 := by
    intro k
    rw [hcz]
    simp [mul_pow, Finset.mul_sum]
  have hseg : segre (R.lift b.1 z.1) = (∏ k, c k) • segre (R.lift z.1 z.1) := by
    rw [hcz]
    funext i
    simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  have hN : ∑ l, ‖Ψ (segre (R.lift b.1 z.1)) l‖ ^ 2 =
      ‖∏ k, c k‖ ^ 2 * ∑ l, ‖Ψ (segre (R.lift z.1 z.1)) l‖ ^ 2 := by
    rw [hseg, map_smul]
    simp [mul_pow, Finset.mul_sum]
  have hsum : ∑ k, Real.log (∑ i, ‖R.lift b.1 z.1 ⟨k, i⟩‖ ^ 2) =
      ∑ k, Real.log (‖c k‖ ^ 2) + ∑ k, Real.log (∑ i, ‖R.lift z.1 z.1 ⟨k, i⟩‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [hS k, Real.log_mul (hc2 k) (blockSum_pos hm k).ne']
  have hprod : Real.log (‖∏ k, c k‖ ^ 2) = ∑ k, Real.log (‖c k‖ ^ 2) := by
    rw [norm_prod, ← Finset.prod_pow, Real.log_prod fun k _ => hc2 k]
  simp only [uFun, projPot, multiprojPot]
  rw [hN, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2
    (Finset.prod_ne_zero_iff.2 fun k _ => hc k))) (sqSum_pos hz).ne', hsum, hprod]
  ring

theorem isPotential_multiprojPot {V : Set R.X} {BV : FinHolAtlas n V}
    (hH : HoloMap BV R.A Subtype.val) : IsPotential BV (multiprojPot R V) := by
  refine isPotential_congr BV (P := (potOf R (HermLine.sqMetric (fun _ => 2))).pullback
    Subtype.val hH.1) (fun _ => rfl) (fun x z hz => ?_)
    (isPotentialPullback R.A BV Subtype.val hH _
      (isPotential_potOf R (isSmoothHerm_sqMetric _)))
  have hm := (R.mem x.1 z.1 hz).1
  show Real.log (∏ k, Real.sqrt (∑ i, ‖R.lift x.1 z.1 ⟨k, i⟩‖ ^ 2) ^ 2) =
    ∑ k, Real.log (∑ i, ‖R.lift x.1 z.1 ⟨k, i⟩‖ ^ 2)
  rw [Finset.prod_congr rfl fun k _ => Real.sq_sqrt (by positivity),
    Real.log_prod fun k _ => (blockSum_pos hm k).ne']

theorem smooth_uFun (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) : BV.Smooth (uFun R Ψ V) := by
  intro j t ht
  set x : V := (BV.chart j).symm t with hx_def
  have hxs : x ∈ (BV.chart j).source := (BV.chart j).map_target ht.1
  have htx : BV.chart j x = t := (BV.chart j).right_inv ht.1
  have hF := ProjRegular.proj_analyticAt Ψ hH x hxs
  have hU := (ProjRegular.lift_analyticAt hH x hxs).2
  rw [htx] at hF hU

  have hp : ContDiffAt ℝ ∞ (fun t' => (projPot R Ψ V).φ x ((BV.chart j).symm t')) t := by
    have hsq : ContDiffAt ℝ ∞ (fun t' => ∑ l, ‖Ψ (segre (R.lift x.1 ((BV.chart j).symm t').1)) l‖ ^ 2) t :=
      ContDiffAt.sum fun l _ =>
        (((analyticAt_pi_iff.1 hF l).contDiffAt).restrict_scalars ℝ).norm_sq ℝ
    have hne : ∑ l, ‖Ψ (segre (R.lift x.1 ((BV.chart j).symm t).1)) l‖ ^ 2 ≠ 0 :=
      (sqSum_pos (hΨ x.1 x.2)).ne'
    exact hsq.log hne

  have hm : ContDiffAt ℝ ∞ (fun t' => (multiprojPot R V).φ x ((BV.chart j).symm t')) t :=
    ((isPotential_multiprojPot hH).1 x j).contDiffAt
      (((BV.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x.1).preimage
        continuous_subtype_val)).mem_nhds ⟨ht.1, R.mem_U x.1⟩)
  refine ((hp.sub hm).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU] with t' ht'
  have := projPot_eq Ψ x ((BV.chart j).symm t') ht' (hΨ _ ((BV.chart j).symm t').2)
  simp only [Function.comp_apply]
  linarith

theorem proof : ProjPotMassEq.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hV hΨ C hC
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  refine massIndep_clopen BV (isPotential_multiprojPot hH) (projPot R Ψ V) (uFun R Ψ V)
    (smooth_uFun Ψ hH hΨ) hC fun j t ht _ => locDens_congr_germ BV _ _ j t ?_
  have hxs : (BV.chart j).symm t ∈ (BV.chart j).source := (BV.chart j).map_target ht
  have hU := (ProjRegular.lift_analyticAt hH ((BV.chart j).symm t) hxs).2
  rw [(BV.chart j).right_inv ht] at hU
  filter_upwards [hU] with t' ht'
  exact projPot_eq Ψ _ _ ht' (hΨ _ ((BV.chart j).symm t').2)

end ProjPotMassEq

end GroundTheory.Heights₂.Heights.Targets
end
end

