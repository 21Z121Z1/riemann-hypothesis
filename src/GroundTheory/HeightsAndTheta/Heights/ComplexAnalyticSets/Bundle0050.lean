import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionSheetedClosureEquations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteProjectionSheetedClosureEquations.surjective_of_no_germ {σ : Type} [Fintype σ] {d : ℕ}
    {w : σ → ℂ} {X : Set (σ → ℂ)} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hA : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) : Function.Surjective A := by
  by_contra hns
  have hlt : LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ)) < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hns (by simpa using LinearMap.range_eq_top.1 htop)
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfA : ∀ z, f (A z) = 0 := fun z => by
    have : f (A z) ∈ (LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ))).map f := ⟨A z, ⟨z, rfl⟩, rfl⟩
    rw [hfmap] at this
    exact this
  have hev := hA (fun y => LinearMap.toContinuousLinearMap f y)
    ((LinearMap.toContinuousLinearMap f).analyticAt _)
    (Eventually.of_forall fun z _ => by simpa using hfA z)
  apply hf0
  have hker : LinearMap.ker f = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    refine ⟨A w, mem_interior_iff_mem_nhds.2 ?_⟩
    filter_upwards [hev] with y hy
    simpa using hy
  exact LinearMap.ker_eq_top.1 hker

theorem FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (m : Multiset ℂ) (a : ℂ) :
    (m.map fun x => a - x).prod =
      ∑ j ∈ Finset.range (Multiset.card m + 1), (-1) ^ j * m.esymm j * a ^ (Multiset.card m - j) := by
  have key := congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm m)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at key
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem FiniteProjectionSheetedClosureEquations.proof
    (hball : FiniteProjectionProperBall.Statement)
    (hcount : UnbranchedProperCountConstant.Statement)
    (hesymm : ProperSheetedFibreEsymm.Statement)
    (hgrid : GridProductLowerBound.Statement) :
    FiniteProjectionSheetedClosureEquations.Statement := by
  intro σ _ X w d A hX hiso hA δ hδ hsh
  classical
  have hsurj := FiniteProjectionSheetedClosureEquations.surjective_of_no_germ A hA
  by_cases hz : ∀ᶠ t in 𝓝 (A w), δ t = 0
  · have hz' : ∀ᶠ z in 𝓝 w, δ (A z) = 0 := (A.continuous.tendsto w).eventually hz
    refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, ?_,
      Eventually.of_forall fun z _ h => absurd (h 0) one_ne_zero⟩
    filter_upwards [hz'] with z hz0 _ hne
    exact absurd hz0 hne
  obtain ⟨M, hM, hMsh⟩ := hsh
  obtain ⟨ρ, hρ, r, hr, hρM, hK⟩ := hball σ X w d A hX hiso M hM
  obtain ⟨r₂, hr₂, hδr⟩ := Metric.eventually_nhds_iff_ball.1 hδ.eventually_analyticAt
  set D : Set (Fin d → ℂ) := Metric.ball (A w) (min r r₂) with hDdef
  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ D} with hYdef
  have hDo : IsOpen D := Metric.isOpen_ball
  have hDc : IsPreconnected D := (convex_ball _ _).isPreconnected
  have hwD : A w ∈ D := Metric.mem_ball_self (lt_min hr hr₂)
  have hmap : Set.MapsTo A Y D := fun x hx => hx.2
  have hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKD hKc
    have hKr : K ⊆ Metric.ball (A w) r := hKD.trans (Metric.ball_subset_ball (min_le_left _ _))
    have heq : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKD h.2⟩, h.2⟩⟩
    rw [heq]
    exact hK K hKr hKc
  have hδD : AnalyticOnNhd ℂ δ D := fun t ht => hδr t (Metric.ball_subset_ball (min_le_right _ _) ht)
  have hne : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0 := by
    rintro W hWo hWD ⟨t, ht⟩
    by_contra hall
    push Not at hall
    have hev : δ =ᶠ[𝓝 t] 0 := by
      filter_upwards [hWo.mem_nhds ht] with s hs
      exact hall s hs
    have h0 := hδD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hWD ht) hev
    apply hz
    filter_upwards [hDo.mem_nhds hwD] with s hs
    exact h0 hs
  have hsec : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O := by
    intro x hx hδx
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hMsh x ⟨hx.1.1, hρM hx.1.2⟩ hδx
    refine ⟨O ∩ g ⁻¹' Metric.ball w ρ ∩ D, V ∩ Metric.ball w ρ ∩ A ⁻¹' D, g,
      (hg.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball).inter hDo,
      (hV.inter Metric.isOpen_ball).inter (hDo.preimage A.continuous), ⟨⟨hxV, hx.1.2⟩, hx.2⟩,
      hg.mono fun t ht => ht.1.1, fun y hy => hAg y hy.1.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨⟨hzX, hzb⟩, hzD⟩, ⟨⟨hzV, -⟩, -⟩⟩
      have hzg : z ∈ g '' O := by
        rw [← hXV]
        exact ⟨hzX, hzV⟩
      obtain ⟨t, ht, rfl⟩ := hzg
      refine ⟨t, ⟨⟨ht, hzb⟩, ?_⟩, rfl⟩
      rw [hAg t ht] at hzD
      exact hzD
    · rintro ⟨t, ⟨⟨ht, htb⟩, htD⟩, rfl⟩
      have hmem : g t ∈ X ∩ V := by
        rw [hXV]
        exact ⟨t, ht, rfl⟩
      have hA' : A (g t) ∈ D := by
        rw [hAg t ht]
        exact htD
      exact ⟨⟨⟨hmem.1, htb⟩, hA'⟩, ⟨⟨hmem.2, htb⟩, hA'⟩⟩
  obtain ⟨N, hN⟩ := hcount σ Y d A D δ hDo hDc hmap hprop hδD fun x hx hx' => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hx'
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩
  let l : (σ → Fin (N + 1)) → (σ → ℂ) →L[ℂ] ℂ := fun u =>
    ∑ i, ((u i : ℕ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i
  have hl : ∀ u z, l u z = ∑ i, ((u i : ℕ) : ℂ) * z i := by
    intro u z
    simp [l]
  choose F hFan hFeq using fun u j => hesymm σ Y d A D δ (l u) j hDo hmap hprop hδD hne hsec
  let c : (σ → Fin (N + 1)) → (σ → ℂ) → ℂ := fun u z =>
    ∑ j ∈ Finset.range (N + 1), (-1) ^ j * F u j (A z) * l u z ^ (N - j)
  have hfib : ∀ z, A z ∈ D → δ (A z) ≠ 0 → ∃ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} ∧ s.card = N := by
    intro z hzD hδz
    have h := hN (A z) hzD hδz
    have hfin := Set.finite_of_encard_eq_coe h
    refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
    have h' : ((hfin.toFinset : Finset (σ → ℂ)) : Set (σ → ℂ)).encard = N := by
      rw [hfin.coe_toFinset]
      exact h
    rw [Set.encard_coe_eq_coe_finsetCard] at h'
    exact_mod_cast h'
  have hprod : ∀ u z, A z ∈ D → δ (A z) ≠ 0 → ∀ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} → s.card = N →
      c u z = ∏ x ∈ s, (l u z - l u x) := by
    intro u z hzD hδz s hs hcard
    have hm : Multiset.card (s.val.map (l u)) = N := by simp [hcard]
    have key := FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (s.val.map (l u)) (l u z)
    rw [hm, Multiset.map_map] at key
    rw [Finset.prod_eq_multiset_prod]
    refine Eq.trans ?_ key.symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFeq u j (A z) hzD hδz s hs]
  have hcan : ∀ u z, A z ∈ D → AnalyticAt ℂ (c u) z := by
    intro u z hzD
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ)
      (f := fun j z => (-1 : ℂ) ^ j * F u j (A z) * l u z ^ (N - j)) _ fun j _ => ?_
    have h1 : AnalyticAt ℂ (F u j ∘ A) z := (hFan u j (A z) hzD).comp (ContinuousLinearMap.analyticAt A z)
    have h2 : AnalyticAt ℂ (fun z => l u z ^ (N - j)) z := ((l u).analyticAt z).pow _
    have h0 : AnalyticAt ℂ (fun _ : σ → ℂ => ((-1 : ℂ) ^ j)) z := analyticAt_const
    exact (h0.mul h1).mul h2
  let e := (Fintype.equivFin (σ → Fin (N + 1))).symm
  have hBw : Metric.ball w ρ ∩ A ⁻¹' D ∈ 𝓝 w :=
    (Metric.isOpen_ball.inter (hDo.preimage A.continuous)).mem_nhds ⟨Metric.mem_ball_self hρ, hwD⟩
  refine ⟨Fintype.card (σ → Fin (N + 1)), fun k => c (e k), fun k => hcan _ w hwD, ?_, ?_⟩
  · filter_upwards [hBw] with z hz hzX hδz k
    obtain ⟨s, hs, hcard⟩ := hfib z hz.2 hδz
    rw [hprod _ z hz.2 hδz s hs hcard]
    have hzs : z ∈ (↑s : Set (σ → ℂ)) := by
      rw [hs]
      exact ⟨⟨⟨hzX, hz.1⟩, hz.2⟩, rfl⟩
    exact Finset.prod_eq_zero hzs (sub_self _)
  · filter_upwards [hBw] with z₀ hz₀ hz₀X hall
    by_contra hcl
    set Z : Set (σ → ℂ) := {x | x ∈ Y ∧ δ (A x) ≠ 0} with hZdef
    have hZb : Bornology.IsBounded Z := Metric.isBounded_ball.subset fun x hx => hx.1.1.2
    have hZsub : Z ⊆ {x | x ∈ X ∧ δ (A x) ≠ 0} := fun x hx => ⟨hx.1.1.1, hx.2⟩
    have hZcl : z₀ ∉ closure Z := fun h => hcl (closure_mono hZsub h)
    obtain ⟨μ, hμ, U, hU, hbound⟩ := hgrid σ N Z z₀ hZb hZcl
    have hsmall : ∀ᶠ z in 𝓝 z₀, ∀ u, ‖c u z‖ < μ := by
      rw [Filter.eventually_all]
      intro u
      have h0 : c u z₀ = 0 := by
        have := hall (e.symm u)
        simpa only [Equiv.apply_symm_apply] using this
      have hcont : Tendsto (fun x => ‖c u x‖) (𝓝 z₀) (𝓝 ‖c u z₀‖) :=
        (hcan u z₀ hz₀.2).continuousAt.norm.tendsto
      rw [h0, norm_zero] at hcont
      exact hcont.eventually (gt_mem_nhds hμ)
    obtain ⟨W, hWsub, hWo, hz₀W⟩ :=
      mem_nhds_iff.1 (inter_mem (inter_mem hU hsmall) ((hDo.preimage A.continuous).mem_nhds hz₀.2))
    obtain ⟨t, ⟨z, hzW, rfl⟩, hδt⟩ := hne (A '' W) (A.isOpenMap hsurj W hWo)
      (by rintro t ⟨z, hz, rfl⟩; exact (hWsub hz).2) ⟨A z₀, z₀, hz₀W, rfl⟩
    obtain ⟨⟨hzU, hzc⟩, hzD⟩ := hWsub hzW
    obtain ⟨s, hs, hcard⟩ := hfib z hzD hδt
    have hsZ : (↑s : Set (σ → ℂ)) ⊆ Z := by
      rw [hs]
      rintro x ⟨hxY, hxA⟩
      exact ⟨hxY, by rw [hxA]; exact hδt⟩
    obtain ⟨u, hu⟩ := hbound z hzU s hsZ hcard.le
    have hlt := hzc u
    rw [hprod u z hzD hδt s hs hcard] at hlt
    have heq : ∏ x ∈ s, (l u z - l u x) = ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [hl, hl, ← Finset.sum_sub_distrib]
      simp [mul_sub]
    rw [heq] at hlt
    linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermCompletionEquiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace GermCompletionEquiv

theorem factorPow_evalₐ {R : Type} [CommRing R] (J : Ideal R) {k l : ℕ} (h : k ≤ l) (x : AdicCompletion J R) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J l x) = AdicCompletion.evalₐ J k x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk J h]

variable {σ : Type} [Fintype σ] (w : σ → ℂ)

theorem sub_polyGerm_C_mem (f : holGerms w) :
    f - polyGerm w (C (holGermValue w f)) ∈ holGermPointIdeal w := by
  rw [holGermPointIdeal, RingHom.mem_ker, map_sub, holGermValue_polyGerm, eval_C, sub_self]

theorem exists_sub_polyGerm_mem (hH : HolGermPointIdealSpan.Statement) (k : ℕ) (f : holGerms w) :
    ∃ q : MvPolynomial σ ℂ, f - polyGerm w q ∈ holGermPointIdeal w ^ k := by
  induction k generalizing f with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih f
    have hkey : holGermPointIdeal w ^ k =
        Ideal.span (polyGerm w '' ↑(Ideal.span (Set.range fun i : σ => (X i - C (w i) : MvPolynomial σ ℂ)) ^ k)) := by
      have e : Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i))) =
          (Ideal.span (Set.range fun i : σ => (X i - C (w i) : MvPolynomial σ ℂ))).map (polyGerm w) := by
        rw [Ideal.map_span, ← Set.range_comp]; rfl
      rw [hH σ w, e, ← Ideal.map_pow]; rfl
    have step : ∀ g ∈ holGermPointIdeal w ^ k,
        ∃ q' : MvPolynomial σ ℂ, g - polyGerm w q' ∈ holGermPointIdeal w ^ (k + 1) := by
      intro g hg
      rw [hkey] at hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, -, rfl⟩ := hx
        exact ⟨p, by simp⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ h1 h2 =>
        obtain ⟨q1, h1⟩ := h1
        obtain ⟨q2, h2⟩ := h2
        refine ⟨q1 + q2, ?_⟩
        rw [map_add]
        convert add_mem h1 h2 using 1
        ring
      | smul a x hx h =>
        obtain ⟨q1, h1⟩ := h
        have hx' : x ∈ holGermPointIdeal w ^ k := hkey ▸ hx
        refine ⟨C (holGermValue w a) * q1, ?_⟩
        have e : a • x - polyGerm w (C (holGermValue w a) * q1) =
            polyGerm w (C (holGermValue w a)) * (x - polyGerm w q1) +
              (a - polyGerm w (C (holGermValue w a))) * x := by
          rw [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ h1) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (sub_polyGerm_C_mem w a) hx'
    obtain ⟨q', hq'⟩ := step _ hq
    exact ⟨q + q', by rw [map_add, ← sub_sub]; exact hq'⟩

variable (I : Ideal (MvPolynomial σ ℂ))

theorem exists_sub_polyGerm_mem_of_mem_map (hH : HolGermPointIdealSpan.Statement) (k : ℕ) {x : holGerms w}
    (hx : x ∈ I.map (polyGerm w)) :
    ∃ i ∈ I, x - polyGerm w i ∈ holGermPointIdeal w ^ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, by simp⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨i1, hi1, h1⟩ := h1
    obtain ⟨i2, hi2, h2⟩ := h2
    refine ⟨i1 + i2, I.add_mem hi1 hi2, ?_⟩
    rw [map_add]
    convert add_mem h1 h2 using 1
    ring
  | smul a x _ h =>
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨q0, hq0⟩ := exists_sub_polyGerm_mem w hH k a
    refine ⟨q0 * i, I.mul_mem_left _ hi, ?_⟩
    have e : a • x - polyGerm w (q0 * i) =
        (a - polyGerm w q0) * x + polyGerm w q0 * (x - polyGerm w i) := by
      rw [smul_eq_mul, map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hq0) (Ideal.mul_mem_left _ _ h)

def phi : MvPolynomial σ ℂ ⧸ I →+* holGerms w ⧸ I.map (polyGerm w) :=
  Ideal.quotientMap _ (polyGerm w) Ideal.le_comap_map

theorem phi_mk (q : MvPolynomial σ ℂ) :
    phi w I (Ideal.Quotient.mk I q) = Ideal.Quotient.mk _ (polyGerm w q) :=
  Ideal.quotientMap_mk

theorem pow_le_comap (k : ℕ) :
    polyPointIdeal I w ^ k ≤ (germQuotPointIdeal I w ^ k).comap (phi w I) := by
  refine (Ideal.pow_right_mono ?_ k).trans (Ideal.le_comap_pow _ k)
  rw [polyPointIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro q hq
  rw [Ideal.mem_comap, RingHom.comp_apply, phi_mk, germQuotPointIdeal]
  exact Ideal.mem_map_of_mem _ (by rw [holGermPointIdeal, RingHom.mem_ker, holGermValue_polyGerm]; exact hq)

def psi (k : ℕ) : (MvPolynomial σ ℂ ⧸ I) ⧸ polyPointIdeal I w ^ k →+*
    (holGerms w ⧸ I.map (polyGerm w)) ⧸ germQuotPointIdeal I w ^ k :=
  Ideal.quotientMap _ (phi w I) (pow_le_comap w I k)

theorem psi_mk (k : ℕ) (q : MvPolynomial σ ℂ) :
    psi w I k (Ideal.Quotient.mk _ (Ideal.Quotient.mk I q)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (polyGerm w q)) := by
  rw [psi, Ideal.quotientMap_mk, phi_mk]

theorem psi_surjective (hH : HolGermPointIdealSpan.Statement) (k : ℕ) : Function.Surjective (psi w I k) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨q, hq⟩ := exists_sub_polyGerm_mem w hH k f
  refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk I q), ?_⟩
  rw [psi_mk, Ideal.Quotient.eq, germQuotPointIdeal, ← Ideal.map_pow, ← map_sub]
  exact Ideal.mem_map_of_mem _ (by rw [← neg_sub]; exact neg_mem hq)

theorem psi_injective (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) (k : ℕ) :
    Function.Injective (psi w I k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [psi_mk, Ideal.Quotient.eq_zero_iff_mem, germQuotPointIdeal, ← Ideal.map_pow,
    Ideal.mem_quotient_iff_mem_sup, Submodule.mem_sup] at hy
  obtain ⟨μ, hμ, ι, hι, he⟩ := hy
  obtain ⟨i, hi, hi'⟩ := exists_sub_polyGerm_mem_of_mem_map w I hH k hι
  have hqi : polyGerm w (q - i) ∈ holGermPointIdeal w ^ k := by
    rw [map_sub, ← he]
    convert add_mem hμ hi' using 1
    ring
  have hq := hP σ w k (q - i) hqi
  have e : q = (q - i) + i := by ring
  rw [Ideal.Quotient.eq_zero_iff_mem, polyPointIdeal, ← Ideal.map_pow, e, map_add,
    Ideal.Quotient.eq_zero_iff_mem.2 hi, add_zero]
  exact Ideal.mem_map_of_mem _ hq

theorem psi_factorPow {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h).comp (psi w I l) =
      (psi w I k).comp (Ideal.Quotient.factorPow (polyPointIdeal I w) h) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [RingHom.comp_apply, psi_mk, Ideal.Quotient.factor_mk]

def psiEquiv (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) (k : ℕ) :
    (MvPolynomial σ ℂ ⧸ I) ⧸ polyPointIdeal I w ^ k ≃+*
      (holGerms w ⧸ I.map (polyGerm w)) ⧸ germQuotPointIdeal I w ^ k :=
  RingEquiv.ofBijective (psi w I k) ⟨psi_injective w I hH hP k, psi_surjective w I hH k⟩

variable (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement)

theorem toCompl_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h).comp
        ((psi w I l).comp (AdicCompletion.evalₐ (polyPointIdeal I w) l).toRingHom) =
      (psi w I k).comp (AdicCompletion.evalₐ (polyPointIdeal I w) k).toRingHom := by
  refine RingHom.ext fun x => ?_
  change Ideal.Quotient.factorPow (germQuotPointIdeal I w) h
      (psi w I l (AdicCompletion.evalₐ (polyPointIdeal I w) l x)) =
    psi w I k (AdicCompletion.evalₐ (polyPointIdeal I w) k x)
  rw [← RingHom.comp_apply (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h), psi_factorPow,
    RingHom.comp_apply, factorPow_evalₐ]

def toCompl : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) →+*
    AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) :=
  AdicCompletion.liftRingHom (germQuotPointIdeal I w)
    (fun k => (psi w I k).comp (AdicCompletion.evalₐ (polyPointIdeal I w) k).toRingHom)
    (fun h => toCompl_compat w I h)

theorem evalₐ_toCompl (k : ℕ) (x : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I)) :
    AdicCompletion.evalₐ (germQuotPointIdeal I w) k (toCompl w I x) =
      psi w I k (AdicCompletion.evalₐ (polyPointIdeal I w) k x) := by
  rw [toCompl, AdicCompletion.evalₐ_liftRingHom _ _ (fun h => toCompl_compat w I h)]
  try rfl

theorem fromCompl_compat {k l : ℕ} (h : k ≤ l)
    (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    Ideal.Quotient.factorPow (polyPointIdeal I w) h
        ((psiEquiv w I hH hP l).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) l x)) =
      (psiEquiv w I hH hP k).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) k x) := by
  apply (psiEquiv w I hH hP k).injective
  rw [RingEquiv.apply_symm_apply]
  change psi w I k _ = _
  rw [← RingHom.comp_apply (psi w I k), ← psi_factorPow w I h, RingHom.comp_apply]
  change Ideal.Quotient.factorPow (germQuotPointIdeal I w) h
    ((psiEquiv w I hH hP l) ((psiEquiv w I hH hP l).symm _)) = _
  rw [RingEquiv.apply_symm_apply, factorPow_evalₐ]

def fromCompl : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) →+*
    AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) :=
  AdicCompletion.liftRingHom (polyPointIdeal I w)
    (fun k => (psiEquiv w I hH hP k).symm.toRingHom.comp
      (AdicCompletion.evalₐ (germQuotPointIdeal I w) k).toRingHom)
    (fun h => RingHom.ext fun x => fromCompl_compat w I hH hP h x)

theorem evalₐ_fromCompl (k : ℕ) (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    AdicCompletion.evalₐ (polyPointIdeal I w) k (fromCompl w I hH hP x) =
      (psiEquiv w I hH hP k).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) k x) := by
  rw [fromCompl, AdicCompletion.evalₐ_liftRingHom _ _
    (fun h => RingHom.ext fun x => fromCompl_compat w I hH hP h x)]
  try rfl

theorem fromCompl_toCompl (x : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I)) :
    fromCompl w I hH hP (toCompl w I x) = x :=
  AdicCompletion.ext_evalₐ fun k => by
    rw [evalₐ_fromCompl, evalₐ_toCompl]
    exact (psiEquiv w I hH hP k).symm_apply_apply _

theorem toCompl_fromCompl (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    toCompl w I (fromCompl w I hH hP x) = x :=
  AdicCompletion.ext_evalₐ fun k => by
    rw [evalₐ_toCompl, evalₐ_fromCompl]
    exact (psiEquiv w I hH hP k).apply_symm_apply _

end GermCompletionEquiv

open GermCompletionEquiv in

theorem GermCompletionEquiv.proof (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) :
    GermCompletionEquiv.Statement := by
  intro σ _ I w
  refine ⟨RingEquiv.ofRingHom (fromCompl w I hH hP) (toCompl w I)
    (RingHom.ext fun x => fromCompl_toCompl w I hH hP x) (RingHom.ext fun x => toCompl_fromCompl w I hH hP x),
    fun q => ?_⟩
  change fromCompl w I hH hP _ = _
  refine AdicCompletion.ext_evalₐ fun k => ?_
  rw [evalₐ_fromCompl, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, RingEquiv.symm_apply_eq]
  exact (psi_mk w I k q).symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchSheetAE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def BranchSheetAE.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ᵐ t ∂(volume.restrict (Metric.ball (0 : Fin d → ℂ) γ.radius)), ∃ s, IsSheetAt J A (γ.toFun t) s

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntSumOffHyperplane
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def ChartIntSumOffHyperplane.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ)
    (m : ℕ) (f : (Fin n → ℂ) → ℝ) (F : Fin m → (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J →
    (∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, F b x) →
    (∀ b, Integrable (chartDens J A (F b) φ)) →
      chartInt J A f φ = ∑ b, chartInt J A (F b) φ

end

end GroundTheory.Heights₂.Heights
end

