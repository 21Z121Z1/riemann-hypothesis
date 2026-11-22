import Mathlib
import GroundTheory.AutomorphicForms.Bundle0005
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.Bundle0009

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinProducts
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

set_option linter.unusedSectionVars false

theorem integral_fin_succ_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {F : (Fin (d + 1) → ℝ) → E} (hF : Integrable F) :
    ∫ t, F t = ∫ s, ∫ t', F (Fin.cons s t') := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have h1 := hmp.symm.integral_comp' F
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← h1]
  refine (integral_prod _ hint).trans ?_
  congr 1; funext s; congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]
  rfl

theorem contDiff_cons_kernel {d : ℕ} {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a)
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) :=
  (ha.comp (contDiff_apply ℝ ℝ 0)).mul
    (hK.comp (contDiff_pi.2 fun j => contDiff_apply ℝ ℝ j.succ))

theorem tsupport_cons_kernel {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ}
    (has : tsupport a ⊆ Icc (-ε) ε)
    (hKs : tsupport K ⊆ Metric.closedBall 0 ε) :
    tsupport (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) ⊆ Metric.closedBall 0 ε := by
  intro t ht
  have h1 := tsupport_mul_subset_left ht
  have h2 := tsupport_mul_subset_right ht
  have h1' : t 0 ∈ tsupport a :=
    tsupport_comp_subset_preimage a (f := fun t : Fin (d + 1) → ℝ => t 0) (continuous_apply 0) h1
  have h2' : Fin.tail t ∈ tsupport K :=
    tsupport_comp_subset_preimage K (f := fun t : Fin (d + 1) → ℝ => Fin.tail t)
      (continuous_pi fun j => continuous_apply j.succ) h2
  have ha' := has h1'
  have hK' := hKs h2'
  rw [mem_closedBall_zero_iff] at hK' ⊢
  refine (pi_norm_le_iff_of_nonneg hε).2 fun j => ?_
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Real.norm_eq_abs, abs_le]; exact ha'
  · exact (norm_le_pi_norm (Fin.tail t) j).trans hK'

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def revProdExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) : G :=
  (List.ofFn fun i => h.expG (t i • X i)).reverse.prod

theorem revProdExp_zero (X : Fin 0 → 𝔤) (t : Fin 0 → ℝ) : h.revProdExp X t = 1 := by
  simp [revProdExp]

theorem revProdExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.revProdExp X t = h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) := by
  simp [revProdExp, List.ofFn_succ, Fin.tail]

theorem continuous_revProdExp : ∀ {d : ℕ} (X : Fin d → 𝔤), Continuous (h.revProdExp X)
  | 0, X => by
    have : h.revProdExp X = fun _ => 1 := funext (h.revProdExp_zero X)
    rw [this]; exact continuous_const
  | d + 1, X => by
    have : h.revProdExp X =
        fun t => h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) :=
      funext (h.revProdExp_succ X)
    rw [this]
    exact ((continuous_revProdExp (Fin.tail X)).comp
      (continuous_pi fun j => continuous_apply j.succ)).mul
      (h.continuous_expG.comp ((continuous_apply 0).smul continuous_const))

theorem revProdExp_inv {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (h.revProdExp X t)⁻¹ = h.prodExp X (-t) := by
  rw [revProdExp, List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, prodExp,
    List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  simp [neg_smul, h.expG_neg]

theorem integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x) =
      ∫ s, ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x))) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp ((h.continuous_revProdExp X).mul continuous_const))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, h.revProdExp_succ, mul_assoc]

theorem integrable_integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x)))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      (((h.continuous_revProdExp (Fin.tail X)).comp continuous_snd).mul
        ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_const))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left

theorem sum_integral_cons_kernel {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (h.revProdExp (Fin.tail X) t' * y)) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (h.revProdExp X t * x) =
      ∫ s, a s * f₁ (h.expG (s • X 0) * x) := by
  rw [Finset.sum_congr rfl fun i _ => h.integral_cons_kernel X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      h.integrable_integral_cons_kernel X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinSeries
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contDiff_iteratedDeriv_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) :
    ∀ {Ψ : E × ℝ → F}, ContDiff ℝ ∞ Ψ → ∀ s : ℝ,
      ContDiff ℝ ∞ (fun Y : E => iteratedDeriv p (fun t : ℝ => Ψ (Y, t)) s) := by
  induction p with
  | zero =>
    intro Ψ hΨ s
    simp only [iteratedDeriv_zero]
    exact hΨ.comp (contDiff_id.prodMk contDiff_const)
  | succ p ih =>
    intro Ψ hΨ s
    have hd : ∀ Y : E, deriv (fun t : ℝ => Ψ (Y, t)) = fun t => fderiv ℝ Ψ (Y, t) (0, 1) := by
      intro Y; funext t
      have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (Y, t)) (Y, t) :=
        (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => ((Y, t) : E × ℝ)) (0, 1) t :=
        (hasDerivAt_const t Y).prodMk (hasDerivAt_id t)
      exact (h1.comp_hasDerivAt t h2).deriv
    have hΨ' : ContDiff ℝ ∞ (fun q : E × ℝ => fderiv ℝ Ψ q (0, 1)) :=
      (hΨ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have e : (fun Y : E => iteratedDeriv (p + 1) (fun t : ℝ => Ψ (Y, t)) s) =
        fun Y => iteratedDeriv p (fun t : ℝ => fderiv ℝ Ψ (Y, t) (0, 1)) s := by
      funext Y; rw [iteratedDeriv_succ', hd Y]
    rw [e]; exact ih hΨ' s

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def dirDeriv (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) : ℂ :=
  iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) 0

theorem iteratedDeriv_comp_expG_mul (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) (s : ℝ) :
    iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) s =
      h.dirDeriv X p f (h.expG (s • X) * x) := by
  have e := congrFun (iteratedDeriv_comp_add_const p (fun t : ℝ => f (h.expG (t • X) * x)) s) 0
  simp only [zero_add] at e
  rw [← e, dirDeriv]
  congr 1
  funext u
  rw [h.expG_add_smul, mul_assoc]

theorem contMDiff_expG_smul_mul (X : 𝔤) (x : G) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔤) ∞ (fun t : ℝ => h.expG (t • X) * x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  exact (h.contMDiff_expG_comp (contDiff_id.smul contDiff_const)).mul contMDiff_const

theorem contDiff_comp_expG_smul_mul {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (x : G) :
    ContDiff ℝ ∞ (fun t : ℝ => f (h.expG (t • X) * x)) := by
  let := h.chartedSpace
  exact (hf.comp (h.contMDiff_expG_smul_mul X x)).contDiff

theorem contDiff_comp_expG_smul_mul_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (g : G) :
    ContDiff ℝ ∞ (fun q : 𝔤 × ℝ => f (h.expG (q.2 • X) * (g * h.expG q.1))) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × ℝ) 𝓘(ℝ, 𝔤) ∞
      (fun q : 𝔤 × ℝ => h.expG (q.2 • X) * (g * h.expG q.1)) :=
    (h.contMDiff_expG_comp (contDiff_snd.smul contDiff_const)).mul
      (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst))
  exact (hf.comp hm).contDiff

theorem dirDeriv_eq_zero_of_notMem {f : G → ℂ} (X : 𝔤) (p : ℕ) {x : G}
    (hx : x ∉ tsupport f) : h.dirDeriv X p f x = 0 := by
  have hc : Continuous (fun t : ℝ => h.expG (t • X) * x) :=
    (h.continuous_expG.comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h.expG ((0 : ℝ) • X) * x = x := by
    simp only [zero_smul]; rw [h.expG_zero, one_mul]
  have hev : (fun t : ℝ => f (h.expG (t • X) * x)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have := hc.continuousAt (x := 0)
    rw [ContinuousAt] at this
    simp only [h0] at this
    exact this.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)
  rw [dirDeriv, hev.iteratedDeriv_eq]
  simp

theorem contDiff_dirDeriv_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (p : ℕ) (g : G) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => h.dirDeriv X p f (g * h.expG Y)) :=
  contDiff_iteratedDeriv_snd p (h.contDiff_comp_expG_smul_mul_mul_expG hf X g) 0

theorem mem_chart_source_self (g : G) : g ∈ (h.chart g).source := by
  let := h.chartedSpace
  exact mem_chart_source 𝔤 g

theorem chart_symm_chart {g x : G} (hx : x ∈ (h.chart g).source) :
    g * h.expG (h.chart g x) = x :=
  (h.chart g).left_inv hx

theorem exists_bound_dirDeriv {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) :
    ∃ M : ℕ → ℝ, (∀ p x, ‖h.dirDeriv X p f x‖ ≤ M p) ∧
      ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) →
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞
          (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x)) ∧
        HasCompactSupport (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  let U : G → Set G := fun g => (h.chart g).source ∩ (h.chart g) ⁻¹' Metric.ball 0 1
  have hU : ∀ g, IsOpen (U g) := fun g =>
    (h.chart g).isOpen_inter_preimage Metric.isOpen_ball
  have hgU : ∀ g, g ∈ U g := fun g =>
    ⟨h.mem_chart_source_self g, by
      show h.chart g g ∈ Metric.ball 0 1
      rw [h.chart_self]; exact Metric.mem_ball_self one_pos⟩
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover U (fun g _ => (hU g).mem_nhds (hgU g))
  let β : ContDiffBump (0 : 𝔤) := ⟨1, 2, one_pos, one_lt_two⟩
  let Φ : G → ℕ → 𝔤 → ℂ := fun g p Y => (β Y : ℂ) * h.dirDeriv X p f (g * h.expG Y)
  have hΦ : ∀ g p, ContDiff ℝ ∞ (Φ g p) := fun g p =>
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul (h.contDiff_dirDeriv_mul_expG hf X p g)
  have hΦc : ∀ g p, HasCompactSupport (Φ g p) := fun g p =>
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hS : ∀ g k p, ∃ C, ∀ Y, ‖iteratedFDeriv ℝ k (Φ g p) Y‖ ≤ C := fun g k p =>
    ((hΦ g p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((hΦc g p).iteratedFDeriv k)
  choose S hS using hS
  have hS0 : ∀ g k p, 0 ≤ S g k p := fun g k p => (norm_nonneg _).trans (hS g k p 0)
  let M : ℕ → ℝ := fun p => ∑ g ∈ t, ∑ k ∈ Finset.range (p + 1), S g k p
  have hM0 : ∀ p, 0 ≤ M p := fun p =>
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p
  have hSM : ∀ p, ∀ g ∈ t, ∀ k ≤ p, S g k p ≤ M p := by
    intro p g hg k hk
    calc S g k p ≤ ∑ k ∈ Finset.range (p + 1), S g k p :=
          Finset.single_le_sum (fun k _ => hS0 g k p) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
      _ ≤ M p := Finset.single_le_sum (f := fun g => ∑ k ∈ Finset.range (p + 1), S g k p)
          (fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p) hg

  have hloc : ∀ g p x, x ∈ U g → h.dirDeriv X p f x = Φ g p (h.chart g x) := by
    intro g p x hx
    have hb : β (h.chart g x) = 1 :=
      β.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.2)
    simp only [Φ, hb, Complex.ofReal_one, one_mul, h.chart_symm_chart hx.1]
  have hzero : ∀ p x, x ∉ K → h.dirDeriv X p f x = 0 := fun p x hx =>
    h.dirDeriv_eq_zero_of_notMem X p hx
  refine ⟨M, ?_, ?_⟩
  · intro p x
    by_cases hx : x ∈ K
    · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
      rw [hloc g p x hxg]
      calc ‖Φ g p (h.chart g x)‖ = ‖iteratedFDeriv ℝ 0 (Φ g p) (h.chart g x)‖ := by
            rw [norm_iteratedFDeriv_zero]
        _ ≤ S g 0 p := hS g 0 p _
        _ ≤ M p := hSM p g hg 0 (Nat.zero_le p)
    · rw [hzero p x hx, norm_zero]; exact hM0 p
  intro c hc

  let F : G → 𝔤 → ℂ := fun g Y => ∑' p, (c p) • Φ g p Y
  have hF : ∀ g ∈ t, ContDiff ℝ ∞ (F g) := by
    intro g hg
    refine contDiff_tsum (N := ⊤) (v := fun k p => |c p| * S g k p)
      (fun p => (hΦ g p).const_smul (c p)) ?_ ?_
    · intro k _
      rw [← summable_nat_add_iff k]
      refine Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (hS0 g k _))
        (fun p => mul_le_mul_of_nonneg_left (hSM (p + k) g hg k (Nat.le_add_left k p))
          (abs_nonneg _)) ?_
      exact (summable_nat_add_iff k).2 hc
    · intro k p Y _
      rw [iteratedFDeriv_const_smul_apply' ((hΦ g p).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hS g k p Y) (abs_nonneg _)
  have hsupp : ∀ x, x ∉ K → ∑' p, (c p : ℂ) * h.dirDeriv X p f x = 0 := by
    intro x hx; simp [hzero _ x hx]
  refine ⟨?_, HasCompactSupport.intro hK hsupp⟩
  intro x
  by_cases hx : x ∈ K
  · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
    have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x]
        fun x => F g (chartAt 𝔤 g x) := by
      filter_upwards [(hU g).mem_nhds hxg] with x' hx'
      show _ = F g (h.chart g x')
      simp only [F, hloc g _ x' hx', Complex.real_smul]
    have hch : ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ (chartAt 𝔤 g) x := by
      have := contMDiffAt_extChartAt' (I := 𝓘(ℝ, 𝔤)) (n := ∞) (x := g) hxg.1
      simpa [extChartAt] using this
    exact (((hF g hg).contMDiff.contMDiffAt).comp x hch).congr_of_eventuallyEq hev
  · have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with x' hx'
      exact hsupp x' hx'
    exact contMDiffAt_const.congr_of_eventuallyEq hev

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.TraceStrongLimit
section
namespace GroundTheory.Automorphic

open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section FinProj

variable {ι : Type*} [Fintype ι]

def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)

theorem finProj_apply (u : ι → H) (x : H) : finProj u x = ∑ i, ⟪u i, x⟫_ℂ • u i := by
  simp [finProj, rankOne_apply]

theorem finProj_mem_span (u : ι → H) (x : H) : finProj u x ∈ Submodule.span ℂ (Set.range u) := by
  rw [finProj_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable {u : ι → H}

theorem inner_finProj_right (hu : Orthonormal ℂ u) (x : H) (j : ι) :
    ⟪u j, finProj u x⟫_ℂ = ⟪u j, x⟫_ℂ := by
  rw [finProj_apply]
  exact hu.inner_right_fintype _ j

theorem inner_sub_finProj_eq_zero (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ⟪g, x - finProj u x⟫_ℂ = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hg
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, inner_sub_right, inner_finProj_right hu, sub_self, mul_zero]

theorem norm_sub_finProj_le (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ‖x - finProj u x‖ ≤ ‖x - g‖ := by
  have hmem : finProj u x - g ∈ Submodule.span ℂ (Set.range u) :=
    Submodule.sub_mem _ (finProj_mem_span u x) hg
  have h0 : ⟪x - finProj u x, finProj u x - g⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_finProj_eq_zero hu x hmem, map_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_sub_cancel] at h
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

theorem norm_sub_finProj_le_norm (hu : Orthonormal ℂ u) (x : H) : ‖x - finProj u x‖ ≤ ‖x‖ := by
  simpa using norm_sub_finProj_le hu x (Submodule.zero_mem _)

theorem hasSum_inner_comp_finProj (u : ι → H) (S : H →L[ℂ] H) {κ : Type*}
    (b : HilbertBasis κ ℂ H) :
    HasSum (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) (∑ i, ⟪u i, S (u i)⟫_ℂ) := by
  have h : (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) =
      fun β => ∑ i, ⟪u i, b β⟫_ℂ * ⟪b β, S (u i)⟫_ℂ := by
    ext β
    rw [finProj_apply, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  rw [h]
  exact hasSum_sum fun i _ => b.hasSum_inner_mul_inner (u i) (S (u i))

theorem trace_comp_finProj [CompleteSpace H] (u : ι → H) (S : H →L[ℂ] H) :
    trace (S.comp (finProj u)) = ∑ i, ⟪u i, S (u i)⟫_ℂ :=
  (hasSum_inner_comp_finProj u S (stdHilbertBasis ℂ H)).tsum_eq

end FinProj

section Limits

variable [CompleteSpace H]

theorem tendsto_trace_comp {α : Type*} {F : Filter α} {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (P : α → H →L[ℂ] H) (hP1 : ∀ a x, ‖x - P a x‖ ≤ ‖x‖)
    (hP : ∀ x, Tendsto (fun a => P a x) F (𝓝 x)) :
    Tendsto (fun a => trace (T.comp (P a))) F (𝓝 (trace T)) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  set Q : α → H →L[ℂ] H := fun a => ContinuousLinearMap.id ℂ H - P a with hQ

  have hdiff : ∀ a, trace (A.comp B) - trace ((A.comp B).comp (P a)) =
      trace (((Q a).comp A).comp B) := by
    intro a
    have hsplit : A.comp B = (A.comp B).comp (P a) + (A.comp B).comp (Q a) := by
      rw [← comp_add]; simp [hQ]
    have h1 : trace (A.comp B) =
        trace ((A.comp B).comp (P a)) + trace ((A.comp B).comp (Q a)) := by
      conv_lhs => rw [hsplit]
      exact trace_add (hT.comp_right _) (hT.comp_right _)
    rw [h1, add_sub_cancel_left, ← trace_comp_comm hT (Q a), comp_assoc]

  let b := stdHilbertBasis ℂ H
  have hQA : ∀ a, IsHilbertSchmidt ((Q a).comp A) := fun a => hA.comp_left _
  have hsq : ∀ a, hsNorm ((Q a).comp A) ^ 2 = ∑' e, ‖A (b e) - P a (A (b e))‖ ^ 2 := by
    intro a
    rw [((hQA a).hasSum_norm_sq b).tsum_eq.symm]
    rfl
  have hlim2 : Tendsto (fun a => hsNorm ((Q a).comp A) ^ 2) F (𝓝 0) := by
    simp_rw [hsq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := F)
      (f := fun a e => ‖A (b e) - P a (A (b e))‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun e => ‖A (b e)‖ ^ 2) (hA.hasSum_norm_sq b).summable ?_ ?_
    · simpa using h
    · intro e
      have := ((tendsto_const_nhds (x := A (b e))).sub (hP (A (b e)))).norm.pow 2
      simpa using this
    · refine Eventually.of_forall fun a e => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP1 a _) 2
  have hlim : Tendsto (fun a => hsNorm ((Q a).comp A)) F (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim2
    simp only [Real.sqrt_zero] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (hsNorm_nonneg _)

  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ a, ‖trace ((A.comp B).comp (P a)) - trace (A.comp B)‖ ≤
      hsNorm ((Q a).comp A) * hsNorm B := by
    intro a
    rw [norm_sub_rev, hdiff a]
    have hfin : traceNorm (((Q a).comp A).comp B) ≠ ∞ := (isTraceClass_comp (hQA a) hB).ne
    have h1 : ‖trace (((Q a).comp A).comp B)‖ ≤ (traceNorm (((Q a).comp A).comp B)).toReal := by
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hfin (enorm_trace_le _)
    exact h1.trans (traceNorm_comp_le (hQA a) hB)
  refine squeeze_zero (fun a => norm_nonneg _) hbound ?_
  simpa using hlim.mul_const (hsNorm B)

end Limits

end

end GroundTheory.Automorphic
end

