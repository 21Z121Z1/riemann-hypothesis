import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0149
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCChain
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem tsum_mix {ι W : Type} (Wd : Finset W) (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hms : Summable m)
    (hM : 0 < ∑' i, m i) (q : ι → W → ℝ) (hq : ∀ i, TB.IsProb Wd (q i)) :
    ∃ θ : W → ℝ, TB.IsProb Wd θ ∧ ∀ N : W → ℝ,
      Summable (fun i => m i * ∑ u ∈ Wd, q i u * N u) ∧
      ∑' i, m i * ∑ u ∈ Wd, q i u * N u = (∑' i, m i) * ∑ u ∈ Wd, θ u * N u := by
  set M := ∑' i, m i with hMdef
  have hq1 : ∀ i u, q i u ≤ 1 := by
    intro i u
    by_cases hu : u ∈ Wd
    · rw [← (hq i).2.2]
      exact Finset.single_le_sum (fun a _ => (hq i).1 a) hu
    · rw [(hq i).2.1 u hu]
      exact zero_le_one
  have hsu : ∀ u, Summable (fun i => m i * q i u) := fun u =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm0 i) ((hq i).1 u))
      (fun i => mul_le_of_le_one_right (hm0 i) (hq1 i u)) hms
  refine ⟨fun u => (∑' i, m i * q i u) / M, ⟨fun u => div_nonneg (tsum_nonneg fun i =>
    mul_nonneg (hm0 i) ((hq i).1 u)) hM.le, fun u hu => ?_, ?_⟩, fun N => ⟨?_, ?_⟩⟩
  · simp [(hq _).2.1 u hu]
  · rw [← Finset.sum_div, div_eq_one_iff_eq hM.ne', ← Summable.tsum_finsetSum (fun u _ => hsu u)]
    refine tsum_congr fun i => ?_
    rw [← Finset.mul_sum, (hq i).2.2, mul_one]
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    exact summable_sum fun u _ => (hsu u).mul_right (N u)
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Summable.tsum_finsetSum (fun u _ => (hsu u).mul_right (N u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tsum_mul_right]
    field_simp

theorem mL_pat {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L σ * ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K = ∏ v ∈ crystallineComparison.pat L σ, L v ^ K := by
  have h1 : ∀ v ∈ crystallineComparison.pat L σ, crystallineComparison.mfac K (L v) ‖σ v‖ * ‖σ v‖ ^ K = L v ^ K := by
    intro v hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have ha : 0 < ‖σ v‖ := lt_of_le_of_lt (hL v) hv
    have hle : (L v / ‖σ v‖) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg (hL v) ha.le) ((div_le_one ha).mpr hv.le)
    unfold crystallineComparison.mfac
    rw [if_neg ha.ne', min_eq_right hle, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ ha.ne'
  have h2 : ∀ v ∈ (Finset.univ : Finset (Fin f)), v ∉ crystallineComparison.pat L σ → crystallineComparison.mfac K (L v) ‖σ v‖ = 1 := by
    intro v _ hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rfl
    · have ha : 0 < ‖σ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact min_eq_left (one_le_pow₀ ((one_le_div ha).mpr hv))
  unfold crystallineComparison.mL
  rw [← Finset.prod_subset (Finset.subset_univ _) h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl h1

theorem bound_mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) (X Y : ℝ)
    (h : (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X ≤ (∏ v ∈ crystallineComparison.pat L σ, L v ^ K) * Y) : X ≤ crystallineComparison.mL K L σ * Y := by
  have hP : 0 < ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K := by
    refine Finset.prod_pos fun v hv => pow_pos ?_ _
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact lt_of_le_of_lt (hL v) hv
  rw [← mL_pat K L hL σ] at h
  refine le_of_mul_le_mul_left ?_ hP
  calc (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X
      ≤ crystallineComparison.mL K L σ * (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * Y := h
    _ = (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * (crystallineComparison.mL K L σ * Y) := by ring

theorem mL_nonneg {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) : 0 ≤ crystallineComparison.mL K L σ := Finset.prod_nonneg fun v _ => by
    unfold crystallineComparison.mfac
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (pow_nonneg (div_nonneg (hL v) (norm_nonneg _)) _)

theorem mL_zero {f : ℕ} (K : ℕ) (L : Fin f → ℝ) : crystallineComparison.mL K L 0 = 1 := by
  unfold crystallineComparison.mL crystallineComparison.mfac
  simp

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem prod_gN (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (p q : Fin S.f → C.LPt) :
    ∏ v, KB.gN S v ε i (w.1 v) (p v) (q v) =
      (∏ v, S.gramLoc v ε i (w.1 v) (p v) (q v)) / (C.Word.size S.P w.1 : ℂ) := by
  unfold KB.gN C.Word.size
  rw [Finset.prod_div_distrib]
  congr 1
  push_cast
  rfl

theorem nstV_eq (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : Fin S.f → ℂ) :
    KB.NstV S ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' *
      ∏ v, KB.gN S v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)]) (C.loc (S.σ v) h' ++ [(s, t' v)]) := by
  unfold KB.NstV
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have e := prod_gN S ε i w (fun v => C.loc (S.σ v) h ++ [(s, t v)]) (fun v => C.loc (S.σ v) h' ++ [(s, t' v)])
  rw [e, mul_div_assoc]

end setting

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QQMemAdjAlgCpt
section
open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def CptAt (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  ∃ K : Set (Mx k r), IsCompact K ∧ K ⊆ {g | 0 < GGl k r z z' g} ∧
    ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0

variable (k r z z' π π') in

def cptSub : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, CptAt Φ c}
  zero_mem' := fun c _ => ⟨∅, isCompact_empty, Set.empty_subset _, fun g _ _ => rfl⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨K1, h1c, h1G, h10⟩ := hΦ c hc
    obtain ⟨K2, h2c, h2G, h20⟩ := hΨ c hc
    refine ⟨K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G, fun g hg hgK => ?_⟩
    show (Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
    rw [h10 g hg (fun h => hgK (Or.inl h)), h20 g hg (fun h => hgK (Or.inr h)), add_zero]
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
    refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
    show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
    rw [hK0 g hg hgK, smul_zero]

theorem intOn_cpt (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    IntOn μ (cptSub k r z z' π π') := by
  intro c hc Φ hΦ Ψ _
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ =>
    int_cpt_gen μ hμ Φ Ψ c _ K hKc hKG hc _ (Or.inr rfl) hK0

theorem smoothLev_slice (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (hc : c ∈ OmX r) (D : Set (Mx k r))
    (hD : D ⊆ {g | 0 < GGl k r z z' g}) :
    SmoothLev k r (Fin.last r) D (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  intro g₀ hg₀
  obtain ⟨hg₀G, hg₀D⟩ := hg₀
  obtain ⟨-, hs, -⟩ := Φ.2
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g₀)
    (show ((c, g₀) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z' from ⟨hc, hg₀G, hD hg₀D⟩)
  have hcont : Continuous fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r) := by fun_prop
  have hsm : ContDiff ℝ ∞ fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r) := by fun_prop
  refine ⟨(fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r)) ⁻¹' U, fun g => F (c, g), hU.preimage hcont, hxU,
    hF.comp hsm.contDiffOn (fun g hg => hg), ?_⟩
  intro g hg hgG
  exact hΦ (c, g) hg hgG

theorem fn_pres_cpt (X : ActualOps k r z z' π π') (j : Fin 6) :
    ∀ Φ ∈ cptSub k r z z' π π', X.fn j Φ ∈ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
  by_cases hx : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · have h := X.fn_apply j Φ (c, g) hx
    dsimp only at h
    rw [h, hK0 g hg hgK, smul_zero]
  · obtain ⟨h0, -, -⟩ := (X.fn j Φ).2
    exact h0 (c, g) hx

theorem t_pres_cpt (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) :
    ∀ Φ ∈ cptSub k r z z' π π', X.t Y a b Φ ∈ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
  by_cases hd : (c, g) ∈ DomR k r z z'
  · have e := X.t_apply Y a b Φ (c, g) hd
    simp only at e
    rw [e]
    set D : Set (Mx k r) := {g | 0 < GGl k r z z' g} \ K with hDdef
    have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).sdiff hKc.isClosed
    have hDG : D ⊆ {g | 0 < GGl k r z z' g} := Set.sdiff_subset
    have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hgK⟩
    have hS1 := smoothLev_slice Φ c hc D hDG
    have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
      intro g₀ hg₀
      exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
    have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
    have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
    have h0 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
      have h := hL0.1
      simp only [smul_zero, add_zero, one_smul] at h
      have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
        rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    have hloc := hL.2 (fun x hx => hK0 x hx.1 hx.2.2)
    rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h0]
  · exact radSp_zero_off (X.t Y a b Φ) (x := (c, g)) hd

end Cpt

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem QQ_mem_adjAlg_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ adjAlg μ (cptSub P.k P.r z z' π π') (intOn_cpt μ hμ) := by
  refine ⟨t_pres_cpt X Y a b, t_pres_cpt X (star Y) b a, fun c hc Φ hΦ Ψ hΨ => ?_⟩
  show pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c
  obtain ⟨K1, h1c, h1G, h10⟩ := hΦ c hc
  obtain ⟨K2, h2c, h2G, h20⟩ := hΨ c hc
  exact pairAt_t_adj_cpt' P z z' π π' hP X μ hμ Φ Ψ c hc
    ⟨K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G,
      fun g hg hgK => ⟨h10 g hg (fun h => hgK (Or.inl h)), h20 g hg (fun h => hgK (Or.inr h))⟩⟩ Y a b

theorem adjTop_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (hK : K (Fin.last P.r) ≤ cptSub P.k P.r z z' π π') :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  exact adjTop_of_tAdj (S := S) P z z' π π' X μ L st K l0 hD (cptSub P.k P.r z z' π π') (intOn_cpt μ hD.2.1) hK
    (fn_pres_cpt X) (fun Y _ a b => QQ_mem_adjAlg_cpt P z z' π π' hD.1 X μ hD.2.1 Y a b)

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem lintegral_zWeight_closedBall_ne_infty (k : ℕ) (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hb : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    unfold B2.zWeight
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      have h1 : Complex.normSq ζ ≤ R ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        have := mem_closedBall_zero_iff.mp hζ
        have h0 : 0 ≤ ‖ζ‖ := norm_nonneg _
        nlinarith
      have h2 : -(T * T') ≤ |T * T'| := neg_le_abs _
      linarith
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono measurable_const (fun ζ hζ => hb ζ hζ)
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem ph_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k n z z' π π')
        (c : Fin n → ℂ) (c₀ : Fin ρ → ℂ),
        P5.ph L st μ ⟨0, by omega⟩ w x y c t =
          ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
            P5.RRform Ls sts μs 0 w (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a))
              (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) y a)) c₀ := by
  subst hn
  have ez : z = liftVec k 1 ρ zs := by
    rw [hz]; funext i; simp [D.castV]
  have ez' : z' = liftVec k 1 ρ zs' := by
    rw [hz']; funext i; simp [D.castV]
  have eπ : πs = fun y => π (ιLev k 1 ρ y) := by
    funext y; rw [hπ y]; congr 1
  have eπ' : πs' = fun y => π' (ιLev k 1 ρ y) := by
    funext y; rw [hπ' y]; congr 1
  subst ez ez' eπ eπ'
  have hmap : μs.map (B2.levM k ρ) = μ := by
    refine map_levM_eq hμ hμs (fun ζ => ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ))
      (fun R => lintegral_zWeight_closedBall_ne_infty k _ _ R) ?_ hlaws
    intro ψ hψ
    rw [hlaw ψ hψ, tz_iota, tz_iota]
  refine ⟨trL ht zs zs' π π', ?_, ?_⟩
  · intro Φ c g
    (try simp [D.castM]) <;> rfl
  · intro S _ _ w x y c c₀
    exact ph_tr ht hzs hzs' hL hLs hst hsts hmap w x y c c₀

def RadTransportPl : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j + 1 ≤ P.r)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j))) (L) (st)
    (Xs : Q.ActualOps (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z'
      (p.T.bs (j + 1)).π (p.T.bs (j + 1)).π')
    (μs : Measure (Mt P.k (P.r - (j + 1)))) (Ls) (sts),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    KB.ZetaNorm (p.T.bs j) μ →
    P5.IsData (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
      (p.T.bs (j + 1)).π' Xs μs Ls sts p.l0 →
    KB.ZetaNorm (p.T.bs (j + 1)) μs →
    ∀ t : ℂ, t ≠ 0 →
      ∃ T : Q.RadSp P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' →ₗ[ℂ]
          Q.RadSp P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
            (p.T.bs (j + 1)).π',
        (∀ Φ c g, (T Φ : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c g =
          (Φ : Q.Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast (by omega) l))
            (D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g))) ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S))
          (x y : Wd.Ix S → Q.RadSp P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
          (c : Fin (P.r - j) → ℂ) (c₀ : Fin (P.r - (j + 1)) → ℂ),
          P5.ph L st μ (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w x y c t =
            ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
              P5.RRform Ls sts μs 0 w
                (fun a => T (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w) x a))
                (fun a => T (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w) y a))
                c₀

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem radial_transport_plus : Formalism.FourierDecayAlt.P.PBH.RadTransportPl := by
  intro Wp Wq _ _ _ _ _ _ P p j hj X μ L st Xs μs Ls sts hD hZ hDs hZs t ht
  exact ph_cast (n := P.r - j) (ρ := P.r - (j + 1)) (by omega)
    (levTower_bs_z_eq_castV_liftVec p.T j hj) (levTower_bs_z'_eq_castV_liftVec p.T j hj) hDs.1.2.1 hDs.1.2.2.1
    (tower_π p.T j hj) (tower_π' p.T j hj) X Xs L st Ls sts _ μ μs
    hD.2.2.1 hDs.2.2.1 hD.2.2.2.1 (fun Y => (hDs.2.2.2.1 Y).trans rfl) hD.2.1 hDs.2.1 hZ.2 hZs.2 t ht

end Formalism.FourierDecayAlt.P
end
end

