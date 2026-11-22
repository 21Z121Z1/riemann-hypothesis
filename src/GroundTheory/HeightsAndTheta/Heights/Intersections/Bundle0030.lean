import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pot_cons {e : ℕ} (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem forall_cons {m : ℕ} {p : HermLine ι → Prop} {M : HermLine ι} {N : Fin m → HermLine ι}
    (hM : p M) (hN : ∀ j, p (N j)) : ∀ j, p ((Fin.cons M N : Fin (m + 1) → HermLine ι) j) :=
  fun j => Fin.cases (by simpa using hM) (fun i => by simpa using hN i) j

theorem ptsIntegral_neg {e : ℕ} (Q : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (f : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral Q φ (fun z => -f z) = -ptsIntegral Q φ f := by
  have key : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity Q Ψ φ (fun z => -f z) y w = -sheetDensity Q Ψ φ f y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · simp

theorem log_h_eq_neg_logNorm_one (D : HermLine ι) :
    (fun z => Real.log (D.h z)) = fun z => -logNorm D 1 z := by
  funext z
  simp [logNorm, Real.log_inv]

theorem isSectionOn_one {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) {D : HermLine ι}
    (hDa : D.a = 0) : IsSectionOn Q D 1 := by
  refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
    fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem ptsIntegral_add_first_log (hAdd : PtsAddFirst.Statement) {Q : Ideal (MRing ι)} {e : ℕ}
    {L : Fin e → HermLine ι} {M N D : HermLine ι} (hQ : IsArithVar Q (e + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) (hD : IsSmoothHerm D)
    (hDa : D.a = 0) :
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (fun z => Real.log (D.h z)) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (fun z => Real.log (D.h z)) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (fun z => Real.log (D.h z)) := by
  rw [log_h_eq_neg_logNorm_one D, ptsIntegral_neg, ptsIntegral_neg, ptsIntegral_neg,
    hAdd K ι Q e L M N D 1 hQ hL hM hN hD (isSectionOn_one hQ hDa)]
  ring

theorem tendsto_finsum_of_finite {α : Type*} {p : α → Prop} (hp : {W | p W}.Finite) {f : ℝ → α → ℝ}
    {g : α → ℝ} {l : Filter ℝ} (h : ∀ W, p W → Tendsto (fun ε => f ε W) l (𝓝 (g W))) :
    Tendsto (fun ε => ∑ᶠ (W) (_ : p W), f ε W) l (𝓝 (∑ᶠ (W) (_ : p W), g W)) := by
  have e : ∀ u : α → ℝ, ∑ᶠ (W) (_ : p W), u W = ∑ W ∈ hp.toFinset, u W :=
    fun u => finsum_mem_eq_finite_toFinset_sum u hp
  have e1 : (fun ε => ∑ᶠ (W) (_ : p W), f ε W) = fun ε => ∑ W ∈ hp.toFinset, f ε W :=
    funext fun ε => e (f ε)
  rw [e1, e g]
  exact tendsto_finsetSum _ fun W hW => h W (hp.mem_toFinset.mp hW)

theorem DeLeSemiPos.proof (hPL1 : ArithmeticPoincareLelongFormula) (hSt : StokesStatement) (hAdd : PtsAddFirst.Statement)
    (hLim : PtsRegLimit.Statement) (hMono : PtsMonoSemiPos.Statement) (hCurv : RegCurvBound.Statement)
    (hNot : HorizNotMem.Statement) : DeLeSemiPos.Statement := by
  intro K _ ι _ P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  obtain ⟨a, haA, hsa, hsP⟩ := id hs
  obtain ⟨a', haA', hsa', hs'P⟩ := id hs'
  have ht : ∃ b : K → ℕ, (∀ k, A.a k = b k) ∧ IsMultiHomog s b := ⟨a, haA, hsa⟩
  have ht' : ∃ b : K → ℕ, (∀ k, A'.a k = b k) ∧ IsMultiHomog s' b := ⟨a', haA', hsa'⟩
  obtain ⟨C, hC⟩ := hCurv K ι A' s' ht' hA'
  have hT := isSmoothHerm_ofMetrics_fs (ι := ι) (fun _ => (C : ℤ))
  generalize HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (C : ℤ)) = T at hC hT
  have hfin : ∀ t : MRing ι, {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
    fun t => (divSupp_finite P t).subset fun W h => h.1

  have e1 : ∀ ε : ℝ, 0 < ε →
      ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s) =
        ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A' s' ht' ε).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) := by
    intro ε hε
    have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
    rw [pot_cons, hAdd K ι P n L _ T A s hP hL (isSmoothHerm_tensor hA' hB) hT hA hs,
      hAdd K ι P n L A' _ A s hP hL hA' hB hA hs, hPL1 K ι P n L A _ s hP hL hA hB rfl hs]
  have h1 : Tendsto
      (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s))
      (𝓝[>] 0)
      (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => (e1 ε hε).symm
    refine Tendsto.congr' ev ((tendsto_const_nhds.add
      ((tendsto_finsum_of_finite (hfin s) fun W hW => ?_).sub ?_)).add tendsto_const_nhds)
    · exact (hLim K ι W n L A' s' ht' ((divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2) hL hA'
        (hNot K ι P (n + 2) s s' W hP hsP hs'P hnc hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons A L) A' s' ht' hP (forall_cons hA hL) hA' hs'P
      rwa [pot_cons] at h

  have h2 : ∀ δ : ℝ, 0 < δ →
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) ≤
      (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z)) := by
    intro δ hδ
    have hD : IsSmoothHerm (regLine A s ht δ) := isSmoothHerm_regLine hA hδ
    have hlimD := hLim K ι P (n + 1) (Fin.cons (regLine A s ht δ) L) A' s' ht' hP (forall_cons hD hL) hA'
      hs'P
    rw [pot_cons, hPL1 K ι P n L A' _ s' hP hL hA' hD rfl hs'] at hlimD
    have hR : Tendsto
        (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)))) := by
      have eR : ∀ ε : ℝ, 0 < ε →
          ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log ((regLine A s ht δ).h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) =
          ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
            (fun z => Real.log ((regLine A s ht δ).h z)) := by
        intro ε hε
        have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
        rw [pot_cons, ptsIntegral_add_first_log hAdd hP hL (isSmoothHerm_tensor hA' hB) hT hD rfl,
          ptsIntegral_add_first_log hAdd hP hL hA' hB hD rfl,
          hSt K ι P n L (regLine A s ht δ) (regLine A' s' ht' ε) hP hL hD hB rfl rfl]
      have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => eR ε hε
      exact Tendsto.congr' ev ((tendsto_const_nhds.add hlimD).add tendsto_const_nhds)
    have hle := le_of_tendsto_of_tendsto h1 hR (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMono K ι P (n + 1) _ A (regLine A s ht δ) s hP
        (forall_cons (isSmoothHerm_tensor (isSmoothHerm_tensor hA' (isSmoothHerm_regLine hA' hε)) hT) hL)
        (forall_cons (hC ε hε) hLp) hA hs hD rfl
        (fun z hz h0 => logNorm_le_log_regLine_h hδ.le hz.1 h0))
    linarith

  have h3 : Tendsto
      (fun δ => (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (logNorm A s)) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    refine (tendsto_finsum_of_finite (hfin s') fun W hW => ?_).add ?_
    · exact (hLim K ι W n L A s ht ((divSuppArith K ι P (n + 1) A' s' W hP hs' hW.1).1 hW.2) hL hA
        (hNot K ι P (n + 2) s' s W hP hs'P hsP (fun W h h' => hnc W h' h) hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons T L) A s ht hP (forall_cons hT hL) hA hsP
      rwa [pot_cons] at h
  have h4 := ge_of_tendsto h3 (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact h2 δ hδ)
  unfold De
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOffMinor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOffMinor

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def lineSubst (ι ν κ : Type) : (Σ b, T.wwIdx ι ν κ b) → Polynomial (MRing (T.wwIdx ι ν κ))
  | ⟨.base, i⟩ => Polynomial.C (X ⟨.base, i⟩)
  | ⟨.det, l⟩ => Polynomial.C (X ⟨.det, l⟩)
  | ⟨.line0, p⟩ => Polynomial.C (X ⟨.line0, p⟩)
  | ⟨.line1, p⟩ => Polynomial.C (X ⟨.line0, p⟩) * Polynomial.X

def blockSubst : T.WBlk → Polynomial (MvPolynomial T.WBlk Φ)
  | .line1 => Polynomial.C (X .line0) * Polynomial.X
  | b => Polynomial.C (X b)

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem map_comp_subst (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    (Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁))).comp
        (eval₂Hom (Int.castRingHom _) (lineSubst ι ν κ)) =
      (eval₂Hom (Polynomial.C.comp C) (blockSubst (Φ := Φ))).comp
        (T.multiConeMap (T.wwCoord x δ e φ a₀ a₀)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [T.multiConeMap]
  · rintro ⟨b, q⟩
    cases b <;> simp [T.multiConeMap, T.wwCoord, lineSubst, blockSubst]
    ring

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem diag_le_of_prop (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) (W : Ideal (MRing (T.wwIdx ι ν κ))) [W.IsPrime] (hW : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (m : κ)
    (hm : (X ⟨.line0, m⟩ : MRing (T.wwIdx ι ν κ)) ∉ W)
    (hprop : ∀ q : κ, (X ⟨.line0, m⟩ * X ⟨.line1, q⟩ - X ⟨.line1, m⟩ * X ⟨.line0, q⟩ :
      MRing (T.wwIdx ι ν κ)) ∈ W) :
    T.wwIdeal x δ e φ a₀ a₀ ≤ W := by
  classical
  let K := FractionRing (MRing (T.wwIdx ι ν κ) ⧸ W)
  let π : MRing (T.wwIdx ι ν κ) →+* K := (algebraMap _ K).comp (Ideal.Quotient.mk W)
  have hπ : ∀ g, π g = 0 ↔ g ∈ W := fun g => by
    simp only [π, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let σ := eval₂Hom (Int.castRingHom (Polynomial (MRing (T.wwIdx ι ν κ)))) (lineSubst ι ν κ)
  have hm' : π (X ⟨.line0, m⟩) ≠ 0 := fun h => hm ((hπ _).1 h)
  have hσ : (Polynomial.eval₂RingHom π (π (X ⟨.line1, m⟩) / π (X ⟨.line0, m⟩))).comp σ = π := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [σ]
    · rintro ⟨b, q⟩
      cases b
      · simp [σ, lineSubst]
      · simp [σ, lineSubst]
      · simp [σ, lineSubst]
      · have h := (hπ _).2 (hprop q)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
        simp only [σ, RingHom.comp_apply, eval₂Hom_X', lineSubst, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [mul_div_assoc', div_eq_iff hm']
        linear_combination -h
  intro g hg
  rw [T.wwIdeal, RingHom.mem_ker] at hg
  have h1 : Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁)) (σ g) = 0 := by
    rw [← RingHom.comp_apply, map_comp_subst, RingHom.comp_apply, hg, map_zero]
  have h2 : (σ g).map π = 0 := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, hπ]
    refine hW ?_
    rw [T.wwIdeal, RingHom.mem_ker]
    have := congrArg (fun f => Polynomial.coeff f n) h1
    simpa [Polynomial.coeff_map] using this
  rw [← hπ, ← hσ, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, h2,
    Polynomial.eval_zero]

theorem frame_rel (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (B : ChartBundle ℤ x 2 E) (hsec : T.IsTwistedDualSec B φ) (hdet : T.IsTwistedDetGen B e δ) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (l : ν) (k k' : κ) (N : ℕ) (F : MRing (T.wwIdx ι ν κ))
    (hF : IsMultiHomog F (T.wwDeg (N + 3) 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k')) (p : κ) :
    ∃ (n : ℕ) (α β : MRing (T.wwIdx ι ν κ)),
      X ⟨.base, i⟩ ^ n * F * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ ∧
        X ⟨.base, i⟩ ^ n * F * X ⟨.line1, p⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ := by
  classical
  obtain ⟨r₁, hr₁, h₁⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi p k' ((hdet i hi).1 l)
  obtain ⟨r₂, hr₂, h₂⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi k p ((hdet i hi).1 l)
  obtain ⟨n₁, G, hG, hGv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) x δ e φ a₀ a₁ i hi hr₁
  obtain ⟨n₂, H, hH, hHv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) x δ e φ a₀ a₁ i hi hr₂
  have hXp : ∀ M, IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := fun M =>
    DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_pow (DiagonalForms.isMultiHomog_X
      (ι := T.wwIdx ι ν κ) T.WBlk.base i) M) (by funext b; cases b <;> simp [T.wwDeg])
  have hdeg : ∀ {A B C : ℕ} {f : MRing (T.wwIdx ι ν κ)}, A + B = C → IsMultiHomog f (T.wwDeg B 0) →
      IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ A * f) (T.wwDeg C 0) := fun hABC hf =>
    DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_mul (hXp _) hf)
      (by funext b; cases b <;> simp [T.wwDeg, ← hABC])
  have hu := hdeg (A := n₁ + n₂) (C := N + 3 + n₁ + n₂) (by omega) hF
  have hα := hdeg (A := N + 3 + n₂) (C := N + 3 + n₁ + n₂) (by omega) hG
  have hβ := hdeg (A := N + 3 + n₁) (C := N + 3 + n₁ + n₂) (by omega) hH
  set c := T.wwCoord x δ e φ a₀ a₁
  set s := x i ^ (N + n₁ + n₂) * δ l
  have hxi : aeval c (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) = algebraMap Ω Φ (x i) := by
    rw [aeval_X]; rfl
  have hUv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (n₁ + n₂) * F) =
      algebraMap Ω Φ (s * dualMinor e φ k k') := by
    rw [map_mul, map_pow, hxi, hFv, ← map_pow, ← map_mul]; congr 1; ring
  have hAv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (N + 3 + n₂) * G) =
      algebraMap Ω Φ (s * dualMinor e φ p k') := by
    rw [map_mul, map_pow, hxi, hGv, ← map_pow, ← map_mul]; congr 1
    simp only [s, dualMinor]; linear_combination (-(x i ^ (N + n₁ + n₂))) * h₁
  have hBv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (N + 3 + n₁) * H) =
      algebraMap Ω Φ (s * dualMinor e φ k p) := by
    rw [map_mul, map_pow, hxi, hHv, ← map_pow, ← map_mul]; congr 1
    simp only [s, dualMinor]; linear_combination (-(x i ^ (N + n₁ + n₂))) * h₂
  have hcr : ∀ a : Φ, algebraMap Ω Φ (s * dualMinor e φ k k') * T.lineVal e (φ p) a -
      algebraMap Ω Φ (s * dualMinor e φ p k') * T.lineVal e (φ k) a -
      algebraMap Ω Φ (s * dualMinor e φ k p) * T.lineVal e (φ k') a = 0 := fun a => by
    simp only [T.lineVal, dualMinor, map_mul, map_sub]; ring
  have hC : ∀ a : Φ, (C (algebraMap Ω Φ (s * dualMinor e φ k k')) * C (T.lineVal e (φ p) a) -
      C (algebraMap Ω Φ (s * dualMinor e φ p k')) * C (T.lineVal e (φ k) a) -
      C (algebraMap Ω Φ (s * dualMinor e φ k p)) * C (T.lineVal e (φ k') a) : MvPolynomial T.WBlk Φ) = 0 :=
    fun a => by rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_sub, hcr, map_zero]
  have hX0 : ∀ q : κ, T.multiConeMap c (X ⟨T.WBlk.line0, q⟩) = C (T.lineVal e (φ q) a₀) * X T.WBlk.line0 :=
    fun q => by simp [T.multiConeMap, c, T.wwCoord]
  have hX1 : ∀ q : κ, T.multiConeMap c (X ⟨T.WBlk.line1, q⟩) = C (T.lineVal e (φ q) a₁) * X T.WBlk.line1 :=
    fun q => by simp [T.multiConeMap, c, T.wwCoord]
  refine ⟨n₁ + n₂, X ⟨T.WBlk.base, i⟩ ^ (N + 3 + n₂) * G, X ⟨T.WBlk.base, i⟩ ^ (N + 3 + n₁) * H, ?_, ?_⟩
  all_goals
    rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_sub, map_mul _ (_ ^ (n₁ + n₂) * F),
      map_mul _ (_ ^ (N + 3 + n₂) * G), map_mul _ (_ ^ (N + 3 + n₁) * H),
      DiagRAux.multiConeMap_of_homog c _ _ hu, DiagRAux.multiConeMap_of_homog c _ _ hα,
      DiagRAux.multiConeMap_of_homog c _ _ hβ, hUv, hAv, hBv]
  · rw [hX0, hX0, hX0]
    linear_combination ((∏ b, X b ^ T.wwDeg (N + 3 + n₁ + n₂) 0 b) * X T.WBlk.line0) * hC a₀
  · rw [hX1, hX1, hX1]
    linear_combination ((∏ b, X b ^ T.wwDeg (N + 3 + n₁ + n₂) 0 b) * X T.WBlk.line1) * hC a₁

end DiagonalOffMinor

open DiagonalOffMinor in

theorem DiagOffMinor.proof : DiagOffMinor.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec _ hdet _ a _ W hWp hrel hW i l k k' hfr hQ
  obtain ⟨hXi, -, N, F, hF, hFv, hFW⟩ := hfr
  classical
  have hi : x i ≠ 0 := by
    intro h0
    apply hXi
    apply hW
    rw [T.wwIdeal, RingHom.mem_ker]
    simp [T.multiConeMap, T.wwCoord, h0]
  have hrel' : ∀ p : κ, ∃ u α β : MRing (T.wwIdx ι ν κ), u ∉ W ∧
      u * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ ∈ W ∧
      u * X ⟨.line1, p⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩ ∈ W := fun p => by
    obtain ⟨n, α, β, h0, h1⟩ := frame_rel x δ e φ B hsec hdet (a 0) (a 1) i hi l k k' N F hF hFv p
    refine ⟨X ⟨T.WBlk.base, i⟩ ^ n * F, α, β, ?_, ?_, ?_⟩
    · intro h
      rcases hWp.mem_or_mem h with h' | h'
      · have hXn : ∀ m : ℕ, (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ m ∉ W := by
          intro m
          induction m with
          | zero => rw [pow_zero]; exact (Ideal.ne_top_iff_one W).1 hWp.ne_top
          | succ m ihm => rw [pow_succ]; exact fun hm => (hWp.mem_or_mem hm).elim ihm hXi
        exact hXn n h'
      · exact hFW h'
    · exact hW h0
    · exact hW h1
  have hQ' : (X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩ : MRing (T.wwIdx ι ν κ)) ∈ W := hQ
  obtain ⟨p, hp⟩ := hrel T.WBlk.line0
  by_cases hk : (X ⟨.line0, k⟩ : MRing (T.wwIdx ι ν κ)) ∈ W
  · have hk' : (X ⟨.line0, k'⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := by
      intro hk'
      obtain ⟨u, α, β, hu, h0, -⟩ := hrel' p
      have h := add_mem (add_mem h0 (W.mul_mem_left α hk)) (W.mul_mem_left β hk')
      rw [show u * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ + α * X ⟨.line0, k⟩ +
        β * X ⟨.line0, k'⟩ = u * (X ⟨.line0, p⟩ : MRing (T.wwIdx ι ν κ)) by ring] at h
      exact (hWp.mem_or_mem h).elim hu hp
    have := hWp
    refine diag_le_of_prop x δ e φ (a 0) (a 1) W hW k' hk' fun q => ?_
    obtain ⟨u, α, β, hu, h0, h1⟩ := hrel' q
    refine (hWp.mem_or_mem ?_).resolve_left hu
    rw [show u * (X ⟨.line0, k'⟩ * X ⟨.line1, q⟩ - X ⟨.line1, k'⟩ * X ⟨.line0, q⟩) =
      X ⟨.line0, k'⟩ * (u * X ⟨.line1, q⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩) -
        X ⟨.line1, k'⟩ * (u * X ⟨.line0, q⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩) -
        α * (X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩) by ring]
    exact sub_mem (sub_mem (W.mul_mem_left _ h1) (W.mul_mem_left _ h0)) (W.mul_mem_left _ hQ')
  · have := hWp
    refine diag_le_of_prop x δ e φ (a 0) (a 1) W hW k hk fun q => ?_
    obtain ⟨u, α, β, hu, h0, h1⟩ := hrel' q
    refine (hWp.mem_or_mem ?_).resolve_left hu
    rw [show u * (X ⟨.line0, k⟩ * X ⟨.line1, q⟩ - X ⟨.line1, k⟩ * X ⟨.line0, q⟩) =
      X ⟨.line0, k⟩ * (u * X ⟨.line1, q⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩) -
        X ⟨.line1, k⟩ * (u * X ⟨.line0, q⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩) +
        β * (X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩) by ring]
    exact add_mem (sub_mem (W.mul_mem_left _ h1) (W.mul_mem_left _ h0)) (W.mul_mem_left _ hQ')

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOffUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

open DiagonalForms in

theorem DiagOffUnit.proof (hF : DiagOffFrame.Statement) (hM : DiagOffMinor.Statement) :
    DiagOffUnit.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec hgen hdet hx a ha W hW hrel hPW hΔ
  obtain ⟨i, l, k, k', hfr⟩ := hF Ω ι ν κ E Φ x B e φ δ hsec hgen hdet hx a ha W hW hrel hPW
  have hQ : lineMinor k k' ∉ W := fun hQ =>
    hΔ (hM Ω ι ν κ E Φ x B e φ δ hsec hgen hdet hx a ha W hW hrel hPW i l k k' hfr hQ)
  obtain ⟨hXi, hXl, N, F, hFd, hFv, hFW⟩ := hfr
  refine ⟨T.wwDeg (N + 3) 0, T.wwDeg N 1, F,
    (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * X ⟨T.WBlk.det, l⟩ * lineMinor k k', hFd, ?_, ?_, hFW,
    ?_, ?_⟩
  · unfold lineMinor
    have := isMultiHomog_mul
      (isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) N)
        (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l))
      (isMultiHomog_sub
        (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k)
          (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k'))
        (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k')
          (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k)))
    refine isMultiHomog_of_eq this ?_
    funext b
    cases b <;> simp [T.wwDeg]
  · intro b
    cases b <;> simp [T.wwDeg]
  · intro hv
    rcases hW.mem_or_mem hv with h | h
    · rcases hW.mem_or_mem h with h | h
      · exact hXi (hW.mem_of_pow_mem _ h)
      · exact hXl h
    · exact hQ h
  · rw [hFv]
    simp only [lineMinor, map_mul, map_sub, map_pow, aeval_X]
    show algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) * algebraMap Ω Φ (dualMinor e φ k k') * T.diagSec a =
      algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) *
        (T.lineVal e (φ k) (a 0) * T.lineVal e (φ k') (a 1) - T.lineVal e (φ k') (a 0) * T.lineVal e (φ k) (a 1))
    rw [lineVal_cross, T.diagSec, dualMinor]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotAlgIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagPivotAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ),
    AlgebraicIndependent F (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotIdentity
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagPivotIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (S : PluckerBlocks n n j),
    flagMinor M j S * ∏ a ∈ Finset.Iic j, leadMinor M a = leadMinor M j * flagMinor (pivotMatrix M) j S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

