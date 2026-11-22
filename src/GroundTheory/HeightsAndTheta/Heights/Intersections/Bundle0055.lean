import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDegrees
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiProjPrime divCycle intNum cycEval)
open GroundTheory.Heights₂.Heights.FieldNumbers (CutRegular.full IntNumSymm.full IntNumAdd.full IntNumBase.full
  homFracDegZero)

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zInt_cons_const (P : Ideal (MRing ι ℂ)) (e : ℕ) (c : ℝ) (φ : Fin e → MCone ι → ℝ)
    (g : MCone ι → ℝ) : zInt P (e + 1) (Fin.cons (fun _ => c) φ) g = 0 := by
  unfold zInt
  split_ifs with h
  · unfold Res.int
    rw [← ReciprocityTheory.AnForm.M.mIntConstPot h.some.atlas c (fun j => h.some.pot (φ j))
      (fun x => g (h.some.pt x))]
    refine ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _
    cases i using Fin.cases <;> rfl
  · rfl

theorem zPts_anti {P W : Ideal (MRing ι ℂ)} (h : P ≤ W) {z : MCone ι} (hz : z ∈ zPts W) :
    z ∈ zPts P :=
  ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isSmoothMetric_mono {P W : Ideal (MRing ι ℂ)} (h : P ≤ W) {L : HLine ι}
    (hL : IsSmoothMetric P L) : IsSmoothMetric W L := by
  intro z hz
  obtain ⟨U, hU, G, hG, hGU⟩ := hL z (zPts_anti h hz)
  exact ⟨U, hU, G, hG, fun w hw => hGU w ⟨hw.1, zPts_anti h hw.2⟩⟩

theorem isSmoothMetric_tensor {P : Ideal (MRing ι ℂ)} {A B : HLine ι} (hA : IsSmoothMetric P A)
    (hB : IsSmoothMetric P B) :
    IsSmoothMetric P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B) := by
  intro z hz
  obtain ⟨U, hU, G, hG, hGU⟩ := hA z hz
  obtain ⟨V, hV, H, hH, hHV⟩ := hB z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, G + H,
    (hG.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right), fun w hw => ?_⟩
  have hw0 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := hw.2.1
  show Real.log (A.h w * B.h w) = G w + H w
  rw [Real.log_mul (A.pos w hw0).ne' (B.pos w hw0).ne', ← hGU w ⟨hw.1.1, hw.2⟩,
    ← hHV w ⟨hw.1.2, hw.2⟩]
  rfl

theorem isSmoothFn_one (P : Ideal (MRing ι ℂ)) : IsSmoothFn P (fun _ => (1 : ℝ)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => ⟨Set.univ, Filter.univ_mem, fun _ => 1, contDiffOn_const,
    fun _ _ => rfl⟩⟩

theorem cons_comp_finRotate {n : ℕ} (c : K → ℤ) (bs : Fin n → K → ℤ) :
    (Fin.cons c bs : Fin (n + 1) → K → ℤ) ∘ finRotate (n + 1) =
      Fin.snoc (α := fun _ => K → ℤ) bs c := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    simp only [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ,
      Fin.snoc_castSucc]

theorem degrees_step (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) {e : ℕ}
    (ih : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e →
      (∀ j, IsSmoothMetric W (L j)) →
      zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ))
    {P : Ideal (MRing ι ℂ)} (hP : IsProjVar P (e + 1)) (L : Fin e → HLine ι)
    (hL : ∀ j, IsSmoothMetric P (L j)) (E : HLine ι) (c : K → ℕ) (hEc : ∀ k, E.a k = c k)
    (hE : IsSmoothMetric P E) :
    zInt P (e + 1) (Fin.cons (logH E) fun j => logH (L j)) (fun _ => 1) =
      (intNum ℂ P (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a) : ℝ) := by
  obtain ⟨s, hs, hsP⟩ := exists_form hP.1 c
  have hW : ∀ W ∈ comps P s, IsProjVar W e := fun W hW => isProjVar_of_mem_comps hP hs hsP hW
  have h1 := hPL1 K ι P e L E s (fun _ => 1) hP (hRes K ι P (e + 1) hP)
    (fun W hW' => hRes K ι W e (hW W hW')) hL hE ⟨c, hEc, hs, hsP⟩ (isSmoothFn_one P)
  rw [zInt_cons_const] at h1
  have hfin : (comps P s).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun W h => h.1
  have hsupp : Function.support (fun W => divCycle P s W * intNum ℂ W fun j => (L j).a) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι ℂ))) := by
    intro W hW
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hW (by simp only [divCycle, dif_neg (show ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W) from h), zero_mul])
  have hsum : (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) (fun _ => 1)) =
      ((cycEval (fun W => intNum ℂ W fun j => (L j).a) (divCycle P s) : ℤ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, cycEval, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    rw [Set.Finite.mem_toFinset] at hWm
    rw [ih W L (hW W hWm) fun j => isSmoothMetric_mono
      (le_sup_left.trans hWm.1.1.2) (hL j)]
  have hcut := CutRegular.full ℂ K ι P hP.1 e (relDim_of_isProjVar hP) c s hs hsP fun j => (L j).a
  have hsymm := IntNumSymm.full ℂ K ι P (e + 1) (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a)
    (finRotate (e + 1))
  rw [cons_comp_finRotate, hcut] at hsymm
  rw [← hsymm]
  linarith

theorem degrees_of (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) (hPt : ZIntPoint.Statement) (e : ℕ) :
    ∀ (P : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar P e → (∀ j, IsSmoothMetric P (L j)) →
      zInt P e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ P (fun j => (L j).a) : ℝ) := by
  induction e with
  | zero =>
    intro P L hP _
    rw [hPt K ι P _ hP (hRes K ι P 0 hP)]
    have hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = 0 := by
      rw [relDim_of_isProjVar hP]
      rfl
    obtain ⟨hfd, hb⟩ := IntNumBase.full ℂ K ι P hP.1 hrel
    have := hP.1.isPrime
    have hbot : homFracDegZero P = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have h1 : Module.finrank ℂ (homFracDegZero P) = 1 := IntermediateField.finrank_eq_one_iff.mpr hbot
    have hL0 : (fun j => (L j).a) = (![] : Fin 0 → K → ℤ) := Subsingleton.elim _ _
    rw [hL0, hb, h1]
    norm_num
  | succ e ih =>
    intro P M hP hM
    set A := M 0
    set L : Fin e → HLine ι := fun j => M j.succ
    have hL : ∀ j, IsSmoothMetric P (L j) := fun j => hM j.succ
    have hlog : (fun j => logH (M j)) = Fin.cons (logH A) fun j => logH (L j) := by
      funext j
      cases j using Fin.cases <;> rfl
    have hdeg : (fun j => (M j).a) = (Fin.cons A.a fun j => (L j).a : Fin (e + 1) → K → ℤ) := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hlog, hdeg]
    have ih' : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e →
        (∀ j, IsSmoothMetric W (L j)) →
        zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ) := ih
    let b : K → ℕ := fun k => (-(A.a k)).toNat
    let B : HLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric b
    have hB : IsSmoothMetric P B :=
      isSmoothMetric_of_isSmoothHerm P B (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric b)
    have hA : IsSmoothMetric P A := hM 0
    let c : K → ℕ := fun k => (A.a k + b k).toNat
    have hc : ∀ k, (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B).a k = c k := by
      intro k
      show A.a k + (b k : ℤ) = ((A.a k + b k).toNat : ℤ)
      simp only [b]
      omega
    have hC := degrees_step hPL1 hRes ih' hP L hL _ c hc (isSmoothMetric_tensor hA hB)
    have hBs := degrees_step hPL1 hRes ih' hP L hL B b (fun k => rfl) hB
    have hsum := ZIntAdd.proof K ι P e L A B hP (hRes K ι P (e + 1) hP) hL hA hB
    have hadd := IntNumAdd.full ℂ K ι P hP.1.multiHomog hP.1.relevant (e + 1) (relDim_of_isProjVar hP)
      (Fin.cons A.a fun j => (L j).a) 0 A.a (fun k => (b k : ℤ))
    simp only [Fin.update_cons_zero] at hadd
    have hcs : (fun k => ((c k : ℕ) : ℤ)) = A.a + fun k => (b k : ℤ) := by
      funext k
      simp only [c, b, Pi.add_apply]
      omega
    rw [hcs, hadd] at hC
    push_cast at hC
    linarith

theorem Degrees.proof (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) (hPt : ZIntPoint.Statement) :
    Degrees.Statement := by
  intro K _ _ ι _ P e L hP _ hL
  exact degrees_of hPL1 hRes hPt e P L hP hL

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreDivSupp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDivSupp.proof (h : FibreIncomp.Statement) : FibreDivSupp.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW W'
  have hmin : ∀ Q ∈ (P' ⊔ Ideal.span {rename v s}).minimalPrimes, IsRelevant Q → IsMultiProjPrime Q :=
    fun Q hQm hQr => ⟨hQm.1.1, cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP'.2.1.2.1
      (rename_isMultiHomog hv hs) hQm, hQr⟩
  have hmem : ∀ Q ∈ (P' ⊔ Ideal.span {rename v s}).minimalPrimes, P' ≤ Q ∧ rename v s ∈ Q :=
    fun Q hQm => ⟨le_sup_left.trans hQm.1.2,
      hQm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
  constructor
  · rintro ⟨⟨hW'p, hPW', himg⟩, hsW'⟩
    have := hW'p.1
    obtain ⟨Q, hQm, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW' ((Ideal.span_singleton_le_iff_mem _).2 hsW'))
    have hQr : IsRelevant Q := fun k => (hW'p.2.2 k).imp fun _ hi hq => hi (hQW' hq)
    obtain ⟨hPQ, hsQ'⟩ := hmem Q hQm
    have hQi : imageZ v Q = W := by
      have := hQm.1.1
      have hpr : (imageZ v Q).IsPrime := Ideal.comap_isPrime _ _
      have hle : imageZ v P' ⊔ Ideal.span {s} ≤ imageZ v Q :=
        sup_le (Ideal.comap_mono hPQ) ((Ideal.span_singleton_le_iff_mem _).2 hsQ')
      have hle2 : imageZ v Q ≤ W := himg ▸ Ideal.comap_mono hQW'
      exact le_antisymm hle2 (hW.1.2 ⟨hpr, hle⟩ hle2)
    have hQe := h K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW Q W' ⟨hmin Q hQm hQr, hPQ, hQi⟩
      ⟨hW'p, hPW', himg⟩ hQW'
    subst hQe
    exact ⟨⟨hQm, hQr⟩, hQi⟩
  · rintro ⟨⟨hW'm, hW'r⟩, himg⟩
    exact ⟨⟨hmin W' hW'm hW'r, (hmem W' hW'm).1, himg⟩, (hmem W' hW'm).2⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

namespace PointsAbsIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cxHessian_tensor {D : ℕ} {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    cxHessian (fun y' => Real.log ((X.tensor Y).h (γ y'))) y =
      cxHessian (fun y' => Real.log (X.h (γ y'))) y + cxHessian (fun y' => Real.log (Y.h (γ y'))) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (X.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hX (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (Y.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hY (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((X.tensor Y).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (X.h (γ y')) + 1 * Real.log (Y.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (X.pos _ hy'.2).ne' (Y.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simpa only [Complex.ofReal_one, one_smul] using hH

theorem abs_maDensity_le {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L T : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (hT : ∀ j, IsSmoothHerm (T j))
    (hTp : ∀ j, IsSemiPosHerm (T j)) (hLTp : ∀ j, IsSemiPosHerm ((L j).tensor (T j)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hS : IsSheet P Ψ y w γ) :
    |maDensity (fun j y' => pot L j (γ y')) y| ≤
      3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y := by
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0 := by
    filter_upwards [hS.2] with y' hy'
    exact ⟨hy'.1, hy'.2.1.1⟩
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hT j)
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (fun y' => pot L j (γ y')) y with hAdef
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ :=
    fun j => cxHessian (fun y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y with hBdef
  have hHT : ∀ j, (cxHessian (fun y' => Real.log ((T j).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ (T j) y w γ (hT j) (hTp j) hS
  have hHLT : ∀ j, (cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ _ y w γ (hLT j) (hLTp j) hS
  have hB : ∀ j, B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
      cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hLT j) (hT j) hγ
  have hA : ∀ j, cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y =
      A j + cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hL j) (hT j) hγ
  have hle : ∀ j, (B j - A j).PosSemidef := fun j => by
    have e1 : B j - A j = cxHessian (fun y' => Real.log ((T j).h (γ y'))) y +
        cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHT j).add (hHT j)
  have hge : ∀ j, (A j + B j).PosSemidef := fun j => by
    have e1 : A j + B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
        cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHLT j).add (hHLT j)
  have hn : ‖mixedDisc A‖ ≤ 3 ^ e * (mixedDisc B).re :=
    ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le A B hle hge
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [abs_mul, abs_of_nonneg hc]
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * |(mixedDisc A).re|
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (3 ^ e * (mixedDisc B).re) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hn) hc
    _ = 3 ^ e * ((e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc B).re) := by ring

end PointsAbsIntegrable

open PointsAbsIntegrable in

theorem PtsAbsIntegrable.proof (hInt : PtsIntegrableStatement) (hMeas : PtsAbsMeasurable.Statement) :
    PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hTw := SemiPosTwist.proof TorusInvLevi.proof
  choose T hTs hTp hLTp using fun j => hTw K ι (L j) (hL j)
  have hN : ∀ j, IsSmoothHerm (((L j).tensor (T j)).tensor (T j)) := fun j =>
    isSmoothHerm_tensor (isSmoothHerm_tensor (hL j) (hTs j)) (hTs j)
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have hs : IsSectionOn P A s := ⟨a, ha, hsa, hsP⟩
  set D := regLine A s ⟨a, ha, hsa⟩ 1 with hDdef
  have hD : IsSmoothHerm D := isSmoothHerm_regLine hA one_pos
  have hD1 : IsSectionOn P D 1 := by
    refine ⟨0, fun k => by simp [hDdef, regLine_a], fun m hm k => ?_,
      fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have h1 := hInt K ι P e Ψ _ A s hP hΨ hN hA hs
  have h2 := hInt K ι P e Ψ _ D 1 hP hΨ hN hD hD1

  have key : ∀ y w, |sheetDensity P Ψ (pot L) (logNorm A s) y w| ≤
      3 ^ e * (-2 * sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm D 1) y w -
        sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm A s) y w) := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · simp only [dif_pos hγ]
      set γ := hγ.choose
      have hS : IsSheet P Ψ y w γ := hγ.choose_spec
      have hmem : γ y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hm := abs_maDensity_le hL hTs hTp hLTp hS
      set r := Real.log (D.h (γ y)) with hr
      have hr0 : 0 ≤ r := by
        rw [hr, hDdef, log_regLine_h]
        exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg (secNorm A s (γ y))])) (by norm_num)
      have hgr : logNorm A s (γ y) ≤ r := by
        by_cases h0 : eval (γ y) (map (Int.castRingHom ℂ) s) = 0
        · have : logNorm A s (γ y) = 0 := by simp [logNorm, h0]
          rw [this]
          exact hr0
        · exact logNorm_le_log_regLine_h zero_le_one hmem.1 h0
      have hD1r : logNorm D 1 (γ y) = -r := by
        simp [logNorm, hr, Real.log_inv]
      rw [hD1r]
      have hg : |logNorm A s (γ y)| ≤ 2 * r - logNorm A s (γ y) := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc |logNorm A s (γ y)| * |maDensity (fun j y' => pot L j (γ y')) y|
          ≤ (2 * r - logNorm A s (γ y)) *
              (3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y) :=
            mul_le_mul hg hm (abs_nonneg _) (by linarith [abs_nonneg (logNorm A s (γ y))])
        _ = _ := by ring
    · simp only [dif_neg hγ]
      simp
  refine Integrable.mono' (((h2.const_mul (-2)).sub h1).const_mul (3 ^ e))
    (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) (Eventually.of_forall fun y => ?_)
  have hfin := fibreFinite K ι P e Ψ hP hΨ y
  simp only [Pi.sub_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => key y w

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocRank.proof (hDim : FibreDimStatement) (hAdj : SemilocRankAdjoin.Statement) :
    SemilocRank.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W hv hP' hZ hJ hs hsP hW
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ P' := hP'.2.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hZ
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (fibreIdeal κ G) (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, hAdj K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi']
  congr 1
  exact (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ThmIExists

theorem ThmIExists.proof (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement) (hWD : WellDefined.Statement)
    (hSymm : ThmISymm.Statement) : ThmIExists.Statement := by
  refine ⟨fun K _ ι _ => famI (K := K) (ι := ι), fun K _ ι _ => ?_⟩
  have hRF : IsRFamily (famI (K := K) (ι := ι)) :=
    isRFamily_famI hD1 hMul fun n hR hA P L B s t hP hL hB hs ht =>
      hWD K ι famI P n L B s t hR hA hP hL hB hs ht
  exact ⟨hSymm K ι _ hRF, hRF.1, hRF.2⟩

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StCentreOverW
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def CentreOverW.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (_hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    ∀ R : ValuationSubring (FractionRing (MRing ι' ⧸ P')),
      (∀ a ∈ locRing (imageZ v P') W, fracMapZ v P' a ∈ R) →
      ∀ y : Ideal (MRing ι'), IsValCentre P' R y → y = P' ∨ y ∈ fibreOver v P' W

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocRankFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRankFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (s : MRing ι) (α : K → ℕ) (W : Ideal (MRing ι)) (i' : ∀ k', ι' k')
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)) [Algebra ℚ G.Φ'],
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) =
      IntermediateField.relfinrank
        (IntermediateField.adjoin ℚ
          (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩))

end GroundTheory.Heights₂.Heights.Inter
end
end

