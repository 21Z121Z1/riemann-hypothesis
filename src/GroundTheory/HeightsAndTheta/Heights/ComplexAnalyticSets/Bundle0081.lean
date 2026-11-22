import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0067
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDoublePointsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

namespace NormalDoublePointsGeneric

theorem ringKrullDim_quotient_le_of_primes {R : Type*} [CommRing R] (I : Ideal R) (k : WithBot ℕ∞)
    (h : ∀ W : Ideal R, W.IsPrime → I ≤ W → ∃ K : Ideal R, K ≤ W ∧ ringKrullDim (R ⧸ K) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨K, hKW, hK⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) K) :=
    ⟨l.length, fun i => ⟨(l i).1, show (K : Set R) ⊆ (l i).1.asIdeal from hKW.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) K) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ K) := (ringKrullDim_quotient K).symm
    _ ≤ k := hK

theorem ringKrullDim_quotient_anti {R : Type*} [CommRing R] {K K' : Ideal R} (h : K ≤ K') :
    ringKrullDim (R ⧸ K') ≤ ringKrullDim (R ⧸ K) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

theorem ringKrullDim_quot_sup_span_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

def belowNat : ℕ → WithBot ℕ∞
  | 0 => ⊥
  | e + 1 => (e : WithBot ℕ∞)

theorem belowNat_lt (d : ℕ) : belowNat d < (d : WithBot ℕ∞) := by
  cases d with
  | zero => exact WithBot.bot_lt_coe _
  | succ e =>
    show ((e : ℕ) : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞)
    exact_mod_cast Nat.lt_succ_self e

theorem le_belowNat_of_add_two_le {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ belowNat d := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_add, top_add] at h
        exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k =>
      have h2 : k + 1 + 1 ≤ d + 1 := by exact_mod_cast h
      cases d with
      | zero => omega
      | succ e => show ((k : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞); exact_mod_cast (by omega : k ≤ e)

theorem proof : NormalDoublePointsGeneric.Statement := by
  intro n d J u M hJ hdim hu
  classical
  choose a b hbJ hab using M.birational
  set bb : MvPolynomial (Fin n) ℂ := ∏ i, b i with hbb
  have hbbJ : bb ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  set K : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {bb} with hK
  have hfin : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  set S : Finset (Ideal (MvPolynomial (Fin n) ℂ)) := hfin.toFinset.filter (fun P => linForm u ∉ P) with hS
  have memS : ∀ P, P ∈ S ↔ P ∈ K.minimalPrimes ∧ linForm u ∉ P := fun P => by
    simp [hS]
  refine ⟨S.inf (fun P => P ⊔ Ideal.span {linForm u}), ?_, ?_, ?_⟩
  · refine Finset.le_inf fun P hP => sup_le_sup_right ?_ _
    exact le_sup_left.trans ((memS P).1 hP).1.1.2
  · have := hJ
    have hdimK : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      hdim ▸ ringKrullDim_quot_sup_span_add_one_le J hbbJ
    refine lt_of_le_of_lt (ringKrullDim_quotient_le_of_primes _ (belowNat d) fun W hW hIW => ?_) (belowNat_lt d)
    obtain ⟨P, hPS, hPW⟩ := (hW.inf_le').1 hIW
    refine ⟨_, hPW, le_belowNat_of_add_two_le ?_⟩
    obtain ⟨hPm, huP⟩ := (memS P).1 hPS
    have := hPm.1.1
    have h1 := ringKrullDim_quot_sup_span_add_one_le P huP
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) :=
      ringKrullDim_quotient_anti hPm.1.2
    calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (P ⊔ Ideal.span {linForm u})) + 1 + 1
        ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 := by gcongr; exact h1.trans h2
      _ ≤ _ := hdimK
  · intro q _ hqu hqI
    have evu : ∀ x, eval x (linForm u) = linEval u x := fun x => by simp [linForm, linEval]
    have hqP : ∀ P ∈ S, q ∉ zeroSet P := by
      intro P hP hqP
      apply hqI
      intro f hf
      have hf' : f ∈ P ⊔ Ideal.span {linForm u} := (Finset.inf_le (f := fun P => P ⊔ Ideal.span {linForm u}) hP) hf
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.1 hf'
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      simp [hqP p hp, evu, hqu]
    have hclosed : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet P) := fun P => by
      have : zeroSet P = ⋂ f ∈ P, {x : Fin n → ℂ | eval x f = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
    refine ⟨⋂ P ∈ S, (zeroSet P)ᶜ, (Filter.biInter_finset_mem S).2 fun P hP =>
      (hclosed P).isOpen_compl.mem_nhds (hqP P hP), ?_⟩
    intro w hw w' hw' hww hxN hne
    set x := IndefiniteRowSideFullHecke.ComplexSets.firstCoords w with hx
    have hwx : (w ∘ Sum.inl) = x := rfl
    have hw'x : (w' ∘ Sum.inl) = x := by rw [hww]; rfl
    have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => by
      have hf' : rename Sum.inl f ∈ M.ideal := by
        rw [← M.comap_eq] at hf; exact hf
      have := hw _ hf'
      rwa [eval_rename, hwx] at this
    have hbx : eval x bb = 0 := by
      by_contra hb
      apply hne
      funext s
      rcases s with i | i
      · exact congrFun hww i
      · have hbi : eval x (b i) ≠ 0 := fun h0 => hb (by
          rw [hbb, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have e1 := hw _ (hab i)
        have e2 := hw' _ (hab i)
        simp only [map_sub, map_mul, eval_rename, eval_X, hwx, hw'x] at e1 e2
        exact mul_left_cancel₀ hbi (by linear_combination e1 - e2)
    have hKx : K ≤ RingHom.ker (eval x) := sup_le (fun f hf => RingHom.mem_ker.2 (hxJ f hf))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hbx)))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPm, hPx⟩ := Ideal.exists_minimalPrimes_le hKx
    by_cases huP : linForm u ∈ P
    · rw [← evu]; exact RingHom.mem_ker.1 (hPx huP)
    · exfalso
      have hPS : P ∈ S := (memS P).2 ⟨hPm, huP⟩
      have hxP : x ∈ zeroSet P := fun f hf => RingHom.mem_ker.1 (hPx hf)
      exact (Set.mem_iInter₂.1 hxN P hPS) hxP

end NormalDoublePointsGeneric

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIrreducible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem eq_zero_of_mem_closure_of_continuousAt {σ : Type} [Fintype σ] {k : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} {u : σ → ℂ} (hk : ContinuousAt k u) (hu : u ∈ closure S)
    (h0 : ∀ y ∈ S, k y = 0) : k u = 0 := by
  have h1 := hk.continuousWithinAt.mem_closure_image hu
  have h2 : k '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h0 y hy
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, Set.mem_singleton_iff] at h3

theorem NormalGermIrreducible.proof (hreg : RegularLocusIdentity.Statement)
    (hext : NormalRiemannExtensionLocal.Statement) (hvan : VanishNearPoint.Statement) :
    NormalGermIrreducible.Statement := by
  classical
  intro σ _ I w hI hnorm hw
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  set X := zeroSetIn I with hX
  obtain ⟨h, hhI, hid⟩ := hreg σ I hI

  set U : Set (σ → ℂ) := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z} ∩
    {z | ∀ᶠ y in 𝓝 z, y ∈ X → f y * g y = 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g) |>.inter isOpen_setOfPred_eventually_nhds
  have hwU : w ∈ U := ⟨⟨hf, hg⟩, hfg⟩

  set E : (σ → ℂ) → Prop := fun z => ∀ᶠ y in 𝓝 z, y ∈ X → f y = 0 with hE

  have key : ∀ z ∈ X ∩ U, eval z h ≠ 0 → ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ((∀ u ∈ X ∩ V, E u) ∨ (∀ u ∈ X ∩ V, ¬ E u ∧ g u = 0)) := by
    rintro z ⟨hzX, hzU⟩ hhz
    obtain ⟨V, hVo, hzV, hVU, hVid⟩ := hid z hzX hhz U (hUo.mem_nhds hzU)
    refine ⟨V, hVo, hzV, hVU, ?_⟩
    have hfV : AnalyticOnNhd ℂ f V := fun y hy => (hVU hy).1.1
    have hgV : AnalyticOnNhd ℂ g V := fun y hy => (hVU hy).1.2
    by_cases hA : ∃ y ∈ X ∩ V, E y
    · left
      have hf0 := hVid f hfV hA
      intro u hu
      filter_upwards [hVo.mem_nhds hu.2] with y hyV hyX using hf0 y ⟨hyX, hyV⟩
    · right
      push Not at hA
      have hnz : ¬ E z := hA z ⟨hzX, hzV⟩
      have hfr : ∃ᶠ y in 𝓝 z, y ∈ X ∧ f y ≠ 0 := by
        rw [Filter.not_eventually] at hnz
        refine hnz.mono fun y hy => ?_
        by_contra hc
        exact hy fun hyX => by_contra fun hne => hc ⟨hyX, hne⟩
      obtain ⟨y, ⟨hyX, hfy⟩, hyV⟩ := (hfr.and_eventually (hVo.mem_nhds hzV)).exists
      have hg0 : ∀ᶠ u in 𝓝 y, u ∈ X → g u = 0 := by
        filter_upwards [(hVU hyV).2, (hfV y hyV).continuousAt.eventually_ne hfy] with u hu hfu huX
        exact (mul_eq_zero.1 (hu huX)).resolve_left hfu
      have hg0V := hVid g hgV ⟨y, ⟨hyX, hyV⟩, hg0⟩
      exact fun u hu => ⟨hA u hu, hg0V u hu⟩

  set φ : (σ → ℂ) → ℂ := fun z => if E z then 0 else 1 with hφ
  set S := (X ∩ U) \ {z | eval z h = 0} with hS
  have hφhol : HolomorphicOnSubset φ S := by
    rintro z ⟨hzXU, hhz⟩
    obtain ⟨V, hVo, hzV, -, hcase⟩ := key z hzXU hhz
    refine ⟨V, hVo, hzV, ?_⟩
    rcases hcase with h0 | h1
    · refine ⟨fun _ => 0, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_pos (h0 u ⟨hu.1.1.1, hu.2⟩)]
    · refine ⟨fun _ => 1, differentiableOn_const _, fun u hu => ?_⟩
      simp only [hφ, if_neg (h1 u ⟨hu.1.1.1, hu.2⟩).1]
  have hφb : Bornology.IsBounded (φ '' S) := by
    refine ((Set.finite_singleton (1 : ℂ)).insert 0).isBounded.subset ?_
    rintro _ ⟨z, -, rfl⟩
    by_cases hz : E z
    · simp [hφ, hz]
    · simp [hφ, hz]
  obtain ⟨V, hVo, hwV, hVU, F, hFd, hFeq⟩ :=
    hext σ I h w U φ hI hnorm hhI hw (hUo.mem_nhds hwU) hφhol hφb

  set N := V ∩ F ⁻¹' Metric.ball (F w) (1 / 2) with hN
  have hNo : IsOpen N := hFd.continuousOn.isOpen_inter_preimage hVo Metric.isOpen_ball
  have hwN : w ∈ N := ⟨hwV, Metric.mem_ball_self (by norm_num)⟩
  have hdense := zeroSetIn_subset_closure_diff hvan I h hI hhI

  have spread : ∀ k : (σ → ℂ) → ℂ, (∀ y ∈ U, ContinuousAt k y) →
      (∀ y ∈ X ∩ N, eval y h ≠ 0 → k y = 0) → ∀ᶠ u in 𝓝 w, u ∈ X → k u = 0 := by
    intro k hk h0
    filter_upwards [hNo.mem_nhds hwN] with u huN huX
    have hcl : u ∈ closure (N ∩ (X \ {z | eval z h = 0})) := hNo.inter_closure ⟨huN, hdense huX⟩
    exact eq_zero_of_mem_closure_of_continuousAt (hk u (hVU huN.1)) hcl
      fun y hy => h0 y ⟨hy.2.1, hy.1⟩ hy.2.2
  have hφN : ∀ y ∈ X ∩ N, eval y h ≠ 0 → ‖φ y - F w‖ < 1 / 2 := by
    rintro y ⟨hyX, hyV, hyF⟩ hhy
    rw [← hFeq ⟨⟨hyX, hyV⟩, hhy⟩]
    simpa [dist_eq_norm] using hyF
  by_cases hc : ‖F w‖ < 1 / 2
  · left
    refine spread f (fun y hy => hy.1.1.continuousAt) fun y hy hhy => ?_
    have hEy : E y := by
      by_contra hnE
      have h1 := hφN y hy hhy
      simp only [hφ, if_neg hnE] at h1
      have : ‖(1 : ℂ)‖ < 1 := by
        calc ‖(1 : ℂ)‖ = ‖(1 - F w) + F w‖ := by ring_nf
          _ ≤ ‖1 - F w‖ + ‖F w‖ := norm_add_le _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 hc
          _ = 1 := by norm_num
      simp at this
    exact hEy.self_of_nhds hy.1
  · right
    refine spread g (fun y hy => hy.1.2.continuousAt) fun y hy hhy => ?_
    have hnE : ¬ E y := by
      intro hEy
      have h1 := hφN y hy hhy
      simp only [hφ, if_pos hEy, zero_sub, norm_neg] at h1
      exact hc h1
    obtain ⟨V', -, hyV', -, hcase⟩ := key y ⟨hy.1, hVU hy.2.1⟩ hhy
    rcases hcase with h0 | h1
    · exact absurd (h0 y ⟨hy.1, hyV'⟩) hnE
    · exact (h1 y ⟨hy.1, hyV'⟩).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamChartInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamChartInt.proof (hCA : ChartIntCountAdd.Statement) (hPI : ParamPieceInt.Statement)
    (hCN : ParamCritNull.Statement) (hOR : ParamOffRegularZero.Statement)
    (hRP : RegularInjectivePieces.Statement) (hDI : ParamDensIntegrable.Statement) :
    ParamChartInt.Statement := by
  intro n d W A σ r r' N hW hdim hA hσ hinj hN hrr hprop hcov f φ hf hfc hfN hφ
  classical
  set F : (Fin d → ℂ) → ℝ := fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w with hF
  have hf0 : ∀ x, x ∉ N → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfN h)
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hmv : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
    have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
    convert h using 1
    funext x
    simp
  have hgd : DifferentiableOn ℂ g Ω := hmv.comp_differentiableOn (hσ.mono Set.inter_subset_left)
  set Reg : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hReg
  obtain ⟨P, hPm, hPd, hPU, hPinj⟩ := hRP d Ω g hΩo hgd
  have hPReg : ⋃ i, P i = Reg := by
    rw [hPU]; ext w
    simp only [hΩ, Reg, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  have hPsub : ∀ i, P i ⊆ Reg := fun i => hPReg ▸ Set.subset_iUnion P i
  have hRegB : Reg ⊆ Metric.ball 0 r := fun w hw => hw.1
  have hPB : ∀ i, P i ⊆ Metric.ball 0 r := fun i => (hPsub i).trans hRegB
  have hσP : ∀ i, MeasurableSet (σ '' P i) := fun i =>
    (hPm i).image_of_continuousOn_injOn (hσ.continuousOn.mono (hPB i)) (hinj.mono (hPB i))
  have hσReg : σ '' Reg = ⋃ i, σ '' P i := by rw [← hPReg, Set.image_iUnion]

  let E : ℕ → Set (Fin n → ℂ) := fun i => Nat.casesOn i (σ '' Reg)ᶜ fun j => σ '' P j
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    cases i with
    | zero => show MeasurableSet (σ '' Reg)ᶜ; rw [hσReg]; exact (MeasurableSet.iUnion hσP).compl
    | succ j => exact hσP j
  have hdisjP : ∀ i j, i ≠ j → Disjoint (σ '' P i) (σ '' P j) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba := hinj (hPB j hb) (hPB i ha) hab
    subst hba
    exact Set.disjoint_left.1 (hPd hij) ha hb
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => exact Set.disjoint_compl_left_iff_subset.2 (Set.image_mono (hPsub j))
    | succ i =>
      cases j with
      | zero => exact Set.disjoint_compl_right_iff_subset.2 (Set.image_mono (hPsub i))
      | succ j => exact hdisjP i j fun h => hij (by rw [h])
  have hEU : ⋃ i, E i = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ σ '' Reg
    · rw [hσReg, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      exact Set.mem_iUnion.2 ⟨j + 1, hj⟩
    · exact Set.mem_iUnion.2 ⟨0, hx⟩

  have hsum := hCA n d W A f φ E hW hdim hA hf.continuous hfc hφ hEm hEd
  rw [hEU, Set.indicator_univ] at hsum
  have h0 : chartInt W A ((E 0).indicator f) φ = 0 := hOR n d W A σ r N hσ hcov f φ hfN
  have hi : ∀ j, chartInt W A ((E (j + 1)).indicator f) φ = ∫ w in P j, F w := fun j =>
    hPI n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ (P j) hφ (hPm j) (hPB j)
      (fun w hw => ⟨(hPsub j hw).2.1, (hPsub j hw).2.2⟩) (hPinj j)
  have hL : HasSum (fun j => ∫ w in P j, F w) (chartInt W A f φ) := by
    have h1 := (hasSum_nat_add_iff' 1).2 hsum
    rw [Finset.sum_range_one, h0, sub_zero] at h1
    have h2 : (fun j => chartInt W A ((E (j + 1)).indicator f) φ) = fun j => ∫ w in P j, F w :=
      funext hi
    rwa [h2] at h1

  have hint : IntegrableOn F (Metric.ball 0 r) :=
    hDI n d W σ r r' N hσ hrr hprop f φ hf.continuous hfN hφ
  have hR : HasSum (fun j => ∫ w in P j, F w) (∫ w in Reg, F w) := by
    have h1 := hasSum_integral_iUnion hPm hPd (by rw [hPReg]; exact hint.mono_set hRegB)
    rwa [hPReg] at h1
  have hnull := hCN n d W A σ r N hW hdim hA hσ hinj hN fun w hw hwN => (hprop w hw hwN).1
  have hB : ∫ w in Metric.ball 0 r, F w = ∫ w in Reg, F w := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      Metric.isOpen_ball.measurableSet.nullMeasurableSet hRegB ?_
    have hae : ∀ᵐ w ∂(volume : Measure (Fin d → ℂ)), w ∉ {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧
        σ w ∈ N ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [hae] with w hw hwd
    obtain ⟨hwB, hwR⟩ := hwd
    by_cases hwN : σ w ∈ N
    · exfalso
      by_cases hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0
      · exact hw ⟨hwB, hwN, hdet⟩
      · exact hwR ⟨hwB, hwN, hdet⟩
    · show f (σ w) * _ = 0
      rw [hf0 _ hwN, zero_mul]
  rw [hB]
  exact hL.unique hR

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamDensIntegrable.analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem ParamDensIntegrable.proof : ParamDensIntegrable.Statement := by
  intro n d W σ r r' N hσ hrr' hN f φ hf hfN hφ
  set B := Metric.ball (0 : Fin d → ℂ) r with hB
  choose U hUo hZU hφU using hφ
  set V : Set (Fin d → ℂ) := B ∩ σ ⁻¹' (⋂ k, U k) with hV
  have hσc : ContinuousOn σ B := hσ.continuousOn
  have hVo : IsOpen V := hσc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_iInter_of_finite hUo)
  have hσ2 : ContDiffOn ℝ 2 σ B :=
    ((ParamDensIntegrable.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hσ).contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ σ) V := by
    intro k
    exact ((hφU k).of_le (WithTop.coe_le_coe.2 le_top)).comp (hσ2.mono Set.inter_subset_left)
      fun w hw => Set.mem_iInter.1 hw.2 k
  have hmaV : ContinuousOn (ReciprocityTheory.AnForm.maDens fun k => φ k ∘ σ) V :=
    ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ hVo hc2
  have hcont : ContinuousOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w) B := by
    refine continuousOn_of_forall_continuousAt fun w hw => ?_
    by_cases hs : σ w ∈ tsupport f
    · have hwV : w ∈ V := ⟨hw, Set.mem_iInter.2 fun k => hZU k (hN w hw (hfN hs)).1⟩
      exact ((hf.continuousAt).comp (hσc.continuousAt (Metric.isOpen_ball.mem_nhds hw))).mul
        (hmaV.continuousAt (hVo.mem_nhds hwV))
    · have hO : IsOpen (B ∩ σ ⁻¹' (tsupport f)ᶜ) :=
        hσc.isOpen_inter_preimage Metric.isOpen_ball (isClosed_tsupport f).isOpen_compl
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hO.mem_nhds ⟨hw, hs⟩] with w' hw'
      simp [image_eq_zero_of_notMem_tsupport hw'.2]
  have hK : IsCompact (Metric.closedBall (0 : Fin d → ℂ) r') := isCompact_closedBall 0 r'
  have hKB : Metric.closedBall (0 : Fin d → ℂ) r' ⊆ B := Metric.closedBall_subset_ball hrr'
  refine ((hcont.mono hKB).integrableOn_compact hK).of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet ?_
  rintro w ⟨hwB, hwK⟩
  have hf0 : f (σ w) = 0 := by
    by_contra h
    exact hwK (Metric.mem_closedBall.2 (by
      simpa using (hN w hwB (hfN (subset_tsupport f h))).2))
  simp [hf0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPoincareLelong
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem PoincareLelong.proof (hStokes : StokesOnVariety.Statement)
    (hReg : LelongRegularise.Statement) (hLim : LelongLimit.Statement) :
    PoincareLelong.Statement := by
  intro n d J u f φ hJ hdim hu hf hfc hφ
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ), varInt J (d + 1) f (vecCons (logReg u ε) φ) =
      varInt J (d + 1) (logReg u ε) (vecCons f φ) := fun ε hε =>
    hStokes n d J f (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hf)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hfc)
  exact tendsto_nhds_unique (hReg n d J u f φ hJ hdim hu hf hfc hφ)
    ((hLim n d J u f φ hJ hdim hu hf hfc hφ).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights
end

