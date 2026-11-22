import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0004

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ProdExt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.prodExt :
    ∀ (Ω X Z : Type) [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] [T2Space Z] (ν : Measure Ω) (r : Ω → X) (s : Ω → Z) (ρ : Ω → ℂ),
    TopologicalSpace.IsTopologicalBasis {T : Set Z | IsCompact T ∧ IsOpen T} → Measurable r → Measurable s → Integrable ρ ν →
    (∀ (S : Set X) (T : Set Z), MeasurableSet S → IsCompact T → IsOpen T → ∫ ω, S.indicator 1 (r ω) * (T.indicator 1 (s ω) * ρ ω) ∂ν = 0) →
    ∀ Q : X × Z → ℂ, Measurable Q → (∀ x, ‖Q x‖ ≤ 1) → ∫ ω, Q (r ω, s ω) * ρ ω ∂ν = 0 := by
  intro Ω X Z _ _ _ _ _ _ _ ν r s ρ hB hr hs hρ H Q hQ hQ1
  have hφ : Measurable (fun ω => (r ω, s ω)) := hr.prodMk hs

  obtain ⟨e, he, heU⟩ : ∃ e : ℕ → Set Z, (∀ n, IsCompact (e n) ∧ IsOpen (e n)) ∧ ⋃ n, e n = Set.univ := by
    obtain ⟨T, hTc, hTs, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
      {T : Set Z | IsCompact T ∧ IsOpen T} (fun t ht => ht.2)
    have hne : (insert ∅ T).Nonempty := Set.insert_nonempty _ _
    obtain ⟨e, he⟩ := (hTc.insert ∅).exists_eq_range hne
    refine ⟨e, fun n => ?_, ?_⟩
    · have hn : e n ∈ insert ∅ T := he ▸ Set.mem_range_self n
      rcases hn with hn | hn
      · rw [hn]; exact ⟨isCompact_empty, isOpen_empty⟩
      · exact hTs hn
    · rw [← Set.sUnion_range, ← he, Set.sUnion_insert, Set.empty_union, hTU, hB.sUnion_eq]

  have hmass : ∫ ω, ρ ω ∂ν = 0 := by
    have hF : ∀ n, ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν = 0 := by
      intro n
      have hc : IsCompact (Set.accumulate e n) := isCompact_accumulate (fun i => (he i).1) n
      have ho : IsOpen (Set.accumulate e n) := by
        rw [Set.accumulate_def]
        exact isOpen_biUnion (fun i _ => (he i).2)
      have := H Set.univ (Set.accumulate e n) MeasurableSet.univ hc ho
      simpa using this
    have hlim : Tendsto (fun n => ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν)
        atTop (𝓝 (∫ ω, ρ ω ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
      · intro n
        have hm : MeasurableSet (Set.accumulate e n) :=
          (isCompact_accumulate (fun i => (he i).1) n).isClosed.measurableSet
        exact (((measurable_one.indicator hm).comp hs).aestronglyMeasurable).mul hρ.1
      · intro n
        refine Eventually.of_forall (fun ω => ?_)
        by_cases h : s ω ∈ Set.accumulate e n <;> simp [h]
      · refine Eventually.of_forall (fun ω => ?_)
        have hmem : s ω ∈ ⋃ n, e n := heU ▸ Set.mem_univ _
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with m hm
        have : s ω ∈ Set.accumulate e m := Set.mem_accumulate.2 ⟨n, hm, hn⟩
        simp [this]
    have := tendsto_nhds_unique hlim (by simp only [hF]; exact tendsto_const_nhds)
    exact this

  have hgen : (inferInstance : MeasurableSpace (X × Z)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
        {T : Set Z | IsCompact T ∧ IsOpen T}) := by
    have hD : IsCountablySpanning {T : Set Z | IsCompact T ∧ IsOpen T} := ⟨e, he, heU⟩
    have h1 : ‹MeasurableSpace Z› = MeasurableSpace.generateFrom {T : Set Z | IsCompact T ∧ IsOpen T} :=
      (BorelSpace.measurable_eq).trans hB.borel_eq_generateFrom
    have := generateFrom_prod_eq (isCountablySpanning_measurableSet (α := X)) hD
    rw [MeasurableSpace.generateFrom_measurableSet, ← h1] at this
    exact this
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
      {T : Set Z | IsCompact T ∧ IsOpen T}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod
      (fun a ha b hb _ => ⟨ha.1.inter hb.1, ha.2.inter hb.2⟩)
  have hset : ∀ A : Set (X × Z), MeasurableSet A → ∫ ω in (fun ω => (r ω, s ω)) ⁻¹' A, ρ ω ∂ν = 0 := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, T, hT, rfl⟩ := ht
      have hTm : MeasurableSet T := hT.2.measurableSet
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' (S ×ˢ T)) := hφ (hS.prod hTm)
      rw [← integral_indicator hm, ← H S T hS hT.1 hT.2]
      congr 1
      funext ω
      by_cases h1 : r ω ∈ S <;> by_cases h2 : s ω ∈ T <;> simp [Set.indicator, h1, h2]
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hφ htm) hρ, ih, hmass, sub_zero]
    | iUnion f hd hm ih =>
      rw [Set.preimage_iUnion, integral_iUnion (fun i => hφ (hm i))
        (fun i j hij => (hd hij).preimage _) hρ.integrableOn]
      simp [ih]

  have hint : ∀ (f : Ω → ℂ) (C : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ C) →
      Integrable (fun ω => f ω * ρ ω) ν := fun f C hf hC =>
    hρ.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)
  have hsimple : ∀ g : SimpleFunc (X × Z) ℂ, ∫ ω, g (r ω, s ω) * ρ ω ∂ν = 0 := by
    intro g
    induction g using SimpleFunc.induction with
    | const c hA =>
      rename_i A
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' A) := hφ hA
      have h0 := hset A hA
      rw [← integral_indicator hm] at h0
      have : (fun ω => (SimpleFunc.piecewise A hA (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) (r ω, s ω) * ρ ω)
          = fun ω => c * ((fun ω => (r ω, s ω)) ⁻¹' A).indicator ρ ω := by
        funext ω
        by_cases h : (r ω, s ω) ∈ A <;> simp [Set.indicator, h, Set.piecewise]
      rw [this, integral_const_mul, h0, mul_zero]
    | add hd hf hg =>
      rename_i f g
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have hif := hint (fun ω => f (r ω, s ω)) Cf (f.measurable.comp hφ) (fun ω => hCf _)
      have hig := hint (fun ω => g (r ω, s ω)) Cg (g.measurable.comp hφ) (fun ω => hCg _)
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [integral_add hif hig, hf, hg, add_zero]

  have hSM : StronglyMeasurable Q := hQ.stronglyMeasurable
  have hlim : Tendsto (fun n => ∫ ω, hSM.approxBounded 1 n (r ω, s ω) * ρ ω ∂ν) atTop
      (𝓝 (∫ ω, Q (r ω, s ω) * ρ ω ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
    · intro n
      exact (((hSM.approxBounded 1 n).measurable.comp hφ).aestronglyMeasurable).mul hρ.1
    · intro n
      refine Eventually.of_forall (fun ω => ?_)
      rw [norm_mul]
      have := hSM.norm_approxBounded_le zero_le_one n (r ω, s ω)
      calc _ ≤ 1 * ‖ρ ω‖ := by gcongr
        _ = ‖ρ ω‖ := one_mul _
    · refine Eventually.of_forall (fun ω => ?_)
      exact (hSM.tendsto_approxBounded_of_norm_le (hQ1 _)).mul_const _
  exact tendsto_nhds_unique hlim (by simp only [hsimple]; exact tendsto_const_nhds)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.PtMove
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem conj_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    {ξ : Fin 2 → F} (hξ : ξ ≠ 0) : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0 := by
  intro h
  have hl := Fintype.linearIndependent_iff.1 D.b.linearIndependent ![ξ 0, -ξ 1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, D.b0, D.b1, Algebra.smul_def, map_neg]
    simp only [Matrix.cons_val_fin_one, mul_one, map_neg]
    linear_combination h)
  apply hξ
  ext i
  fin_cases i
  · simpa using hl 0
  · simpa using hl 1

private theorem coe_al {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (ξ : Fin 2 → F) (h : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0) :
    ((al D ξ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (-rt (ξ 1)) := by
  have e := D.mkE_rt (ξ 0) (-ξ 1)
  have e' : -rt (ξ 1) = (rt (-ξ 1) : A F) := (map_neg _ _).symm
  rw [e', e, al, dif_neg h, IdeleGroup.coe_diagonal]
  simp [sub_eq_add_neg]

private theorem vcD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    (gl (cD t x)).val = !![x 0 0, x 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * x 1 0, x 1 1] := rfl

private theorem vgl {F : Type} [Field F] [NumberField F] (x : G1 F) : (gl x).val = x.1 := rfl

private theorem vmD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    (gl (mD t)).val = !![(t : A F), 0; 0, ((t⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem cD_dM {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    gl (cD t x) * dM t = dM t * gl x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, vcD, vgl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] <;> ring

private theorem dM_mD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : dM t * gl (mD t) = aE t := by
  refine Units.ext ?_
  rw [Units.val_mul, vmD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, aE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pt_move {F : Type} [Field F] [NumberField F] (t n : (A F)ˣ) (g : G1 F) :
    gl (cD t (mD t * g)) * dM (t * n) = aE t * (gl g * dM n) := by
  rw [UpperTheory.ConvolutionTheory.R2.dM_mul, ← mul_assoc, cD_dM, gl_mul, ← mul_assoc (dM t), dM_mD, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.wxPt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (ξ : Fin 2 → F), ξ ≠ 0 → ∃ t : Fˣ, ∀ f : GL (Fin 2) (A F) → ℂ, Pp.Lf f → ∀ φ h g,
    w1 W f φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) (mD (IdeleGroup.diagonal F t) * g)) = wx W f φ h ξ g := by
  intro F E _ _ _ _ _ _ _ D W ξ hξ
  have hz := conj_ne D hξ
  have hα := coe_al D ξ hz
  set α := al D ξ with hαdef
  let t : Fˣ := Units.map (Algebra.norm F : E →* F) (Units.mk0 _ hz)
  have hT : ideleNorm F E α = IdeleGroup.diagonal F t := by
    rw [hαdef, al, dif_neg hz, ideleNorm_diagonal]
  have hco : D.co (α : A E) = ![rt (ξ 0), -rt (ξ 1)] := by rw [hα, D.co_mkE]
  have ht : (t : F) = ξ 0 ^ 2 - D.δ * ξ 1 ^ 2 := by
    haveI := AdeleBaseChange.nontrivial_adeleRing F
    apply (algebraMap F (A F)).injective
    have h1 := D.coe_ideleNorm α
    rw [hT, IdeleGroup.coe_diagonal, hco] at h1
    simpa using h1
  refine ⟨t, fun f hf φ h g => ?_⟩
  set T := IdeleGroup.diagonal F t with hTdef
  have hnu : nu F (aE α * h) = T * nu F h := by rw [nu_mul, nu_aE, hT]
  have hpoint : ![T * (0 : A F), ((T⁻¹ : (A F)ˣ) : A F) * ((ideleNorm F E α : (A F)ˣ) * 1),
      T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 0, T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 1] = pt ξ := by
    have hb : am E (T : A F) * ((α⁻¹ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (rt (ξ 1)) := by
      rw [← hT, D.am_ideleNorm, mul_comm (α : A E), mul_assoc, Units.mul_inv, mul_one, hα, D.bar_mkE, neg_neg]
    have hc := D.co_am_mul (T : A F) ((α⁻¹ : (A E)ˣ) : A E)
    rw [hb, D.co_mkE] at hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    rw [D.mkE_one, mul_one, hT]
    simp [pt, ← h0, ← h1]
  have hhat : hat (W.Om (cD T (mD T * g)) (W.L (aE α * h) φ)).1 ![0, 1, 1, 0] = hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    have hcm : W.Om (cD T (mD T * g)) (W.L (aE α) (W.L h φ)) = W.L (aE α) (W.Om (mD T * g) (W.L h φ)) := by
      have := W.comm (aE α) (mD T * g)
      rw [nu_aE, hT] at this
      exact (LinearMap.congr_fun this (W.L h φ)).symm
    rw [map_mul, Module.End.mul_apply, hcm]
    have hS := hatSt F E D W
    have e1 := hS.aE α (W.Om (mD T * g) (W.L h φ)) 0 1 1 0
    have e2 := hS.m T (W.Om g (W.L h φ))
    have e3 : ((W.η.1 T : ℂˣ) : ℂ) = 1 := by rw [← hT, W.η_norm]; rfl
    have e4 : ab T = 1 := ab_diagonal t
    rw [e1, map_mul, Module.End.mul_apply, e2, e3, e4]
    have hv := hpoint
    rw [← hv]
    simp
  have hw : ∫ b in fundamentalSet F, f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) ∂(adeleMeasure F) =
      Wf f (aE T * (gl g * dM (nu F h))) := by
    rw [← ht]
    exact Pp.wfT F f hf t _
  simp only [w1, wx]
  rw [hhat, hnu, pt_move, hw]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.RowMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.rowMul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (p : (Fin 2 → A F) → ℂ) (φ φ' : S4 F), (∀ v, hat φ'.1 v = p ![v 0, v 1] * hat φ.1 v) →
    ∀ (g : G1 F) v, hat (W.Om g φ').1 v = p (![v 0, v 1] ᵥ* g.1) * hat (W.Om g φ).1 v := by
  intro F E _ _ _ _ _ _ _ D W
  have hS := hatSt F E D W
  let P : G1 F → Prop := fun g => ∀ (p : (Fin 2 → A F) → ℂ) (φ φ' : S4 F),
    (∀ v, hat φ'.1 v = p ![v 0, v 1] * hat φ.1 v) →
      ∀ v, hat (W.Om g φ').1 v = p (![v 0, v 1] ᵥ* g.1) * hat (W.Om g φ).1 v
  have hone : P 1 := by
    intro p φ φ' h v
    simpa using h v
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb p φ φ' h v
    have h1 := ha (fun r => p (r ᵥ* b.1)) (W.Om b φ) (W.Om b φ') (hb p φ φ' h) v
    simp only [map_mul, Module.End.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
    rw [h1, Matrix.vecMul_vecMul]
  have hn : ∀ b, P (nU b) := by
    intro b p φ φ' h v
    rw [hS.n, hS.n, h]
    have e : ![Function.update v 1 (v 1 + b * v 0) 0, Function.update v 1 (v 1 + b * v 0) 1] =
        ![v 0, v 1] ᵥ* (nU b).1 := by
      ext i
      fin_cases i <;> simp [nU, Matrix.vecMul, dotProduct, Fin.sum_univ_two, add_comm, mul_comm]
    rw [e]
    ring
  have hw : P (wW F) := by
    intro p φ φ' h v
    rw [hS.w, hS.w]
    have e : ![-v 1, v 0] = ![v 0, v 1] ᵥ* (wW F).1 := by
      ext i
      fin_cases i <;> simp [wW, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [← e, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [h]
    simp [mul_assoc]
  have hninv : ∀ b : A F, (nU b)⁻¹ = nU (-b) := by
    intro b
    refine inv_eq_of_mul_eq_one_right ?_
    refine Subtype.ext ?_
    show (nU b).1 * (nU (-b)).1 = 1
    simp [nU, Matrix.one_fin_two, Matrix.mul_fin_two]
  have hwinv : (wW F)⁻¹ = wW F * wW F * wW F := by
    refine inv_eq_of_mul_eq_one_right ?_
    refine Subtype.ext ?_
    show (wW F).1 * ((wW F).1 * (wW F).1 * (wW F).1) = 1
    simp [wW, Matrix.one_fin_two, Matrix.mul_fin_two]
  let T : Subgroup (G1 F) :=
    { carrier := {g | P g ∧ P g⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨hmul a b ha.1 hb.1, by
        rw [_root_.mul_inv_rev]; exact hmul _ _ hb.2 ha.2⟩
      one_mem' := ⟨hone, by rw [inv_one]; exact hone⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have hle : Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨b, rfl⟩ | rfl)
    · exact ⟨hn b, by rw [hninv]; exact hn _⟩
    · exact ⟨hw, by rw [hwinv]; exact hmul _ _ (hmul _ _ hw hw) hw⟩
  intro p φ φ' h g v
  have hg : g ∈ T := hle (by rw [(gen F).1]; exact Subgroup.mem_top g)
  exact hg.1 p φ φ' h v
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.TransN
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem nu_nE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) :
    nu F (nE D u * h) = nu F h := by
  have hd : Matrix.GeneralLinearGroup.det (nE D u) = 1 := by
    exact Units.ext (nU (D.mkE (u 0) (u 1))).2
  simp only [nu, map_mul, hd, one_mul]

private theorem cD_unit {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem om_L {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) (φ : S4 F) (g : G1 F) :
    W.Om g (W.L (nE D u * h) φ) = W.L (nE D u) (W.Om g (W.L h φ)) := by
  have hn : nu F (nE D u) = 1 := by
    have := nu_nE D u 1
    rw [mul_one] at this
    rw [this]
    simp [nu]
  have hc := W.comm (nE D u) g
  rw [hn, cD_unit] at hc
  rw [map_mul, Module.End.mul_apply]
  exact (LinearMap.congr_fun hc (W.L h φ)).symm

theorem UpperTheory.ConvolutionTheory.R2.G.transN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (u : Fin 2 → A F), T0 W M f φ (nE D u * h) = T0 W M f φ h ∧
    ∀ ξ, Wx W M f φ (nE D u * h) ξ = chi D.δ ξ u * Wx W M f φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M f φ h u
  have hH : St.Hat W := hatSt F E D W
  have hnu := nu_nE D u h
  constructor
  · unfold T0
    refine setIntegral_congr_fun M.meas fun g _ => ?_
    have hrow : ThRow 0 0 (W.Om g (W.L (nE D u * h) φ)).1 = ThRow 0 0 (W.Om g (W.L h φ)).1 := by
      rw [om_L]
      unfold ThRow
      refine tsum_congr fun ξ => ?_
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 0 (rt (ξ 0)) (rt (ξ 1))
      simpa [nE, zero_mul, neg_zero, ψ] using this
    simp only [hnu, hrow]
  · intro ξ
    have hpt : ∀ g, wx W f φ (nE D u * h) ξ g = chi D.δ ξ u * wx W f φ h ξ g := by
      intro g
      unfold wx
      rw [hnu, om_L]
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 1 (rt (ξ 0)) (rt (ξ 1))
      have e : hat (W.L (nE D u) (W.Om g (W.L h φ))).1 (pt ξ) =
          chi D.δ ξ u * hat (W.Om g (W.L h φ)).1 (pt ξ) := by
        simpa only [one_mul, chi, pt, nE] using this
      rw [e]
      ring
    unfold Wx Meas.I0
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [iw, hpt]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UnfoldSum
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem enorm_tsum_le' {β : Type*} (f : β → ℂ) : ‖∑' b, f b‖ₑ ≤ ∑' b, ‖f b‖ₑ := by
  by_cases h : ∑' b, ‖f b‖ₑ = ⊤
  · simp [h]
  · have hs : Summable fun b => ‖f b‖ := by
      simpa [toReal_enorm] using ENNReal.summable_toReal h
    have h1 : ‖∑' b, f b‖ ≤ ∑' b, ‖f b‖ := norm_tsum_le_tsum_norm hs
    have h2 : ENNReal.ofReal (∑' b, ‖f b‖) = ∑' b, ‖f b‖ₑ := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp [ofReal_norm_eq_enorm]
    rw [← h2, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal h1

private theorem tsum_comm_of_enorm {α β : Type*} (f : α → β → ℂ) (h : ∑' a, ∑' b, ‖f a b‖ₑ ≠ ⊤) :
    ∑' b, ∑' a, f a b = ∑' a, ∑' b, f a b := by
  have h' : ∑' p : α × β, ‖Function.uncurry f p‖ₑ ≠ ⊤ := by
    have : ∑' p : α × β, ‖Function.uncurry f p‖ₑ = ∑' a, ∑' b, ‖f a b‖ₑ :=
      ENNReal.tsum_prod (f := fun a b => ‖f a b‖ₑ)
    rwa [this]
  have hs : Summable fun p => ‖Function.uncurry f p‖ := by
    simpa [toReal_enorm] using ENNReal.summable_toReal h'
  exact (Summable.of_norm hs).tsum_comm

theorem UpperTheory.ConvolutionTheory.R2.G.unfoldSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), _root_.UpperTheory.ConvolutionTheory.R2.M.RowSec σ → ∀ (ι : Type) [Countable ι] (u : ι → G1 F → ℂ), (∀ i, NInv (u i)) → ∑' i, abelian₂ M (u i) ≠ ⊤ →
    Summable (fun i => ‖M.I0 (av (u i))‖) ∧ IntegrableOn (fun g => ∑' r, ∑' i, u i (ratS F (σ r) * g)) M.D M.μ ∧
    ∫ g in M.D, ∑' r, ∑' i, u i (ratS F (σ r) * g) ∂M.μ = ∑' i, M.I0 (av (u i)) := by
  intro F _ _ _ M σ hσ ι _ u hu hL
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hLi : ∀ i, abelian₂ M (u i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hL (ENNReal.le_tsum i)
  have hC := fun i => _root_.UpperTheory.ConvolutionTheory.R2.M.unfC F M σ (u i) hσ (hu i).1 (hu i).2 (hLi i)
  have hTL : ∀ i, ∫⁻ g in M.D, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = abelian₂ M (u i) := fun i =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.unfL F M σ (fun g => ‖u i g‖ₑ) hσ (hu i).1.enorm
      (fun ξ g => by simp only [(hu i).2 ξ g])
  have hTm : ∀ i, Measurable fun g : G1 F => ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i =>
    Measurable.ennreal_tsum fun r => ((hu i).1.comp (measurable_const_mul _)).enorm
  have hTT : ∫⁻ g in M.D, ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = ∑' i, abelian₂ M (u i) := by
    rw [lintegral_tsum fun i => (hTm i).aemeasurable]
    exact tsum_congr hTL
  have hfin : ∀ᵐ g ∂(M.μ.restrict M.D), ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ := by
    have hm : AEMeasurable (fun g : G1 F => ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ) (M.μ.restrict M.D) :=
      (Measurable.ennreal_tsum hTm).aemeasurable
    filter_upwards [ae_lt_top' hm (by rw [hTT]; exact hL)] with g hg using hg.ne
  have hST : ∀ i g, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≤ ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i g =>
    enorm_tsum_le' _
  have hSL : ∀ i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ abelian₂ M (u i) := fun i =>
    (lintegral_mono fun g => hST i g).trans_eq (hTL i)
  have hsum : ∑' i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≠ ⊤ :=
    ne_top_of_le_ne_top hL (ENNReal.tsum_le_tsum hSL)
  have hSm : ∀ i, AEStronglyMeasurable (fun g => ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) :=
    fun i => (hC i).2.1.aestronglyMeasurable
  have hI := integral_tsum hSm hsum
  have hae : ∀ᵐ g ∂(M.μ.restrict M.D),
      ∑' r, ∑' i, u i (ratS F (σ r) * g) = ∑' i, ∑' r, u i (ratS F (σ r) * g) := by
    filter_upwards [hfin] with g hg using
      tsum_comm_of_enorm (fun i r => u i (ratS F (σ r) * g)) hg
  have hI0 : ∀ i, M.I0 (av (u i)) = ∫ g in M.D, ∑' r, u i (ratS F (σ r) * g) ∂M.μ := fun i =>
    ((hC i).2.2.2).symm
  refine ⟨?_, ?_, ?_⟩
  · have hle : ∀ i, ‖M.I0 (av (u i))‖ₑ ≤ ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ := fun i => by
      rw [hI0 i]
      exact enorm_integral_le_lintegral_enorm _
    have : ∑' i, ‖M.I0 (av (u i))‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle)
    simpa [toReal_enorm] using ENNReal.summable_toReal this
  · have hsm : AEStronglyMeasurable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
        (f := fun (s : Finset ι) g => ∑ i ∈ s, ∑' r, u i (ratS F (σ r) * g)) ?_ ?_
      · intro s
        exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hSm i
      · filter_upwards [hfin] with g hg
        have h1 : ∑' i, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ :=
          ne_top_of_le_ne_top hg (ENNReal.tsum_le_tsum fun i => hST i g)
        have h2 : Summable fun i => ‖∑' r, u i (ratS F (σ r) * g)‖ := by
          simpa [toReal_enorm] using ENNReal.summable_toReal h1
        exact (Summable.of_norm h2).hasSum
    have hint : Integrable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine ⟨hsm, ?_⟩
      have hb : ∫⁻ g in M.D, ‖∑' i, ∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ ∑' i, abelian₂ M (u i) := by
        rw [← hTT]
        refine lintegral_mono fun g => ?_
        exact (enorm_tsum_le' _).trans (ENNReal.tsum_le_tsum fun i => hST i g)
      exact lt_of_le_of_lt hb hL.lt_top
    exact hint.congr (hae.mono fun g hg => hg.symm)
  · rw [integral_congr_ae hae, hI]
    exact tsum_congr fun i => (hI0 i).symm
end

