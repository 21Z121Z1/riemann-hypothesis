import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulLeftInvariantMapLevyProductMapToFourierJaco
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.LeftFJ

open GlobalTheory.RootEx

section Alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def conjN (p : ℕ) (g : GL n k) (u' : N k n c p) : N k n c p :=
  ⟨embX c g⁻¹ * (u' : GL (n ⊕ Fin c) k) * (embX c g⁻¹)⁻¹,
    ((Radical.unipotent_radical_basic k n c p).2.2.2.1 g⁻¹ u' u'.2).1⟩

theorem mul_prodRFJ_embX (ρ : ℕ) (g' : GL n k) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    embX c g' * (prodRFJ ρ q : GL (n ⊕ Fin c) k) = prodRFJ ρ ((g' * q.1.1, q.1.2), q.2) := by
  simp only [prodRFJ_coe, map_mul, mul_assoc]

theorem mul_prodRFJ_N (ρ : ℕ) (u' : N k n c (ρ + 1)) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (u' : GL (n ⊕ Fin c) k) * (prodRFJ ρ q : GL (n ⊕ Fin c) k) =
      prodRFJ ρ ((q.1.1, conjN (ρ + 1) q.1.1 u' * q.1.2), q.2) := by
  simp only [prodRFJ_coe, conjN, Subgroup.coe_mul, map_inv, inv_inv]
  group

theorem mul_prodRFJ_colE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k)
    (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    colE c (ρ + 1) β' * (prodRFJ ρ q : GL (n ⊕ Fin c) k) =
      prodRFJ ρ ((q.1.1, cjE ρ h1 h2 (((q.1.1)⁻¹ : GL n k).val *ᵥ β') q.1.2),
        ((q.1.1)⁻¹ : GL n k).val *ᵥ β' + q.2) := by
  obtain ⟨⟨g, u⟩, β⟩ := q
  set γ := ((g)⁻¹ : GL n k).val *ᵥ β'
  have hc : colE c (ρ + 1) β' = embX c g * colE c (ρ + 1) γ * (embX c g)⁻¹ := by
    rw [QuotStep.conj_colE]
    congr 1
    simp only [γ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [prodRFJ_coe, prodRFJ_coe, cjE_coe, hc, ← FourierJacobiGroup.colE_add]
  group

end Alg

section Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_conjN (p : ℕ) (u' : N k n c p) : Continuous fun g : GL n k => conjN p g u' := by
  have he := QuotStep.continuous_embX (k := k) (n := n) (c := c)
  refine Continuous.subtype_mk ?_ _
  exact ((he.comp continuous_inv).mul continuous_const).mul (he.comp continuous_inv).inv

theorem continuous_cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) :
    Continuous fun x : (n → k) × N k n c (ρ + 1) => cjE ρ h1 h2 x.1 x.2 := by
  have hc := QuotStep.continuous_colE (k := k) (n := n) (c := c) (ρ + 1)
  refine Continuous.subtype_mk ?_ _
  exact ((hc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
    (hc.comp continuous_fst).inv

theorem continuous_prodRFJ (ρ : ℕ) : Continuous (prodRFJ (k := k) (n := n) (c := c) ρ) := by
  have he := QuotStep.continuous_embX (k := k) (n := n) (c := c)
  have hc := QuotStep.continuous_colE (k := k) (n := n) (c := c) (ρ + 1)
  refine Continuous.subtype_mk ?_ _
  exact ((he.comp (continuous_fst.comp continuous_fst)).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul (hc.comp continuous_snd)

theorem continuous_invMulVec (β' : n → k) : Continuous fun g : GL n k => ((g⁻¹ : GL n k)).val *ᵥ β' :=
  (Units.continuous_val.comp continuous_inv).matrix_mulVec continuous_const

end Meas

theorem map_mul_left_of_conj {Q G : Type} [MeasurableSpace Q] [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure Q) (f : Q → G) (hf : Measurable f) (h : G) (T : Q → Q) (hT : MeasurePreserving T μ μ)
    (he : ∀ q, h * f q = f (T q)) : (μ.map f).map (h * ·) = μ.map f := by
  rw [Measure.map_map (measurable_const_mul h) hf]
  have : (fun x => h * x) ∘ f = f ∘ T := funext he
  rw [this, ← Measure.map_map hf hT.measurable, hT.map_eq]

theorem map_mul_left_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (κ : Measure G)
    (a b : G) (ha : κ.map (a * ·) = κ) (hb : κ.map (b * ·) = κ) : κ.map ((a * b) * ·) = κ := by
  have : (fun x => a * b * x) = (fun x => a * x) ∘ (fun x => b * x) := funext fun x => mul_assoc a b x
  rw [this, ← Measure.map_map (measurable_const_mul a) (measurable_const_mul b), hb, ha]

section Kinds
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  [SecondCountableTopology k] [BorelSpace (GL n k)] [SecondCountableTopology (GL n k)]
  [BorelSpace (GL (n ⊕ Fin c) k)] [SecondCountableTopology (GL (n ⊕ Fin c) k)]

def fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k) (g : GL n k) (x : N k n c (ρ + 1) × (n → k)) :
    N k n c (ρ + 1) × (n → k) :=
  (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β') x.1, ((g⁻¹ : GL n k)).val *ᵥ β' + x.2)

theorem measurable_fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k) :
    Measurable (Function.uncurry (fibFJ ρ h1 h2 β')) := by
  have hγ : Continuous fun p : GL n k × (N k n c (ρ + 1) × (n → k)) => ((p.1⁻¹ : GL n k)).val *ᵥ β' :=
    (continuous_invMulVec β').comp continuous_fst
  have hc : Continuous fun p : GL n k × (N k n c (ρ + 1) × (n → k)) =>
      (cjE ρ h1 h2 (((p.1⁻¹ : GL n k)).val *ᵥ β') p.2.1, ((p.1⁻¹ : GL n k)).val *ᵥ β' + p.2.2) :=
    ((continuous_cjE ρ h1 h2).comp (hγ.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (hγ.add (continuous_snd.comp continuous_snd))
  exact hc.measurable

theorem map_fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    [SFinite (volN ν n c (ρ + 1))] (β' : n → k) (g : GL n k) :
    ((volN ν n c (ρ + 1)).prod (Measure.pi fun _ : n => ν)).map (fibFJ ρ h1 h2 β' g) =
      (volN ν n c (ρ + 1)).prod (Measure.pi fun _ : n => ν) := by
  have e : fibFJ ρ h1 h2 β' g = Prod.map (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β'))
      (fun β => ((g⁻¹ : GL n k)).val *ᵥ β' + β) := rfl
  have hcm : Measurable (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β')) :=
    ((continuous_cjE ρ h1 h2).comp (continuous_const.prodMk continuous_id)).measurable
  rw [e, ← Measure.map_prod_map _ _ hcm (measurable_const_add _), GlobalTheory.T.conjByColumnUnipotent_preserves_unipotentHaar k n c ρ h1 h2 ν inferInstance,
    map_add_left_eq_self]

theorem mp_colE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    [SFinite (volN ν n c (ρ + 1))] (m : Measure (GL n k)) [SFinite m] (β' : n → k) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) =>
      ((q.1.1, cjE ρ h1 h2 (((q.1.1)⁻¹ : GL n k).val *ᵥ β') q.1.2), ((q.1.1)⁻¹ : GL n k).val *ᵥ β' + q.2))
      ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν))
      ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
  have hA := measurePreserving_prodAssoc m (volN ν n c (ρ + 1)) (Measure.pi fun _ : n => ν)
  have hs := (MeasurePreserving.id m).skew_product (measurable_fibFJ ρ h1 h2 β')
    (Filter.Eventually.of_forall (map_fibFJ ρ h1 h2 ν β'))
  exact (MeasurePreserving.symm _ hA).comp (hs.comp hA)

theorem mp_N (ρ : ℕ) (ν : Measure k) [ν.IsAddHaarMeasure] (V : Measure (N k n c (ρ + 1)))
    [V.IsMulLeftInvariant] [SFinite V] (m : Measure (GL n k)) [SFinite m] (u' : N k n c (ρ + 1)) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) =>
      ((q.1.1, conjN (ρ + 1) q.1.1 u' * q.1.2), q.2))
      ((m.prod V).prod (Measure.pi fun _ : n => ν)) ((m.prod V).prod (Measure.pi fun _ : n => ν)) := by
  have hm2 : Measurable (Function.uncurry fun (g : GL n k) (u : N k n c (ρ + 1)) => conjN (ρ + 1) g u' * u) :=
    (((continuous_conjN (ρ + 1) u').comp continuous_fst).mul continuous_snd).measurable
  have hs := (MeasurePreserving.id m).skew_product hm2 (Filter.Eventually.of_forall fun g => map_mul_left_eq_self V _)
  exact hs.prod (MeasurePreserving.id _)

theorem mp_embX (ρ : ℕ) (ν : Measure k) [ν.IsAddHaarMeasure] (V : Measure (N k n c (ρ + 1))) [SFinite V]
    (m : Measure (GL n k)) [m.IsMulLeftInvariant] [SFinite m] (g' : GL n k) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) => ((g' * q.1.1, q.1.2), q.2))
      ((m.prod V).prod (Measure.pi fun _ : n => ν)) ((m.prod V).prod (Measure.pi fun _ : n => ν)) :=
  ((measurePreserving_mul_left m g').prod (MeasurePreserving.id V)).prod (MeasurePreserving.id _)

end Kinds

theorem isMulLeftInvariant_map_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)).IsMulLeftInvariant := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν m hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL n k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI hVH : (volN ν n c (ρ + 1)).IsHaarMeasure :=
    (GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν).2.2.1
  haveI : SFinite (volN ν n c (ρ + 1)) := by rw [GlobalTheory.RootEx.VolN.volN_eq]; infer_instance
  have hf : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) := (continuous_prodRFJ ρ).measurable
  refine ⟨fun h => ?_⟩
  obtain ⟨r, hr, β', he⟩ := ((FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).1 h.1).1 h.2
  obtain ⟨g', u', hu', rfl⟩ := Radical.exists_of_mem_R hr
  have hg : embX c g' ∈ RFJ k n c ρ := Subgroup.mem_sup_right (Subgroup.mem_sup_left ⟨g', rfl⟩)
  have hu : u' ∈ RFJ k n c ρ := Subgroup.mem_sup_right (Subgroup.mem_sup_right hu')
  have hb : colE c (ρ + 1) β' ∈ RFJ k n c ρ := Subgroup.mem_sup_left (Subgroup.mem_sup_right
    ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) β' (Nat.lt_succ_self ρ)).1)
  have hh : h = (⟨embX c g', hg⟩ : RFJ k n c ρ) * ⟨u', hu⟩ * ⟨colE c (ρ + 1) β', hb⟩ := Subtype.ext he
  rw [hh]
  refine map_mul_left_mul _ _ _ (map_mul_left_mul _ _ _ ?_ ?_) ?_
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_embX ρ ν _ m g') fun q => Subtype.ext (mul_prodRFJ_embX ρ g' q)
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_N ρ ν _ m ⟨u', hu'⟩) fun q => Subtype.ext (mul_prodRFJ_N ρ ⟨u', hu'⟩ q)
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_colE ρ h1 h2 ν m β') fun q => Subtype.ext (mul_prodRFJ_colE ρ h1 h2 β' q)

end GlobalTheory.HaarR.LeftFJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_besselGroup_unfold_fundamental_domain : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  first | exact @GlobalTheory.Core.Mi.Unfold.lintegral_unfold | exact GlobalTheory.Core.Mi.Unfold.lintegral_unfold | (intros; apply GlobalTheory.Core.Mi.Unfold.lintegral_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListProdMapNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

private theorem list_prod_map_pow_eq {α : Type} (l : List α) (f g : α → ℂ) (n : ℕ) (h : ∀ a, f a ^ n = g a ^ n) :
    (l.map f).prod ^ n = (l.map g).prod ^ n := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, mul_pow, ih, h]

private theorem list_prod_map_ne_zero {α : Type} (l : List α) (f : α → ℂ) (h : ∀ a, f a ≠ 0) :
    (l.map f).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_ne_zero (h a) ih

theorem mono_pow_eq {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ χ' : (AE D)ˣ →* Circle) (n : ℕ) (hn : χ ^ n = χ' ^ n) :
    o.mono r e χ ^ n = o.mono r e χ' ^ n := by
  unfold TDat.mono
  apply list_prod_map_pow_eq
  intro i
  simp only [mul_pow, chrPow]
  congr 1
  have key : ∀ μ : (AE D)ˣ →* Circle, ((μ ((o.p i).idele o.q.unit) ^ e i : Circle) : ℂ) ^ n
      = ((((μ ^ n) ((o.p i).idele o.q.unit)) ^ e i : Circle) : ℂ) := by
    intro μ
    rw [MonoidHom.pow_apply, ← Circle.coe_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  rw [key χ, key χ', hn]

theorem mono_ne_zero {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ : (AE D)ˣ →* Circle) (hr : ∀ i, 0 < r i) : o.mono r e χ ≠ 0 := by
  unfold TDat.mono
  apply list_prod_map_ne_zero
  intro i
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (hr i).ne'
  · exact Circle.coe_ne_zero _

theorem mono_unitRatio : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (χ χ' : (AE D)ˣ →* Circle)
    (S : ℕ → Prop), (∀ i, 0 < r i) → (∃ n : ℕ, 0 < n ∧ χ ^ n = χ' ^ n) → UnitRatio S (o.mono r e χ) (o.mono r e χ') := by
  intro D c k _ _ _ _ ι o r e χ χ' S hr ⟨n, hn, hχ⟩
  exact (GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws S).2.2.1 _ _ n (mono_ne_zero o r e χ' hr) hn (mono_pow_eq o r e χ χ' n hχ)

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (N : Lat S) (P : Pl D → Prop), P q.v → IntIn q S F N → ∀ g : GA D S, Moves S g N N P → ∀ x : GL Y k, (mt S g).map q.pr = F.β * x.val * F.γ → x ∈ GlobalTheory.SplitWeil.KO k Y := by
  first | exact @GlobalTheory.SplitInt.mem_KO_of_moves | exact GlobalTheory.SplitInt.mem_KO_of_moves | (intros; apply GlobalTheory.SplitInt.mem_KO_of_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMap
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.LocFromGlob

open scoped TensorProduct

theorem mem_latLoc_iff_of_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hL' : L'.FG) (b : GL (Fin n) (TensorProduct F (Af F) E))
    (hb : ∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E)))
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E) :
    z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by

  let ext : (Fin n → Fv F v ⊗[F] E) → (Fin n → Af F ⊗[F] E) :=
    fun z i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have hself : ∀ z, GlobalTheory.AdelicU.vecLoc v (ext z) = z := fun z =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have hne : ∀ z u, u ≠ v → GlobalTheory.AdelicU.vecLoc u (ext z) = 0 := fun z u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have hmul : ∀ (g : GL (Fin n) (TensorProduct F (Af F) E)) u y, GlobalTheory.AdelicU.vecLoc u (g.val *ᵥ y) =
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom g).val *ᵥ
        GlobalTheory.AdelicU.vecLoc u y := fun g u y => funext fun i =>
    RingHom.map_mulVec (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom _ y i
  have hext : ∀ (M : Submodule (𝓞 E) (Fin n → E)), M.FG → ∀ z, z ∈ latLoc F M v →
      ext z ∈ Formalism.MainNotions.StandardLattice.latHat F E (M : Set (Fin n → E)) := fun M hM z hz => by
    rw [GlobalTheory.AdelicU.mem_latHat_iff hM]
    intro u
    by_cases e : u = v
    · subst e; rw [hself]; exact hz
    · rw [hne z u e]; exact zero_mem _
  constructor
  · intro hz
    have h1 := (GlobalTheory.AdelicU.mem_latHat_iff hL' _).1 ((hb _).1 (hext L hL z hz)) v
    rwa [hmul, hself] at h1
  · intro hz
    have h1 := hext L' hL' _ hz
    set y := ext ((Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z)
    have h2 : b.val *ᵥ ((b⁻¹).val *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hL _).1 ((hb _).2 (h2 ▸ h1)) v
    rw [hmul, hself, Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.Core.LocFromGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_space_of_typed_automorphic : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  first | exact @GlobalTheory.TriStep.mem_space_of_typed | exact GlobalTheory.TriStep.mem_space_of_typed | (intros; apply GlobalTheory.TriStep.mem_space_of_typed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ValueAtOrigin

theorem mixS_zero_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ h f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (d.mixS T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hS hS₀ μ 𝓕 hμ h f hf
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · have hz := (GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d μ 𝓕 hμ
    have hi := (GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hS.std).2.2.2 χS χT om om₀ hS hS₀ 1 h f hf
    rw [hz, hz, hi, map_one]
  · obtain ⟨hsp, hrat, -, -, -, hmix, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    have hc := GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT χT om om₀ hS hS₀ μ 𝓕 (hrat ▸ hμ) h f hf
    have h0 : ∀ g : WO S T → ℂ, heisO ψ S T (d.extX T 0) g = g := by
      intro g; funext w
      simp [heisO, symplOH_zero_right]
    rw [hmix, hmix, h0, h0, hc]

end GlobalTheory.ValueAtOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem le_mul_ofReal_inv_of_mul_le {a b : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (h : a * ENNReal.ofReal ((1 + r) ^ N) ≤ b) : a ≤ b * ENNReal.ofReal (((1 + r) ^ N)⁻¹) := by
  have hpos : 0 < (1 + r) ^ N := by positivity
  rw [ENNReal.ofReal_inv_of_pos hpos, ← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos)) (Or.inl ENNReal.ofReal_ne_top)]
  exact h

theorem mixS_le_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)),
    IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ≥0,
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w,
      ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ C * supSob ψ θ N f * ENNReal.ofReal (maj θ K N x) := by
  intro D ψ hψ θ hθ S S₀ T ρ d v U hU
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.mixedModelSource_support_finiteComponentInBox D ψ hψ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.mixedCoordinate_decay_realEntries D ψ hψ θ hθ S S₀ T ρ d v N
  refine ⟨C, fun f hf x w => ?_⟩
  by_cases h0 : d.mixS T ψ v.μ v.𝓕 f x w = 0
  · rw [h0]; simp
  · have hbox := hsupp f hf x w h0
    have hmaj : maj θ K N x = ((1 + realSize θ x) ^ N)⁻¹ := by
      unfold maj; rw [if_pos hbox]
    rw [hmaj]
    exact le_mul_ofReal_inv_of_mul_le (realSize_nonneg θ x) N (hC f hf.1 x w)

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MxAtEmbedKappa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KapLatSupp

theorem mxAt_embed_kappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S T A : HSp D) (o : OrthDec T A L') (P : Pl D → Prop) (x : WO S L'), MxAt P x → MxAt P ((B.o.resS S).symm (0, l.κ S x)) ∧ MxAt P ((o.resT S).symm (0, x)) := by
  intro D ρ B L' ζ' l S T A o P x hx
  refine ⟨?_, ?_⟩
  · rw [OrthDec.resS_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_r GlobalTheory.LastOpPf.mxAt_zero _)
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LinkKapMx.mxAt_linkKappa D ρ B L' ζ' l S P x hx) _)
  · rw [OrthDec.resT_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_l _ GlobalTheory.LastOpPf.mxAt_zero) (GlobalTheory.LastOpPf.mxAt_mul_l _ hx)

end GlobalTheory.KapLatSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinearStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_centre_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (z : MvPolynomial ℕ ℂ), (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → omCentreT om θ τ z (f + f') = omCentreT om θ τ z f + omCentreT om θ τ z f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → omCentreT om θ τ z (c • f) = c • omCentreT om θ τ z f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g h, thetaKO om g h (omCentreT om θ τ z f) = centreAct θ τ T z (fun h' => thetaKO om g h' f) h := by
  first | exact @GlobalTheory.Core.Rk.ZcComm.omCentreT_comm | exact GlobalTheory.Core.Rk.ZcComm.omCentreT_comm | (intros; apply GlobalTheory.Core.Rk.ZcComm.omCentreT_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_intertwiner_values_kFinite : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  first | exact @GlobalTheory.ItKFin.itKFin | exact GlobalTheory.ItKFin.itKFin | (intros; apply GlobalTheory.ItKFin.itKFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairSlotStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  first | exact @GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | exact GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | (intros; apply GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one <;> assumption)
end

