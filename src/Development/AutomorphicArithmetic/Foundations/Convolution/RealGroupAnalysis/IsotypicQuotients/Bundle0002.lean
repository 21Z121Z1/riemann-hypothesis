import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0003

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.ConvolutionTheory.R2.Pp.cuspZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.CuspZero F := by
  intro F _ _ _ π f hf
  obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
  refine ⟨⟨φ.2.1.continuous, (π.cusp _ hf).1.left⟩, fun g => ?_⟩
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← int_one (ι := UPos 2 1), ← φ.2.2 1 one_pos one_lt_two g]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unipGL x := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vn, unipMatrix, blockEntry_apply]
    rfl
  simp only [this]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfBasic :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfBasic F := by
  intro F _ _ f hf
  have hc : ∀ {f : GL (Fin 2) (A F) → ℂ}, Lf f → ∀ g, IntegrableOn (fun b => f (gl (nU b) * g) * ψ b) (fundamentalSet F)
      (adeleMeasure F) := fun hf g => intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  refine ⟨?_, fun b g => ?_, hc hf, fun c g => ?_, fun f' hf' g => ?_⟩
  · obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
    have e : Wf f = fun g => ∫ b in C, f (gl (nU b) * g) * ψ b ∂((adeleMeasure F).restrict (fundamentalSet F)) := by
      funext g
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]; rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasure F).restrict (fundamentalSet F)) :=
      isFiniteMeasure_restrict.2 (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top)
    exact continuous_parametric_integral_of_continuous
      ((hf.1.comp ((cont_n.comp continuous_snd).mul continuous_fst)).mul (cont_ψ.comp continuous_snd)) hC
  · unfold Wf
    rw [← integral_const_mul, ← int_add (h := fun x => ψ (-b) * (f (gl (nU x) * g) * ψ x))
      (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) b]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : ψ (-b) * ψ (x + b) = ψ x := by rw [← ψ_add]; congr 1; ring
    simp only [n_add, mul_assoc]
    rw [mul_left_comm, this]
  · unfold Wf
    rw [← integral_const_mul]
    simp [mul_assoc]
  · unfold Wf
    rw [← integral_add (hc hf g) (hc hf' g)]
    simp [add_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfEig
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open private eig_int from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigMap

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfEig :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfEig F := by
  intro F _ _ f hf v B h g
  refine eig_int ((adeleMeasure F).restrict (fundamentalSet F)) (h 1).card
    (fun b y => f (gl (nU b) * (g * finGL F 2 (locGL F 2 v y)))) ψ (fun b => ?_) fun y => ?_
  · simpa only [mul_assoc] using h (gl (nU b) * g)
  · exact intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfT
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfT :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfT F := by
  intro F _ _ f hf t g
  unfold Wf
  rw [← int_mul (h := fun x => f (gl (nU x) * (aE (IdeleGroup.diagonal F t) * g)) * ψ x)
    (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨γ, hγ⟩ := rat_a t
  have := a_n (IdeleGroup.diagonal F t) x
  simp only
  rw [← hf.2 γ (gl (nU x) * g), hγ, ← mul_assoc, ← mul_assoc, this]
  rfl
end

