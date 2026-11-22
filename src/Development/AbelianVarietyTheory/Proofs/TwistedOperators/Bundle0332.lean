import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDataAtRealPlaceNegFirstLowEndLtCloud
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0334

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Cusp.WeightCommute

open Matrix

variable {D : D7} {V : HSp D}

theorem ratAct_mul' (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one' (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem hT_ratAct (γ : GF V) (a b : V.V) :
    V.hT (GlobalTheory.Cusp.ratAct D.sp.cm V γ a) (GlobalTheory.Cusp.ratAct D.sp.cm V γ b) = V.hT a b := by
  have hγ : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 * V.gram * γ.1.1 = V.gram := γ.2
  have hc : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 = Matrix.conjTranspose γ.1.1 := by
    ext i j; rfl
  rw [hc] at hγ
  have hr : ∀ w, V.frame.repr (GlobalTheory.Cusp.ratAct D.sp.cm V γ w) = γ.1.1 *ᵥ V.frame.repr w := fun w => by
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, GlobalTheory.Cusp.ratAct, LinearMap.toMatrix_toLin]
  have hform : ∀ x y : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, hr, hr, hform, hform, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hγ]

theorem hT_frame (Φ : WittFrame V) (i j : Fin (wittIndex V)) :
    V.hT (Φ.f j) (Φ.e i) = (if i = j then 1 else 0) ∧ V.hT (Φ.e j) (Φ.f i) = (if i = j then 1 else 0) ∧
    V.hT (Φ.e j) (Φ.e i) = 0 ∧ V.hT (Φ.f j) (Φ.f i) = 0 := by
  refine ⟨Φ.ef i j, ?_, Φ.ee i j, Φ.ff i j⟩
  rw [← V.herm.eq (Φ.f i) (Φ.e j)]
  have h : V.hT (Φ.f i) (Φ.e j) = if j = i then 1 else 0 := Φ.ef j i
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

end GlobalTheory.Cusp.WeightCommute

open GlobalTheory.Cusp.WeightCommute in

theorem GlobalTheory.Cusp.WeightCommute.commute_of_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  intro D V Φ u γ g t h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨xv, hxv⟩ : ∃ xv : Fin (wittIndex V) → V.V, ∀ i, xv i = if u i = 1 then Φ.e i else Φ.f i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ yv : Fin (wittIndex V) → V.V, ∀ i, yv i = if u i = 1 then Φ.f i else Φ.e i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (wittIndex V)), ∀ i, i ∈ S ↔ u i ≠ 0 :=
    ⟨Finset.univ.filter (fun i => u i ≠ 0), fun i => by simp⟩
  have hsgn : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  have hne : (-1 : SignType) ≠ 1 := by decide
  have hs : ∀ i ∈ S, u i = 1 ∨ u i = -1 := fun i hi => hsgn _ ((hS i).1 hi)
  have key := hT_frame Φ
  have neq : ∀ i j, u i = 1 → u j = -1 → i ≠ j := by
    rintro i j a b rfl; rw [a] at b; exact hne b.symm

  have mx : ∀ i ∈ S, xv i ∈ Φ.sub u := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hxv, if_pos a]; exact Submodule.subset_span (Or.inl ⟨i, a, rfl⟩)
    · rw [hxv, if_neg (by rw [a]; exact hne)]; exact Submodule.subset_span (Or.inr ⟨i, a, rfl⟩)
  have my : ∀ i ∈ S, yv i ∈ Φ.sub (-u) := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hyv, if_pos a]
      exact Submodule.subset_span (Or.inr ⟨i, show -(u i) = -1 by rw [a], rfl⟩)
    · rw [hyv, if_neg (by rw [a]; exact hne)]
      exact Submodule.subset_span (Or.inl ⟨i, show -(u i) = 1 by rw [a]; rfl, rfl⟩)

  have genX : ∀ z, (∀ i ∈ S, V.hT (xv i) z = 0) → ∀ w ∈ Φ.sub u, V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub u ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = 1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_pos (show u i = 1 from hi)] at this
        exact this
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = -1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_neg (by rw [show u i = -1 from hi]; exact hne)] at this
        exact this
    exact hle hw
  have genY : ∀ z, (∀ i ∈ S, V.hT (yv i) z = 0) → ∀ w ∈ Φ.sub (-u), V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have a : u i = -1 := neg_eq_iff_eq_neg.1 (show -(u i) = 1 from hi)
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_neg (by rw [a]; exact hne)] at this
        exact this
      · have a : u i = 1 := by
          have h' : -(u i) = -1 := hi
          simpa using h'
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_pos a] at this
        exact this
    exact hle hw

  have pxx : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (xv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.1
    · rw [(key i j).1, if_neg (neq i j a b)]
    · rw [(key i j).2.1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.2
  have pyy : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (yv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.2
    · rw [(key i j).2.1, if_neg (neq i j a b)]
    · rw [(key i j).1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.1
  have pyx : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (xv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).1
    · rw [(key i j).2.2.1, if_neg (neq i j a b)]
    · rw [(key i j).2.2.2, if_neg (neq j i b a).symm]
    · exact (key i j).2.1
  have pxy : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (yv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.1
    · rw [(key i j).2.2.2, if_neg (neq i j a b)]
    · rw [(key i j).2.2.1, if_neg (neq j i b a).symm]
    · exact (key i j).1

  have decomp : ∀ v : V.V, ∃ x ∈ Φ.sub u, ∃ y ∈ Φ.sub (-u), ∃ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) ∧
      (∀ w ∈ Φ.sub (-u), V.hT w z = 0) ∧ v = x + y + z := by
    intro v
    refine ⟨∑ i ∈ S, V.hT (yv i) v • xv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (mx i hi)),
      ∑ i ∈ S, V.hT (xv i) v • yv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (my i hi)),
      v - (∑ i ∈ S, V.hT (yv i) v • xv i) - ∑ i ∈ S, V.hT (xv i) v • yv i, genX _ ?_, genY _ ?_, by abel⟩
    · intro j hj
      rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pxx i hi j hj, smul_zero]),
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pxy i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        map_smul, pxy j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp
    · intro j hj
      rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pyx i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pyy i hi j hj, smul_zero]),
        map_smul, pyx j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp

  have inv_app : ∀ w, GlobalTheory.Cusp.ratAct D.sp.cm V γ (GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ w) = w := by
    intro w; rw [← ratAct_mul', mul_inv_cancel, ratAct_one']
  have zX : ∀ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) →
      ∀ w ∈ Φ.sub u, V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h3 w hw)
  have zY : ∀ z, (∀ w ∈ Φ.sub (-u), V.hT w z = 0) →
      ∀ w ∈ Φ.sub (-u), V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h4 w hw)
  have hmat : (g * γ).1.1 = (γ * g).1.1 := by
    apply (Matrix.toLin V.frame V.frame).injective
    apply LinearMap.ext
    intro v
    show GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ) v = GlobalTheory.Cusp.ratAct D.sp.cm V (γ * g) v
    rw [ratAct_mul', ratAct_mul']
    obtain ⟨x, hx, y, hy, z, hzX, hzY, rfl⟩ := decomp v
    simp only [map_add]
    rw [h5 _ (h1 x hx), h6 _ (h2 y hy), h7 _ (zX z hzX) (zY z hzY), h5 x hx, h6 y hy, h7 z hzX hzY,
      map_smul, map_smul]
  exact Subtype.ext (Units.ext hmat)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLocallyIntegrable
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.ConstantTermL2

theorem main : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule D.host.E V.V) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (F : DividedPowerChartLift V μ), LocallyIntegrable (constTerm (.single hW) (lift (GQ V) F)) μ ∧ (∀ u ∈ NA (.single hW), (fun g => constTerm (.single hW) (lift (GQ V) F) (u * g)) =ᵐ[μ] constTerm (.single hW) (lift (GQ V) F)) ∧ ∀ f : GA D V → ℂ, Continuous f → HasCompactSupport f → ∀ x, constTerm (.single hW) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) x = ∫ y, f (x⁻¹ * y) * constTerm (.single hW) (lift (GQ V) F) y ∂μ := by
  intro D V μ _ _ W hW F
  have hc := cocompact_single hW
  have hl := leftInv_lift (Γ := GQ V) F
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have hi := GlobalTheory.CuspAE.locallyIntegrable_lift (Γ := GQ V) (μ := μ) F
  refine ⟨GlobalTheory.CuspAE.locallyIntegrable_constTermOn hc hl hm hi, fun u hu => .of_forall fun g =>
    hc.constTermOn_mul_left hl hu g, fun f hf hs x => ?_⟩
  have e1 : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq (μ := μ) f _ x).symm
  rw [e1, ← convR_eq (μ := μ)]
  exact GlobalTheory.CuspAE.constTermOn_convR hc hl hm hi hf hs x

end GlobalTheory.ConstantTermL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_rightConvolution_along_one_parameter_products : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP | exact GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP | (intros; apply GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffHeisenbergTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaMatrixCoeff_heisenbergTranslate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Continuous (fun w : WO S T => thPair μ 𝓕 f (heisO ψ S T w f₀)) := by
  first | exact @GlobalTheory.MatCoefCont.continuous_thPair_heisO | exact GlobalTheory.MatCoefCont.continuous_thPair_heisO | (intros; apply GlobalTheory.MatCoefCont.continuous_thPair_heisO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientMatrixCoefficientContinuousOnUnitaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_matrix_coefficient_continuousOn_unitary : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  first | exact @GlobalTheory.coefA_dual_coef_continuousOn | exact GlobalTheory.coefA_dual_coef_continuousOn | (intros; apply GlobalTheory.coefA_dual_coef_continuousOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

theorem pairPar_X : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m →
    PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j))
      (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  intro D hS i j τ hi hj
  have hnear := grid_nearMid D τ
  have hB1 := gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ
  have hbe := grid_hbe D τ
  have heb := grid_heb D τ
  have hbb := grid_hbb D τ hS
  have hga := grid_hga D τ
  have hN0 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
  have hs2 : ((grid D τ).s : ℚ) + 2 ≤ (grid D τ).ga := by linarith
  have hsOdd := odd_sLen D
  have hle := entries_parD_le (grid D τ) hi hj hnear hB1 hbe hs2
  have hgap : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (bigN D : ℚ) ^ 3) := fun i' =>
    gapOver_parD (grid D τ) i' j hN0 hnear hB1 heb hbb hga
  have hlt : ∀ x ∈ (grid D τ).parD i j, x.1 + ((sLen D : ℚ) + 1) / 2 ≤ (cen D τ (D.R.m - i) : ℚ) := fun x hx =>
    hle x.1 (fst_mem_entries hx)
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδdef
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'def
  have e1 : Odd (i + 1 + j) ↔ ¬ Odd (i + j) := by
    rw [show i + 1 + j = (i + j) + 1 by ring]; exact Nat.odd_add_one
  have hδ : att c (rkV D (i + 1) j) = c + δ := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδdef, sub_eq_add_neg]
    · simp [att, odd_rkV_iff, e1, h, hδdef]
  have hδ' : att c (rkV D i j) = c + δ' := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδ'def]
    · simp [att, odd_rkV_iff, e1, h, hδ'def, sub_eq_add_neg]
  have key : partner (sLen D) false (c + δ) (c + δ') (shift δ ((grid D τ).parD i j)) =
      flip (shift δ' ((grid D τ).parD (i + 1) j)) := by
    rw [parD_succ _ hi]
    ext y
    simp only [partner, Finset.mem_union, Finset.mem_image, mem_flip, mem_shift, mem_plus]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)
      · have := hlt _ hx
        left
        rw [if_pos (by simp only at this; linarith)]
        simp only [Bool.not_not]
        convert hx using 2
        ring
      · right
        refine ⟨?_, rfl⟩
        show z - δ' ∈ TPar.block c (sLen D)
        exact sub_mem_block.2 (by simpa [add_comm] using hz)
    · rintro (h | ⟨h1, h2⟩)
      · left
        refine ⟨(y.1 - δ' + δ, !y.2), by simpa using h, ?_⟩
        have := hlt _ h
        rw [if_pos (by simp only at this ⊢; linarith)]
        ext
        · simp only; ring
        · simp
      · right
        refine ⟨y.1, ?_, ?_⟩
        · have : y.1 - δ' ∈ TPar.block c (sLen D) := h1
          simpa [add_comm] using sub_mem_block.1 this
        · ext
          · rfl
          · simpa using h2
  refine ⟨sLen D, flip (shift δ' ((grid D τ).parD (i + 1) j)), shift δ ((grid D τ).parD i j), ?_, rfl, Or.inr ?_⟩
  · exact flip_dualPar _
  · rw [hδ, hδ', ← key]
    have hX : ((grid D τ).parD i j).Nonempty :=
      ⟨((grid D τ).v 2, true), GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2 ⟨2, le_rfl, (grid D τ).two_le_k, rfl⟩, rfl⟩)⟩
    have hinj : Function.Injective fun x : ℚ × Bool => (x.1 + δ, x.2) := by
      intro a b e
      simp only [Prod.mk.injEq, add_left_inj] at e
      exact Prod.ext e.1 e.2
    have hcard : (shift δ ((grid D τ).parD i j)).card + sLen D ≤ bigN D := by
      rw [shift, card_image_of_injective _ hinj]
      have h1 := card_parD_le (grid D τ) (i := i) (j := j) hi.le
      have h2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have h3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      change _ ≤ D.R.r + j * D.R.t + i * sLen D at h1
      unfold bigN
      nlinarith
    have hN : 1800 < bigN D := by
      have := hS.1
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      unfold bigN
      nlinarith
    refine GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (sLen D) false (c + δ) (c + δ') _ (bigN D) (by unfold sLen; omega) (hX.image _)
      (GapOver.isRegular hN0 (gapOver_shift δ (hgap i))) ?_ ?_ hcard hN (gapOver_shift δ (hgap i))
      (by rw [key]; exact gapOver_flip (gapOver_shift δ' (hgap (i + 1))))
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := mem_shift.1 hsg
      obtain ⟨z, hz⟩ := int_of_mem_entries_parD (grid D τ) D.R.t_odd hsOdd (fst_mem_entries h)
      obtain ⟨w, hw⟩ := hsOdd
      simp only at hz
      refine ⟨z - cen D τ (D.R.m - i) - (w + 1), ?_⟩
      rw [hw]
      push_cast
      linarith
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := hlt _ (mem_shift.1 hsg)
      simp only at h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith

end GlobalTheory.GridParD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
noncomputable section

namespace GlobalTheory.TrConv

variable {D : D7}

theorem finFn_eq_tensorFin (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (y : GfC V) :
    finFn V ff y = tensorFin D.sp.cm.sig V.gram ff ((finPtsEquiv D.sp.cm.sig V.gram).symm y) := by
  unfold finFn tensorFin
  refine finprod_congr fun v => congrArg (ff v) ?_
  have := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm y)
  rw [← this]
  congr 1
  exact (congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y)).symm

theorem conv_finFn : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  intro D V μf _ h1 ν hν a b ha hb
  refine ⟨GlobalTheory.Orb.IsFinFamily.conv ha hb h1, funext fun y => ?_, ?_⟩
  · have hfam := GlobalTheory.Orb.IsFinFamily.mul_translate ha hb (y : GA D V)
    have hint : (fun x : GfC V => finFn V a x * finFn V b (x⁻¹ * y)) =
        finFn V (fun v x => a v x * b v (x⁻¹ * proj D.sp.cm.sig V.gram v (y : GA D V))) := by
      funext x
      have e1 := ha.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have e2 := hb.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      rw [finFn_eq_tensorFin, finFn_eq_tensorFin]
      unfold finFn
      unfold tensorFin
      rw [← finprod_mul_distrib e1 e2]
      refine finprod_congr fun v => ?_
      have p1 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have p2 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      have q1 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm x) = (x : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply x)
      have q2 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y)) = ((x⁻¹ * y : GfC V) : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply _)
      rw [q1] at p1
      rw [q2] at p2
      rw [← p1, ← p2]
      simp [map_mul, map_inv]
    symm
    show ∫ x, finFn V a x * finFn V b (x⁻¹ * y) ∂ν = _
    rw [hint, hν.2 _ hfam]
    rfl
  · have hm := ha.tensorFin_mem
    rw [show finFn V a = tensorFin D.sp.cm.sig V.gram a ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
      funext fun y => finFn_eq_tensorFin V a y]
    exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
      hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

end GlobalTheory.TrConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionPreservesCuspidalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_preserves_cuspidal : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, F ∈ GlobalTheory.Cusp.L2cusp V μ → IsCuspFun V (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) := by
  first | exact @GlobalTheory.CuspConv.isCuspFun_convR_lift | exact GlobalTheory.CuspConv.isCuspFun_convR_lift | (intros; apply GlobalTheory.CuspConv.isCuspFun_convR_lift <;> assumption)
end

