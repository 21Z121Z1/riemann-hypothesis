import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0426
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDarbouxComplexStructureTwoInvolutions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedingerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
      ⇑(archOp om h f₁) = schrF (trP F (Fin n × Fin d)) (archAct M h v) ⇑(archOp om h f) := by
  first | exact @GlobalTheory.ArchHeis.archOp_schrF | exact GlobalTheory.ArchHeis.archOp_schrF | (intros; apply GlobalTheory.ArchHeis.archOp_schrF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMulStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weilOperators_linear_one_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  first | exact @GlobalTheory.ArchLine.archOp_laws | exact GlobalTheory.ArchLine.archOp_laws | (intros; apply GlobalTheory.ArchLine.archOp_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWittStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_vertex_lattice_splits_along_witt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  first | exact @GlobalTheory.MonoBes.monoAt_bes | exact GlobalTheory.MonoBes.monoAt_bes | (intros; apply GlobalTheory.MonoBes.monoAt_bes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedSectionTendstoConstantTermImaginaryFlow
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.HeckeEx

theorem bddSec_tendsto_constTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, (∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom) ∧ Filter.Tendsto (fun t : ℝ => P (X.flow ξ (fun _ => Complex.I * t) x)) Filter.atTop (nhds (X.fj la ξ 0 P x)) := by
  intro E _ _ _ r X la P hP ξ hξ x hx
  have hdom : ∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom := fun t ht =>
    GlobalTheory.FjCauchy.flow_mem_dom X hξ hx _ fun τ => by
      have := GlobalTheory.FjCauchy.tt_pos X hξ hx τ
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add]
      linarith
  refine ⟨hdom, ?_⟩
  have hexp := m3bExp_holds (E := E) r X la P hP.1 ξ hξ x hx

  have hfac : ∀ (ν : X.Ψ → ℝ) (t : ℝ),
      Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ) =
        ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro ν t
    rw [Complex.ofReal_exp]
    congr 1
    have hs : ∑ τ, (ν τ : ℂ) * (Complex.I * (t : ℂ)) = (∑ τ, (ν τ : ℂ)) * (Complex.I * t) := by
      rw [Finset.sum_mul]
    simp only [hs]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  set F : ℝ → (X.Ψ → ℝ) → ℂ := fun t ν =>
    X.fj la ξ ν P x * Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ)
    with hF
  have hF' : ∀ t ν, F t ν = X.fj la ξ ν P x * ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro t ν; rw [hF]; dsimp only; rw [hfac]

  have hsum0 : Summable fun ν : X.Ψ → ℝ => X.fj la ξ ν P x := by
    have h := (hexp _ (hdom 0 le_rfl)).summable
    refine h.congr fun ν => ?_
    have := hF' 0 ν
    rw [hF] at this
    simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, _root_.mul_one] at this
    exact this
  have hbound : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr hsum0
  have hsign : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ := fun ν h =>
    BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP hξ ν hx h
  have hlim : Filter.Tendsto (fun t => ∑' ν, F t ν) Filter.atTop
      (nhds (∑' ν : X.Ψ → ℝ, if ν = 0 then X.fj la ξ 0 P x else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun ν => ?_) ?_
    · by_cases h0 : X.fj la ξ ν P x = 0
      · have : (if ν = 0 then X.fj la ξ 0 P x else 0) = 0 := by
          split_ifs with h; · subst h; exact h0
          · rfl
        rw [this]
        simp only [hF', h0, zero_mul]
        exact tendsto_const_nhds
      by_cases hν : ν = 0
      · subst hν
        simp only [hF', if_true, Finset.sum_const_zero, Pi.zero_apply, mul_zero, zero_mul, neg_zero,
          Real.exp_zero, Complex.ofReal_one, _root_.mul_one]
        exact tendsto_const_nhds
      · rw [if_neg hν]
        have hnn := hsign ν h0
        obtain ⟨τ0, hτ0⟩ : ∃ τ0, ν τ0 ≠ 0 := by
          by_contra hc; push_neg at hc; exact hν (funext hc)
        have hS : 0 < ∑ τ, ν τ :=
          Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ0, Finset.mem_univ _, lt_of_le_of_ne (hnn τ0) (Ne.symm hτ0)⟩
        have hk : 0 < 4 * Real.pi * ∑ τ, ν τ := by positivity
        have he : Filter.Tendsto (fun t : ℝ => Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)))
            Filter.atTop (nhds 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hk)
        have := ((Complex.continuous_ofReal.tendsto 0).comp he).const_mul (X.fj la ξ ν P x)
        simp only [Complex.ofReal_zero, mul_zero] at this
        simp only [hF']
        exact this
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht ν
      rw [hF', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      by_cases h0 : X.fj la ξ ν P x = 0
      · simp [h0]
      have hS : 0 ≤ ∑ τ, ν τ := Finset.sum_nonneg fun τ _ => hsign ν h0 τ
      have : Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 4 * Real.pi * (∑ τ, ν τ) * t := by positivity
        linarith
      calc ‖X.fj la ξ ν P x‖ * Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t))
          ≤ ‖X.fj la ξ ν P x‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖X.fj la ξ ν P x‖ := _root_.mul_one _
  rw [tsum_ite_eq] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [hF]
  exact (hexp _ (hdom t ht)).tsum_eq

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdempotentInIntegralClosureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementary_idempotent_in_integral_closure : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → finPart D (1 - cA D e) ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ GlobalTheory.LiftLevel.liftI Pg Q ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} := by
  first | exact @GlobalTheory.ConjCompl.offConj | exact GlobalTheory.ConjCompl.offConj | (intros; apply GlobalTheory.ConjCompl.offConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperatorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  first | exact @GlobalTheory.ArchLine.archOp_apply_continuous | exact GlobalTheory.ArchLine.archOp_apply_continuous | (intros; apply GlobalTheory.ArchLine.archOp_apply_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateActionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W,
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archAct M (γ (Multiplicative.ofAdd t)) v := by
  first | exact @GlobalTheory.ArchLine.continuous_archAct_line | exact GlobalTheory.ArchLine.continuous_archAct_line | (intros; apply GlobalTheory.ArchLine.continuous_archAct_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPart
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllSum

open Classical in

theorem finsum_subtype_ite {G : Type} (p : G → Prop) {u : G → ℂ} (hu : (Function.support u).Finite) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ δ ∈ hu.toFinset, if p δ then u δ else 0 := by
  rw [finsum_subtype_eq_finsum_cond (f := u) (p := p), finsum_eq_sum_of_support_subset (s := hu.toFinset)]
  · exact Finset.sum_congr rfl fun δ _ => finsum_eq_if
  · intro δ hδ
    simp only [Finite.coe_toFinset]
    intro h0
    exact hδ (by simp [h0])

theorem finsum_group {G Q I : Type} (c : G → Q) (ι : I → Q) (hι : Function.Injective ι) (p : G → Prop)
    (hp : ∀ g, p g ↔ ∃ i, c g = ι i) {u : G → ℂ} (hu : (Function.support u).Finite) (S : Finset I)
    (hS : ∀ g i, u g ≠ 0 → c g = ι i → i ∈ S) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ i ∈ S, ∑ᶠ δ : {δ // c δ = ι i}, u δ.1 := by
  classical
  rw [finsum_subtype_ite p hu, Finset.sum_congr rfl fun i _ => finsum_subtype_ite (fun δ => c δ = ι i) hu,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : u g ≠ 0 := by simpa using hg
  by_cases h : p g
  · obtain ⟨i, hi⟩ := (hp g).1 h
    rw [if_pos h, Finset.sum_eq_single_of_mem i (hS g i hg' hi) fun j _ hj =>
      if_neg fun e => hj (hι (e.symm.trans hi)), if_pos hi]
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun i _ => if_neg fun e => h ((hp g).2 ⟨i, e⟩)).symm

theorem elliptic_expansion {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {r : ℕ} {J : Matrix (Fin r) (Fin r) E}
    (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff)
    (dta : ∀ (P : PPol σ r) (w : InfinitePlace F), Measure (Tor P w.Completion))
    (dtf : ∀ (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)), Measure (Tor P (Fv F v)))
    (dt : ∀ P : PPol σ r, Measure (Tor P (AF F))) (ht : ∀ P, IsTorusMeas P (dta P) (dtf P) (dt P))
    (K : GAd σ J → ℂ)
    (hK : K = fun x => ∑ᶠ δ : {δ : GRat σ J // Irreducible δ.1.1.charpoly}, tensor σ J fa ff (x⁻¹ * ratEmb σ J δ.1 * x))
    (t : PPol σ r → ℂ)
    (hterm : t = fun P => ((torVol P (dt P)).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf P v) (ff v)) *
      ∏ w, Phi (J := J) (μa w) (dta P w) (fa w)) :
    (∀ P, (torVol P (dt P) ≠ ⊤ ∧ (∀ v, PhiOK (J := J) (μf v) (dtf P v) (ff v)) ∧
      ∀ᶠ v in cofinite, Phi (J := J) (μf v) (dtf P v) (ff v) = 1) ∧ ∀ w, PhiOK (J := J) (μa w) (dta P w) (fa w)) ∧
    (Function.support t).Finite ∧ Integrable (descend (ratPts σ J) K) (quotMeasure (ratPts σ J) μ) ∧
      ∫ q, descend (ratPts σ J) K q ∂quotMeasure (ratPts σ J) μ = ∑ᶠ P, t P := by
  have ha' : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w), (ha w).1⟩
  have hc := (continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)).2
  obtain ⟨hfin, hfinx⟩ := GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hcm r J _ hc
  have hpol := fun P => GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals E F σ hcm hun r P J hJ L μa μf μ hμ fa ff ha' hf (dta P) (dtf P) (dt P) (ht P)
  have hinj : Function.Injective (Subtype.val : PPol σ r → E[X]) := Subtype.val_injective
  set S : Finset (PPol σ r) := (hfin.preimage (f := fun P : PPol σ r => P.1) hinj.injOn).toFinset with hSdef
  have hS : ∀ (x : GAd σ J) (γ : GRat σ J) (P : PPol σ r), tensor σ J fa ff (x⁻¹ * ratEmb σ J γ * x) ≠ 0 →
      γ.1.1.charpoly = P.1 → P ∈ S := fun x γ P h e =>
    (Finite.mem_toFinset _).2 ⟨γ, e, x, subset_tsupport _ h⟩
  have hsum : descend (ratPts σ J) K = fun q => ∑ P ∈ S, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q := by
    funext q
    rw [hK]
    refine finsum_group (fun γ : GRat σ J => γ.1.1.charpoly) _ hinj _ (fun γ => ⟨fun h => ?_, ?_⟩)
      (u := fun γ => tensor σ J fa ff ((Quotient.out q)⁻¹ * ratEmb σ J γ * Quotient.out q))
      ((hfinx (Quotient.out q)).subset fun γ h => subset_tsupport _ h) S (hS _)
    · obtain ⟨P, hP, -⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hcm r J hJ).2 γ h
      exact ⟨P, hP⟩
    · rintro ⟨P, hP⟩
      rw [hP]
      exact P.2.2.1
  have hsupp : Function.support t ⊆ S := fun P hP => by
    by_contra hn
    refine hP ?_
    rw [hterm]
    refine (hpol P).2.symm.trans (integral_eq_zero_of_ae (.of_forall fun q => ?_))
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    by_contra h
    exact hn (hS _ δ.1 P h δ.2)
  refine ⟨fun P => ⟨⟨(GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 _ (ht P).haar, fun v => ?_, ?_⟩, fun w => ?_⟩,
    S.finite_toSet.subset hsupp, ?_, ?_⟩
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).1 v _ _ _ (hμ.haar_loc v) ((ht P).haar_loc v) (hf.1 v).1.continuous
      (hf.1 v).2
  · have := isLattice_stdLattice (E := Fld P) (n := 1)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hcm r P J hJ L, hf.2, hμ.eventually_eq_one,
      IsRestrictedProd.eventually_eq_one (ht P)] with v h1 h2 h3 h4
    have h5 := h1.2.2.2 (μf v) (dtf P v) (hμ.haar_loc v) ((ht P).haar_loc v) h3 h4
    rw [h2, Phi, finsum_eq_single _ ⟨1, h1.1⟩ fun q hq => (h5 q).2 fun e => hq (Subtype.ext e)]
    exact (h5 _).1 rfl
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).2 w _ _ _ (hμ.haar_arch w) ((ht P).haar_arch w) (ha' w).1 (ha' w).2
  · rw [hsum]
    exact integrable_finsetSum _ fun P _ => (hpol P).1
  · rw [hsum, integral_finsetSum _ fun P _ => (hpol P).1, finsum_eq_sum_of_support_subset _ hsupp, hterm]
    exact Finset.sum_congr rfl fun P _ => (hpol P).2

theorem ellipticPart : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPart := by
  intro D V lam S M T U μa μf μ fa ff h dta dtf dt ht
  obtain ⟨-, -, -, -, hμ, ha, hf⟩ := h
  exact elliptic_expansion (isCMExt_host D) (GlobalTheory.InertOfConj.unram D) (isHermND_gram V) (frameLat V) hμ ha.mem hf.isFinFamily
    dta dtf dt ht _ rfl _ rfl

end GlobalTheory.TrEllSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainEigenPartHasParametersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankChain_eigenPart_has_parameters : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  first | exact @GlobalTheory.EvenOnto.partPar | exact GlobalTheory.EvenOnto.partPar | (intros; apply GlobalTheory.EvenOnto.partPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  first | exact @GlobalTheory.EvenOnto.parBound_of_rapidDecay | exact GlobalTheory.EvenOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.EvenOnto.parBound_of_rapidDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitian
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChooseHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def scaleSpc {d : ℕ} (V : Spc F E d) (δ : E) : Spc F E d where
  J := δ • V.J
  L := V.L
  θ := V.θ
  bas := V.bas

theorem incM_smul {d : ℕ} (δ : E) (J : Matrix (Fin d) (Fin d) E) :
    incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
  ext i j
  simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]

theorem dbl_smul {d : ℕ} (c : AE F E) (X : Matrix (Fin d) (Fin d) (AE F E)) : dbl (c • X) = c • dbl X := by
  simp [dbl, Matrix.fromBlocks_smul, smul_neg]

end GlobalTheory.SplitChooseHerm

namespace GlobalTheory.SplitChooseHerm

theorem exists_admissible_unipotent_split_place_hermitian : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  intro _ F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, S, hS, hSe⟩ := GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary σ B V r s hB hV v hv hψ
  obtain ⟨δ, hδ, u, hu⟩ := GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace σ hB.cm v π₁ hP.2.2.1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((u : v.adicCompletionIntegers F) : Fv F v) = 0 := by rw [hu, map_zero, map_zero]
    exact u.ne_zero (Subtype.ext h0)
  have hcu : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
  have h2' : IsUnit (2 : v.adicCompletionIntegers F) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h2
    rwa [map_ofNat] at this
  let W' : Spc F E d := scaleSpc V δ
  have hskew : ∀ i j, σ (W'.J j i) = -W'.J i j := by
    intro i j
    show σ (δ * V.J j i) = -(δ * V.J i j)
    rw [map_mul, hδ, hV.herm]
    ring
  have hS' : ∃ S' : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S'.det ∧
      S'.map (fun x => (x : Fv F v)) =
        (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W'.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    refine ⟨(u : v.adicCompletionIntegers F) • S, ?_, ?_⟩
    · rw [Matrix.det_smul]
      exact (u.isUnit.pow _).mul hS
    · have e1 : (incM F W'.J).map π₁ = π₁ (inclR (F := F) (AF F) δ) • (incM F V.J).map π₁ := by
        show (incM F (δ • V.J)).map π₁ = _
        rw [incM_smul]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply]
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, ← hSe, ← hu]
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply]
  let g' : GlobalTheory.DblVac.UD σ W' := ⟨g.1, by
    have h := g.2
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F V.J) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F V.J) at h
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F (δ • V.J)) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F (δ • V.J))
    rw [incM_smul, dbl_smul, Matrix.mul_smul, Matrix.smul_mul, h]⟩
  have hg' : g' ∈ GlobalTheory.DblVac.KD σ W' v := hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ :=
    GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W' v hskew h2' π₁ π₂ b₁ b₂ hP hS' g' hg'
  refine ⟨Y, hYat, hYlat, ?_, M, hM, hMlat⟩
  change Yᵀ * incM F (δ • V.J) + incM F (δ • V.J) * Y.map (cA σ) = 0 at hYadm
  rw [incM_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hYadm
  have h3 := congrArg (fun X => inclR (F := F) (AF F) δ⁻¹ • X) hYadm
  simp only [smul_smul, hcu, one_smul, smul_zero] at h3
  exact h3

end GlobalTheory.SplitChooseHerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDarbouxComplexStructureTwoInvolutionsStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darboux_complex_structure_two_involutions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (θA : InfinitePlace F → Matrix α α ℂ)
    (θB : InfinitePlace F → Matrix β β ℂ) (ε ε' : InfinitePlace F → ℤˣ), IsCMExt F E σ →
    (∀ w, θA w * θA w = 1) → (∀ w, θB w * θB w = 1) →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ u u' u₁ : Matrix α β (AE F E),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧
        (∀ w, u'.map (piInf (τ w)) = (((ε' w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        (∀ w, u₁.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.SignInvolDarboux.exists_bridge | exact GlobalTheory.SignInvolDarboux.exists_bridge | (intros; apply GlobalTheory.SignInvolDarboux.exists_bridge <;> assumption)
end

