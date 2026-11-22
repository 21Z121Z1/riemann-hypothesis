import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsConvOfInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.BesInt

theorem absConv_of_invariant : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∀ f : GA D B.V → ℂ, Continuous f →
    (∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, f (γ * h) = f h) →
    ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h₁ n => f (n.1 * embA B.d B.o h₁ * h) := by
  intro D σ B f hf hinv h
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨hemb, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  obtain ⟨KA, hKA, hcovA⟩ := B.cpt
  obtain ⟨⟨KN, hKN, hcovN⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V σ B.d.e (isIsoSub_e B.d)

  let Φ : NFlag B.V B.d.e × GA D B.A → GA D B.V := fun p => p.1.1 * embA B.d B.o p.2 * h
  have hΦ : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_fst).mul (hemb.comp continuous_snd)).mul continuous_const
  have hΩ : IsCompact (Φ '' (KN ×ˢ KA)) := (hKN.prod hKA).image hΦ
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn

  have hbd : ∀ (h₁ : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h₁ * h)‖ ≤ C := by
    intro h₁ n
    obtain ⟨γ, hγ, hγK⟩ := hcovA h₁
    obtain ⟨δ, hδ, k, hk, hnk⟩ :=
      hcovN ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hconj n.1 n.2 γ⟩
    have heq : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = δ.1 * k.1 := congrArg Subtype.val hnk
    have hγV : embA B.d B.o γ ∈ GQ B.V := by
      have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
      rwa [one_mul] at this
    have hδQ : (δ.1 : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hδ
    have hηQ : (embA B.d B.o γ)⁻¹ * δ.1 ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hγV) hδQ,
        mul_mem (inv_mem (Subgroup.mem_sup_right ⟨γ, rfl⟩)) (Subgroup.mem_sup_left δ.2)⟩
    have e1 : n.1 = (embA B.d B.o γ)⁻¹ * (δ.1 * k.1) * embA B.d B.o γ := by rw [← heq]; group
    have e2 : n.1 * embA B.d B.o h₁ * h =
        ((embA B.d B.o γ)⁻¹ * δ.1) * (k.1 * embA B.d B.o (γ * h₁) * h) := by
      rw [e1, map_mul]; group
    rw [e2, hinv _ hηQ]
    exact hC _ ⟨(k, γ * h₁), ⟨hk, hγK⟩, rfl⟩

  have hfinA : B.vA.μ B.vA.𝓕 < ⊤ := by
    have hcov' : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ c ∈ KA, g = γ * c := fun g => by
      obtain ⟨γ, hγ, hc⟩ := hcovA g
      exact ⟨γ⁻¹, inv_mem hγ, γ * g, hc, by rw [inv_mul_cancel_left]⟩
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain B.A B.vA.μ B.vA.𝓕 KA B.vA.haar B.vA.fund hKA
      hcov' (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hfinN : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfinA.ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hfinN.ne
  have hK : Continuous (Function.uncurry fun (h₁ : GA D B.A) (n : flagN B.d) => f (n.1 * embA B.d B.o h₁ * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)).mul continuous_const)
  exact Integrable.of_bound hK.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hbd p.1 p.2)

end GlobalTheory.Unf.BesInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScaleStatement
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoint_nearCusp_scale : ∀ I : AutInst, NearInst I := by
  first | exact @GlobalTheory.CuspGeo.nearInst | exact GlobalTheory.CuspGeo.nearInst | (intros; apply GlobalTheory.CuspGeo.nearInst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), x0 B ⬝ a = x0 B ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  first | exact @GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint | exact GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint | (intros; apply GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGroup_semidirectProduct_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  first | exact @GlobalTheory.Unf.besSemi | exact GlobalTheory.Unf.besSemi | (intros; apply GlobalTheory.Unf.besSemi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnfLink

theorem star_psi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem link : ∀ D : D7, LinkLaw D := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  refine ⟨GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ, fun G' => ?_⟩
  unfold JacLev.perAll JacLev.per fjAll fjSrcKer
  congr 1; funext h; congr 1; funext n
  have hk := GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ Ξ hΞ
  obtain ⟨hp, hc⟩ := GlobalTheory.T.jacobiActions_match_through_linkMap D ρ ρ B L' ζ' hz l J.W J.W₀ J.d n.1 n.2
  simp only [fjAllFun, fjSrcKerFun, JacLev.ker, jacS, handBF, hk, Pi.smul_apply, smul_eq_mul, heisO_at_zero', hp, hc]
  rw [star_mul', star_star, star_psi s.weil₀.std]
  simp_rw [mul_left_comm (φ _) (ψ _)]
  rw [integral_const_mul]
  ring

end GlobalTheory.UnfLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedFunctionalThetaEstimate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.CharDecay

open GlobalTheory.OrientedHeis Filter Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem line_move (hθ : IsInfFam θ) {k l m n : ℕ} (P : Mx D k m) (Q : Mx D n l) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ P ⬝ z ⬝ compAt θ τ Q) t = (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k l :=
    { toFun := fun t => P ⬝ lineAt θ τ z t ⬝ Q
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by rw [AddMonoidHom.map_add, Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ P ⬝ z ⬝ compAt θ τ Q) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l).map (finPart D) = 0
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l) = _
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem phase_real (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (y : Mx D n m) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) :
    ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ κ).trace)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ τ, 2 * (Matrix.trace (compAt θ τ y ⬝ compAt θ τ κ)).re : ℝ) : ℂ)) := by
  set t := Matrix.trace (y ⬝ κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) t with hR
  have h1 : ψ (-R) = psiInf D.host.F ψ (-(fstA D.host.F R)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F R))
  have h4 : ∀ ρ, θ ρ (infPart D t) = Matrix.trace (compAt θ ρ y ⬝ compAt θ ρ κ) := fun ρ => by
    simp only [ht, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt]
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F R)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace (compAt θ ρ y ⬝ compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hR, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, h4]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring

theorem phase_line (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (y : Mx D n m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ lineAt θ τ z t).trace)) =
      Complex.exp (((4 * Real.pi * (Matrix.trace (compAt θ τ y ⬝ z)).re * t : ℝ) : ℂ) * Complex.I) := by
  have hL := isLineAt_lineAt hθ τ z
  rw [phase_real hψ hθ y _ (hL.2.1 t), Finset.sum_eq_single τ (fun τ' _ e => by
    rw [hL.2.2, if_neg e, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, mul_zero]) (by simp), hL.2.2, if_pos rfl,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring

theorem deriv_char (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (ℓ : (WO S T → ℂ) → ℂ)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f)
    (hb : ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L) (a : ℝ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h : ∀ t : ℝ, ℓ (heisO ψ S T (L t) f) = Complex.exp (((a * t : ℝ) : ℂ) * Complex.I) * ℓ f) :
    ℓ (dLine ψ S T L f) = (a : ℂ) * Complex.I * ℓ f := by
  have hsub : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f - g) = ℓ f - ℓ g := fun f g hf hg => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ g, hadd _ _ hf (theta_smul _ hg), hsmul _ _ hg]
    ring
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (((a * t : ℝ) : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).const_mul a).ofReal_comp).mul_const Complex.I).cexp
    simpa using this
  have h1 := (hd.tendsto_slope_zero_right.mul_const (ℓ f)).sub_const (ℓ (dLine ψ S T L f))
  have h0 : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (sub_eq_zero.1 (tendsto_nhds_unique h1 (squeeze_zero_norm' ?_ h0))).symm
  refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
  have hH := theta_heisO_real hθ hψ (hL.2 t) hf
  have hq := theta_smul (t : ℂ)⁻¹ (theta_sub hH hf)
  have hD := theta_dLine hθ hψ hL hf
  have h2 := (hb _ (theta_sub hq hD)).trans (iSup_le fun w =>
    (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC t ht w)))
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff ((norm_nonneg _).trans (hC t ht 0)), hsub _ _ hq hD,
    hsmul _ _ (theta_sub hH hf), hsub _ _ hH hf, h] at h2
  refine le_of_eq_of_le ?_ h2
  congr 2
  simp only [zero_add, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.real_smul, Complex.ofReal_inv]
  ring

theorem entry_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (P : Mx D T.rank m) (Q : Mx D n S.rank)
    (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f)
    (hb : ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ)
    (hchar : ∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) =
      ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (i : Fin n) (j : Fin m) :
    ‖ℓ f‖ₑ * ENNReal.ofReal ‖compAt θ τ y i j‖ ≤
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i (1 : ℂ) ⬝ compAt θ τ Q) f)‖ₑ +
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i Complex.I ⬝ compAt θ τ Q) f)‖ₑ := by
  have key : ∀ b : ℂ, ‖ℓ f‖ * |(compAt θ τ y i j * b).re| ≤
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i b ⬝ compAt θ τ Q) f)‖ := fun b => by
    rw [dRho_eq_dLine, deriv_char hψ hθ ℓ hadd hsmul hb (isRealDir_lineAt hθ τ _)
      (4 * Real.pi * (Matrix.trace (compAt θ τ y ⬝ single j i b)).re) hf fun t => by
        rw [line_move hθ, hchar _ f hf, phase_line hψ hθ], Matrix.trace_mul_single, op_smul_eq_mul, norm_mul, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 4 * Real.pi),
      mul_comm]
    refine mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) ?_) (norm_nonneg _)
    linarith [Real.pi_gt_three]
  have k1 := key 1
  have k2 := key Complex.I
  rw [mul_one] at k1
  rw [Complex.mul_I_re, abs_neg] at k2
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ (add_le_add k1 k2))
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im _) (norm_nonneg _)

end GlobalTheory.CharDecay

theorem GlobalTheory.CharDecay.decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (m n : ℕ) (P : Mx D T.rank m) (Q : Mx D n S.rank) (N : ℕ), ∃ C : ℝ≥0, ∀ (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m), (∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g) → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f) → (∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) → (∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) = ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f) → ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S T m n P Q N
  have hc : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ c : ℝ≥0, ∀ k (f : WO S T → ℂ),
      IsThetaFunO ψ S T f →
        supSob ψ θ k (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) ≤ c * supSob ψ θ (k + 1) f := fun τ z =>
    ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf =>
      GlobalTheory.Size.SupWord.ws_dRho_le (p := fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) hψ hθ GlobalTheory.Size.SupWord.supN_add_le
        GlobalTheory.Size.SupWord.supN_smul hf τ z k⟩
  choose c hc using hc
  induction N with
  | zero =>
    refine ⟨1, fun ℓ y _ _ hb _ f hf => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    unfold supSob
    rw [GlobalTheory.Size.wordSum_zero]
    exact hb f hf
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + ∑ τ, ∑ i : Fin n, ∑ j : Fin m, (C * c τ (compAt θ τ P ⬝ single j i (1 : ℂ) ⬝ compAt θ τ Q) +
      C * c τ (compAt θ τ P ⬝ single j i Complex.I ⬝ compAt θ τ Q)), fun ℓ y hadd hsmul hb hchar f hf => ?_⟩
    have hs := realSize_nonneg θ y
    have hd : ∀ τ z, ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤
        (C * c τ z : ℝ≥0) * supSob ψ θ (N + 1) f := fun τ z => by
      refine (hC ℓ y hadd hsmul hb hchar _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)).trans ?_
      rw [ENNReal.coe_mul, mul_assoc]
      exact mul_le_mul_right (hc τ z N f hf) _
    have he : ENNReal.ofReal (realSize θ y) = ∑ τ, ∑ i, ∑ j, ENNReal.ofReal ‖compAt θ τ y i j‖ := by
      unfold realSize
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    rw [pow_succ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one hs, ENNReal.ofReal_one, he,
      ← mul_assoc, mul_add, mul_one, ENNReal.coe_add, add_mul]
    refine add_le_add ((hC ℓ y hadd hsmul hb hchar f hf).trans
      (mul_le_mul_right (GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f) _)) ?_
    simp only [ENNReal.ofNNReal_finsetSum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [mul_right_comm, ENNReal.coe_add, add_mul]
    refine (mul_le_mul_left (GlobalTheory.CharDecay.entry_le hψ hθ P Q ℓ y hadd hsmul hb hchar hf τ i j) _).trans ?_
    rw [add_mul]
    exact add_le_add (hd τ _) (hd τ _)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CasimirEqGelfandValueOfInfinitesimalCharacterStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_eq_gelfandValue_of_infinitesimalCharacter : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ χ : Fin n → ℂ, GlobalTheory.Dec.HasInfChar ε χ σ → ∀ v, casimir R.HK.act v = GlobalTheory.Dec.gelfVal χ 2 • v := by
  first | exact @GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar | exact GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar | (intros; apply GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthogonalAllThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ q : WO S T → ℂ, Continuous q → (∀ γ w, q (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * q w) → (∀ f, IsThetaFunO ψ S T f → ∫ w in 𝓕, q w * star (f w) ∂μ = 0) → q = 0 := by
  first | exact @GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta | exact GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta | (intros; apply GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumnsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionTwistData_chainColumns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  first | exact @GlobalTheory.TwBridgeInhab.exists_twData | exact GlobalTheory.TwBridgeInhab.exists_twData | (intros; apply GlobalTheory.TwBridgeInhab.exists_twData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCongruenceModulusIdelicCharacterTrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitAll.char_trivial_modSet | exact GlobalTheory.HeckeSplitAll.char_trivial_modSet | (intros; apply GlobalTheory.HeckeSplitAll.char_trivial_modSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finPartOne_mul_inv_mem_heckeSplitCongruence : ∀ (D : D7) (N : ℕ), 0 < N → ∀ x : (AE D)ˣ, ∃ z : (AE D)ˣ, finPart D (z : AE D) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitAll.grpH D N := by
  first | exact @GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | exact GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | (intros; apply GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem <;> assumption)
end

