import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunction
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anFib_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, FrOver d y₂ y → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → ∃ A₂ : AnFib X bas idx e x L y₂, (∀ θ, A.Reads 1 y.s θ → A₂.Reads 1 y₂.s θ) ∧ ∃ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk₂ ∧ A₂.Marked mk₂ ∧ MarkOver l d.l₂ L mk mk₂ := by
  first | exact @GlobalTheory.Dict.Lift.anFib_lift | exact GlobalTheory.Dict.Lift.anFib_lift | (intros; apply GlobalTheory.Dict.Lift.anFib_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFibre_unitFrame_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  first | exact @GlobalTheory.Dict.uw_anFib | exact GlobalTheory.Dict.uw_anFib | (intros; apply GlobalTheory.Dict.uw_anFib <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r : ℕ) (X : Data E r) (D : SW.Level X) (hn : r ≤ n), r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (x0 : Fin n → Dw.La), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → ∀ q, algebraMap d.c₂.F ℂ (d.w x0 q) = t * ∑ᶠ cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸ (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _, datF D (Mfr l) hn (cl.out : Matrix (Fin n) (Fin r) E) * cexp (-(2 * Real.pi * I * ((∑ b, EF X ((cl.out : Matrix (Fin n) (Fin r) E) b) (Y q b) : ℚ) : ℂ))) := by
  first | exact @GlobalTheory.Dict.CoverFourier.w_eq_sum | exact GlobalTheory.Dict.CoverFourier.w_eq_sum | (intros; apply GlobalTheory.Dict.CoverFourier.w_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsThetaEqOfTranslationInvariantMultipleStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_eq_of_translation_invariant_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (N : ℕ), 0 < N → ∀ θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ θ → (∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ v : WR X n, cexp (-(π * I * (EFR X v (N • embR X y) : ℝ))) * (gaussR X bas idx x (zR X idx x (v + N • embR X y)) * θ (zR X idx x (v + N • embR X y))) = gaussR X bas idx x (zR X idx x v) * θ (zR X idx x v)) → ∃ φ : TF n g, IsSB φ ∧ ∀ z, thA X bas idx φ x z = θ z := by
  first | exact @GlobalTheory.Ker.Onto.exists_thA_eq | exact GlobalTheory.Ker.Onto.exists_thA_eq | (intros; apply GlobalTheory.Ker.Onto.exists_thA_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_generator_isThetaLevelOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  first | exact @GlobalTheory.Dict.isTheta1_of_reads_generator | exact GlobalTheory.Dict.isTheta1_of_reads_generator | (intros; apply GlobalTheory.Dict.isTheta1_of_reads_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhases
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.Proj

section General

variable {α β : Type} [Fintype α] [Fintype β]

theorem ip_smul_smul {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hlin := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.1 (a * conj b)
  have hfun : (fun x => (a • φ) x * conj ((b • ψ) x)) = (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  show haar (fun x => (a • φ) x * conj ((b • ψ) x)) = a * conj b * haar (φ * fun x => conj (ψ x))
  rw [hfun, hlin]

theorem ip_conj {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ip ψ φ = conj (ip φ ψ) := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hc := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.2.1
  have hfun : (fun x => ψ x * conj (φ x)) = fun x => conj ((φ * fun x => conj (ψ x)) x) := by
    funext x
    simp only [Pi.mul_apply, map_mul, Complex.conj_conj]
    ring
  show haar (fun x => ψ x * conj (φ x)) = conj (haar (φ * fun x => conj (ψ x)))
  rw [hfun, hc]

theorem ph_ip [DecidableEq β] {φ ψ : Matrix α β ℚ → ℂ} (hφ : PV φ) (hψ : PV ψ) : Ph (ip φ ψ) := by
  have sφ : Shape φ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β φ).2.1 hφ
  have sψ : Shape ψ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β ψ).2.1 hψ
  have sψc : Shape (fun x => conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β ψ sψ).1
  have spr : Shape (fun x => φ x * conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β φ sφ).2.2 _ sψc
  exact GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase α β _ spr

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem isVac_smul {w : E} {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {v : TF n g}
    (hv : IsVac X bas w A v) {u : ℂ} (hu : ‖u‖ = 1) : IsVac X bas w A (u • v) := by
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨hsb, hip, hfix⟩ := hv'
  unfold IsVac
  refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hsb hsb).2.1 u, ?_, ?_⟩
  · rw [ip_smul_smul hsb hsb, hip, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  · intro y hy
    have hlin : heisG X bas y (u • v) = u • heisG X bas y v := by
      funext x
      simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, smul_comm, hfix y hy]

theorem unitv_smul {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) (c : ℂ) :
    unitv (c • v) = (((‖c‖ : ℝ) : ℂ)⁻¹ * c) • v := by
  have hc : ip (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip_smul_smul hv hv, h1, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold unitv
  rw [hc, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg c), smul_smul]

theorem proj_phases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Λ ∈ Vset E n 1, IsVac X bas w (tens Λ L) (unitv (projA X bas w (tens Λ L) v)) ∧ PV (u • unitv (projA X bas w (tens Λ L) v)) ∧ projA X bas w (tens Λ L) v = ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • unitv (projA X bas w (tens Λ L) v) := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 L hL v hv
  have hstd : stdL E n ∈ Vset E n 1 := GlobalTheory.SW.Base.stdL_mem_Vset n 1
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨A, ε, hA⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL (stdL E n) hstd v hv
  obtain ⟨u, hu1, hupv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) v).2.2.1 A ε hA
  refine ⟨u, hu1, fun Λ hΛ => ?_⟩
  have H := GlobalTheory.T.tensorLattice_vacua_exist_unique E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ
  obtain ⟨vΛ, hvΛ⟩ := H.1
  have hvΛ' := hvΛ
  unfold IsVac at hvΛ'
  have hproj : projA X bas w (tens Λ L) v = ip v vΛ • vΛ := H.2.2.1 v hv'.1 vΛ hvΛ
  have hnorm := H.2.2.2 L hL (stdL E n) hstd vΛ v hvΛ hv
  rw [(GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ).2.2.2.2.2 (stdL E n) hstd,
    ip_conj hv'.1 hvΛ'.1, Complex.norm_conj] at hnorm
  have hsq := congrArg Real.sqrt hnorm
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at hsq
  have hc0 : ‖ip v vΛ‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsq
    exact zero_ne_one hsq
  have hunit : unitv (projA X bas w (tens Λ L) v) = (((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ) • vΛ := by
    rw [hproj]
    exact unitv_smul hvΛ'.1 hvΛ'.2.1 _
  have he : ‖((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hunit]
    exact isVac_smul hvΛ he
  · obtain ⟨A', ε', hA'⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL Λ hΛ vΛ hvΛ
    obtain ⟨u', hu'1, hu'pv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) vΛ).2.2.1 A' ε' hA'
    have hph : Ph (ip (u • v) (u' • vΛ)) := ph_ip hupv hu'pv
    have hu'u : conj u' * u' = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu'1]
      simp
    have heq : u • unitv (projA X bas w (tens Λ L) v) =
        (ip (u • v) (u' • vΛ) * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹) • (u' • vΛ) := by
      rw [hunit, ip_smul_smul hv'.1 hvΛ'.1, smul_smul, smul_smul]
      congr 1
      linear_combination (-(u * ip v vΛ * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹)) * hu'u
    rw [heq]
    exact (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) (u' • vΛ)).2.2.2.1 hu'pv _
      (Ph.mul hph (Ph.inv ((GlobalTheory.T.complex_phase_calculus_rootOfUnity).2.2.1 ‖ip v vΛ‖)))
  · have hC : ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ) *
        ((‖ip v vΛ‖ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
    rw [hunit, hproj, smul_smul, ← _root_.mul_assoc, ← _root_.mul_inv, hC, inv_one, _root_.one_mul]

end GlobalTheory.Phase.Proj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, ∀ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' → (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' → (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' → ∃ t : ℂ, t ≠ 0 ∧ ∀ L ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ ∑ y ∈ s, D.dat hn y • heisG X bas (h * y) (unitv (projA X bas D.w (tens Λ'' (D.sh L)) (v₀ L))) = t • phiF bas D 𝔐 hn v₀ L Λ' := by
  first | exact @GlobalTheory.Dict.SumFree.sum_free | exact GlobalTheory.Dict.SumFree.sum_free | (intros; apply GlobalTheory.Dict.SumFree.sum_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_heisenberg_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  first | exact @GlobalTheory.Dict.thA_heisG_hAct | exact GlobalTheory.Dict.thA_heisG_hAct | (intros; apply GlobalTheory.Dict.thA_heisG_hAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBound
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PhiNorm

section Product

variable {κ ι α : Type} [Fintype κ] [Fintype ι]

theorem sum_left (s : Finset α) (f : α → Matrix κ ι ℚ → ℂ) {ψ : Matrix κ ι ℚ → ℂ}
    (hs : ∀ a ∈ s, IsSB (f a)) (h' : IsSB ψ) :
    IsSB (∑ a ∈ s, f a) ∧ SW.ip (∑ a ∈ s, f a) ψ = ∑ a ∈ s, SW.ip (f a) ψ := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨isSB_zero, ?_⟩
    have := TensVac.ip_smul_left 0 h' h'
    simpa using this
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun φ hφ => hs φ (Finset.mem_insert_of_mem hφ)
    have h3 := hs a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, TensVac.ip_add_left h3 h1 h', h2]
    exact ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h3 h1).1, rfl⟩

theorem ip_sum_diag (s : Finset α) (f f' : α → Matrix κ ι ℚ → ℂ) (hf : ∀ a ∈ s, IsSB (f a))
    (hf' : ∀ a ∈ s, IsSB (f' a)) (h : ∀ a ∈ s, ∀ b ∈ s, SW.ip (f a) (f' b) ≠ 0 → a = b) :
    SW.ip (∑ a ∈ s, f a) (∑ a ∈ s, f' a) = ∑ a ∈ s, SW.ip (f a) (f' a) := by
  rw [(sum_left s f hf (sum_left s f' hf' isSB_zero).1).2]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [TensVac.ip_conj (sum_left s f' hf' isSB_zero).1 (hf a ha), (sum_left s f' hf' (hf a ha)).2,
    map_sum, Finset.sum_eq_single_of_mem a ha, ← TensVac.ip_conj (hf' a ha) (hf a ha)]
  intro b hb hba
  rw [← TensVac.ip_conj (hf' b hb) (hf a ha)]
  by_contra h0
  exact hba (h a ha b hb h0).symm

end Product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem pair_int (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    {v v' : TF n g} (hv : IsSB v) (hv' : IsSB v') {δ y y' : Matrix (Fin n) (Fin r) E}
    (h : epsW X w δ • heisG X bas δ v = v) (h' : epsW X w δ • heisG X bas δ v' = v')
    (h0 : SW.ip (heisG X bas y v) (heisG X bas y' v') ≠ 0) :
    ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k := by
  have H := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have key : ∀ (y : Matrix (Fin n) (Fin r) E) (v : TF n g), IsSB v →
      epsW X w δ • heisG X bas δ v = v → epsW X w δ • heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) • heisG X bas y v := by
    intro y v hv h
    have e : heisG X bas δ (heisG X bas y v) =
        cexp (-(2 * π * I * ((∑ k, EF X (δ k) (y k) : ℚ) : ℂ))) •
          heisG X bas y (heisG X bas δ v) := by
      rw [(H δ v hv).2.2.1 y, (H y v hv).2.2.1 δ, smul_smul, ← Complex.exp_add, add_comm y,
        TensVac.sumEF_swap hs δ y]
      congr 2
      push_cast
      ring
    rw [e, smul_comm, ← TensVac.heisG_smul, h]
  have h1 := (H y v hv).1
  have h2 := (H y' v' hv').1
  have h3 := (H δ _ h1).2.2.2.1 _ h2
  have h4 : SW.ip (epsW X w δ • heisG X bas δ (heisG X bas y v))
      (epsW X w δ • heisG X bas δ (heisG X bas y' v')) =
      SW.ip (heisG X bas y v) (heisG X bas y' v') := by
    rw [TensVac.ip_smul_left _ (H δ _ h1).1 (TensVac.sb_smul _ (H δ _ h2).1),
      TensVac.ip_smul_right _ (H δ _ h1).1 (H δ _ h2).1, ← mul_assoc, TensVac.epsW_mul_conj,
      one_mul, h3]
  rw [key y v hv h, key y' v' hv' h', TensVac.ip_smul_left _ h1 (TensVac.sb_smul _ h2),
    TensVac.ip_smul_right _ h1 h2, ← mul_assoc, mul_left_eq_self₀, or_iff_left h0,
    ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_eq_one_iff] at h4
  obtain ⟨k, hk⟩ := h4
  refine ⟨-k, ?_⟩
  have e : ∑ i, EF X (δ i) ((y - y') i) = ∑ i, EF X (δ i) (y i) - ∑ i, EF X (δ i) (y' i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (y - y') i = y i - y' i := rfl
    simp only [TensLat.EF_eq_bilin, this, map_sub]
  rw [e]
  simp only [map_neg, map_mul, conj_ofReal, conj_I, map_ratCast, map_ofNat] at hk
  have hπ : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  apply Rat.cast_injective (α := ℂ)
  apply mul_left_cancel₀ hπ
  push_cast at hk ⊢
  linear_combination -hk

theorem coprime_cc {𝔪 : Ideal (𝓞 E)} {t t' : 𝓞 E} (ht : (t' : E) = cc (t : E))
    (h : IsCoprime (Ideal.span {t}) (conjI 𝔪)) : IsCoprime (Ideal.span {t'}) 𝔪 := by
  let c : 𝓞 E → 𝓞 E := fun a => ⟨cc (a : E), Base.isIntegral_cc a.isIntegral_coe⟩
  have hc : ∀ a, ((c a : 𝓞 E) : E) = cc (a : E) := fun _ => rfl
  have hm : ∀ m ∈ conjI 𝔪, c m ∈ 𝔪 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have : c x = b := by ext; rw [hc, e]; simp [cc]
      rwa [this]
    | zero =>
      have : c 0 = 0 := by ext; rw [hc]; simp [cc]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : c (x + y) = c x + c y := by ext; push_cast; simp [hc, cc]
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : c (a • x) = c a * c x := by ext; push_cast; simp [hc, cc]
      rw [this]; exact Ideal.mul_mem_left _ _ hx
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  refine Ideal.isCoprime_iff_exists.2 ⟨c u * t', Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, c b,
    hm b hb, ?_⟩
  have := congrArg (fun a : 𝓞 E => cc (a : E)) hab
  ext
  push_cast at this ⊢
  simpa [hc, ht, cc] using this

omit [IsCMField E] in

theorem smul_mem_smul {𝔪 : Ideal (𝓞 E)} {L L' : Lt E r} {t : 𝓞 E} (h : ∀ v ∈ L, t • v ∈ L')
    {v : Fin r → E} (hv : v ∈ 𝔪 • L) : t • v ∈ 𝔪 • L' := by
  refine Submodule.smul_induction_on hv (fun a ha u hu => ?_) fun a b ha hb => ?_
  · rw [smul_comm]; exact Submodule.smul_mem_smul ha (h u hu)
  · rw [smul_add]; exact add_mem ha hb

theorem cong_of_pair (D : Level X) {M : ℕ} (hM : (M : 𝓞 E) ∈ D.𝔪) {L L' : Lt E r}
    (hL : L ∈ D.lats) (hL' : L' ∈ D.lats) (hS : SelfD X (D.sh L)) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {y y' : Matrix (Fin n) (Fin r) E}
    (h : ∀ δ ∈ tens Λ (D.sh L), δ ∈ tens Λ (D.sh L') →
      ∃ k : ℤ, ∑ i, EF X (δ i) ((y - y') i) = k) (k : Fin n) : Cong X D.𝔪 (y k) (y' k) := by
  obtain ⟨-, s, hs, hs1, -⟩ := hL
  obtain ⟨-, s', hs', -, hs2⟩ := hL'
  obtain ⟨N, -, hN, -, hN2⟩ := hΛ.2.2
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 D.cop
  let t : 𝓞 E := ⟨cc ((s' * s : 𝓞 E) : E), Base.isIntegral_cc (s' * s).isIntegral_coe⟩
  have ht : (t : E) = cc ((s' * s : 𝓞 E) : E) := rfl
  have h1 : ∀ v ∈ D.sh L, (s' * s) • v ∈ D.sh L' := fun v hv c hc => by
    rw [smul_comm]
    exact smul_mem_smul (fun u hu => by rw [mul_smul]; exact hs2 _ (hs1 u hu)) (hv c hc)
  have hctr : ∀ (c : E) (d : Matrix (Fin n) (Fin r) E) (v : Fin n → E),
      TensLat.ctr (c • d) v = c • TensLat.ctr d v := fun c d v => by
    funext j
    simp [TensLat.ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]
  have h2 : (t : E) • (y - y') ∈ tens Λ (D.sh L) := by
    refine (TensLat.tens_selfDual hΛ hS _).2 fun δ hδ => ?_
    obtain ⟨m, hm⟩ := h (((s' * s : 𝓞 E) : E) • δ)
      (TensLat.smul_mem_tens hΛ (s' * s).isIntegral_coe hδ) (by
        rw [TensLat.mem_tens_iff hΛ] at hδ ⊢
        intro v hv
        rw [hctr]
        exact h1 _ (hδ v hv))
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, ← hm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensLat.EF_swap]
    exact congrArg Neg.neg (TensLat.EF_smul X _ _ _).symm
  have h3 := (TensLat.mem_tens_iff hΛ _ _).1 h2 _
    (hN2 (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩))
  have h4 : TensLat.ctr ((t : E) • (y - y')) ((N : E) • (Pi.single k 1 : Fin n → E)) =
      ((N : 𝓞 E) * t) • (y k - y' k) := by
    rw [TensLat.ctr, Finset.sum_eq_single k]
    · funext j
      change _ = (((N : 𝓞 E) * t : 𝓞 E) : E) * (y k j - y' k j)
      simp [cc, mul_assoc, Algebra.smul_def]
    · intro j _ hj; simp [hj, cc]
    · simp
  rw [h4] at h3
  refine ⟨s * (b * (N * t)), ?_, ?_⟩
  · simp only [← Ideal.span_singleton_mul_span_singleton]
    refine hs.of_mul_right_left.mul_left (IsCoprime.mul_left ?_ (IsCoprime.mul_left ?_ ?_))
    · exact Ideal.isCoprime_iff_exists.2 ⟨b, Ideal.mem_span_singleton_self b, a, ha,
        (add_comm _ _).trans hab⟩
    · obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hN
      refine Ideal.isCoprime_iff_exists.2 ⟨p * N, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, q * M,
        Ideal.mul_mem_left _ _ hM, ?_⟩
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
    · refine coprime_cc ht ?_
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact hs'.of_mul_right_right.mul_left hs.of_mul_right_right
  · rw [mul_smul, mul_smul]
    exact smul_mem_smul hs1 (h3 b hb)

theorem eq_rpow {a : ℝ} {m n : ℕ} (ha : 0 ≤ a) (h : ((m ^ n : ℕ) : ℝ) * a ^ 2 = 1) :
    a = (m : ℝ) ^ (-(n : ℝ) / 2) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [← pow_left_inj₀ ha (Real.rpow_nonneg hm _) two_ne_zero, ← Real.rpow_natCast (_ ^ _),
    ← Real.rpow_mul hm, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
    Real.rpow_neg hm, Real.rpow_natCast]
  exact eq_inv_of_mul_eq_one_right (by exact_mod_cast h)

theorem phi_norm_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L Λ) = (Nat.card D.J : ℂ) ∧ ∀ L' ∈ D.lats, ‖SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ)‖ ≤ (Nat.card D.J : ℝ) * (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) := by
  intro E _ _ _ r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  have H := (heisG_laws E r X g bas idx n hs hev).2.2.2
  have P := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM0 hM v₀ hv₀
  have Lv := (GlobalTheory.T.level_structure_properties E r X g bas idx n hs hev D hn).2.2.2.1
  have hv := (P L hL Λ hΛ).2.1
  have main : ∀ L' ∈ D.lats, SW.ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) =
      (Nat.card D.J : ℂ) * SW.ip (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)))
        (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L'))) := by
    intro L' hL'
    have hv' := (P L' hL' Λ hΛ).2.1
    obtain ⟨s, hcard, hsy, e, e'⟩ := (P L hL Λ hΛ).2.2.1 L' hL'
    rw [e, e', ip_sum_diag s _ _ (fun y _ => TensVac.sb_smul _ (H y _ hv.1).1)
      (fun y _ => TensVac.sb_smul _ (H y _ hv'.1).1), ← hcard, ← nsmul_eq_mul,
      ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y _ hv'.1).1, ← mul_assoc, Complex.mul_conj',
        (hsy y hy).2.1, (H y _ hv.1).2.2.2.1 _ hv'.1]
      simp
    · intro y hy y' hy' h0
      rw [TensVac.ip_smul_left _ (H y _ hv.1).1 (TensVac.sb_smul _ (H y' _ hv'.1).1),
        TensVac.ip_smul_right _ (H y _ hv.1).1 (H y' _ hv'.1).1] at h0
      refine (hsy y hy).2.2 y' hy' (cong_of_pair D hM hL hL' (Lv L hL).1 hΛ fun δ hδ hδ' => ?_)
      exact pair_int idx hs hev hv.1 hv'.1 (hv.2.2 δ hδ) (hv'.2.2 δ hδ')
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
  refine ⟨by rw [main L hL, hv.2.1, mul_one], fun L' hL' => ?_⟩
  have hv' := (P L' hL' Λ hΛ).2.1
  have h1 := (TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr _ (Lv L hL).1 M Λ
    hΛ).2.2.2 _ (Lv L' hL').1 Λ hΛ _ _ hv hv'
  rw [((TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w D.w_int D.w_tr _
    (Lv L hL).1 M Λ hΛ).2.2.2.2.1 _ (Lv L' hL').1).1, (Lv L hL).2.2.1 L' hL'] at h1
  rw [main L' hL', norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Nat.cast_nonneg _)
  exact eq_rpow (norm_nonneg _) h1

end GlobalTheory.SW.PhiNorm
end

