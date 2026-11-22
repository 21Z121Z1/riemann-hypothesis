import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharSeparatesIntegralFiniteAdeles
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdCharSep

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_of_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1) : ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
    push_cast
    exact mul_right_cancel₀ hne hn
  exact_mod_cast h2

theorem psi_of_trace_int {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ∃ z : ℤ, Algebra.trace ℚ F x = z) : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 := by
  obtain ⟨z, hz⟩ := h
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, hz, Complex.exp_eq_one_iff]
  exact ⟨z, by push_cast; ring⟩

theorem psi_int_mul {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (s : F)
    (hs : ∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z)
    (w : Af F) (hw : ∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (w * algebraMap F (Af F) s)) = 1 :=
  GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 s (fun a => psi_of_trace_int hψ _ (hs a)) w hw

theorem mem_of_dual (k : F) (h : ∀ s : F, (∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z) →
    ∃ z : ℤ, Algebra.trace ℚ F (k * s) = z) : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = k := by
  have h1 : k ∈ FractionalIdeal.dual ℤ ℚ
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
    rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ (GlobalTheory.AdLat.one_ne_zero_fracIdeal F))]
    intro s hs
    rw [FractionalIdeal.mem_dual (GlobalTheory.AdLat.one_ne_zero_fracIdeal F)] at hs
    obtain ⟨z, hz⟩ := h s (fun a => by
      obtain ⟨y, hy⟩ := hs (a : F) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      refine ⟨y, ?_⟩
      rw [Algebra.traceForm_apply] at hy
      rw [mul_comm, ← hy]
      simp)
    exact ⟨z, by rw [Algebra.traceForm_apply, hz]; simp⟩
  rw [FractionalIdeal.dual_dual] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem exists_sep : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := by
  intro F _ _ ψ hψ b hb
  by_contra H
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) b
  have hbk : b = algebraMap F (Af F) k + (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) := by abel
  obtain ⟨o, ho⟩ := mem_of_dual k (fun s hs => by
    have hb1 : ψ (pairA F 0 (b * algebraMap F (Af F) s)) = 1 := by
      by_contra hne
      exact H ⟨s, hne, fun w hw => psi_int_mul hψ s hs w hw⟩
    have hc1 := psi_int_mul hψ s hs _ hk
    have e : pairA F 0 (b * algebraMap F (Af F) s) = pairA F 0 (algebraMap F (Af F) (k * s)) +
        pairA F 0 ((b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s) := by
      refine Prod.ext (add_zero 0).symm ?_
      show b * algebraMap F (Af F) s = algebraMap F (Af F) (k * s) +
        (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s
      rw [map_mul]
      ring
    rw [e, AddChar.map_add_eq_mul, hc1, mul_one] at hb1
    exact trace_int_of_psi hψ _ hb1)
  apply hb
  intro v
  rw [hbk]
  refine add_mem ?_ (hk v)
  show ((k : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [← ho]
  exact GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v o

end GlobalTheory.StdCharSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModuleMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.CoinvLine

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hψ : IsStdChar D ψ (-1)) [Nonempty D.what₂.Tau] {W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X) {Ψ : WO W₁ X → ℂ}
    (hΨ : Ψ ∈ algF ψ θ false A₁ B) : IsThetaFunO ψ W₁ X Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn false A₁) B hf).1 (Classical.arbitrary _) P
  | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ W₁ X
  | add x y _ _ hx hy => exact Formalism.IndefR.Fock.CCR.theta_add hx hy
  | smul c x _ hx => exact Formalism.IndefR.Fock.CCR.theta_smul hx c

theorem coinv_kills_line_deriv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  intro _ D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ _ _ hM Vs hJ γ hγ Ψ hΨ Ψ₁ _ hder
  have hω : IsWeilDatumO ψ W₁ X α (α / β) ωB := hM.weilB
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  obtain ⟨g, h1, h2, h3, h4⟩ := GlobalTheory.OmegaDer.exists_line W₁ hc Vs hJ γ hγ
  have hg : ∀ t : ℝ, GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ (γ (Multiplicative.ofAdd t)) = g t :=
    fun t => by rw [← h1 t]; exact (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hJ).left_inv (g t)
  obtain ⟨Z, hZ⟩ := GlobalTheory.OmegaDer.exists_expInf hθ W₁ g h2 h3 h4

  have hst := fun τ => hM.mapB.stabM.2 τ (Z τ).1 (Z τ).2 Ψ hΨ
  choose Ψ' hΨ' hd using hst
  have hk : ∀ τ, p' (Ψ' τ) = 0 := fun τ => hM.mapB.invl τ (Z τ).1 (Z τ).2 Ψ hΨ (Ψ' τ) (hΨ' τ) (hd τ)
  have hsum : Ψ₁ = ∑ τ, Ψ' τ := by
    funext z
    rw [Finset.sum_apply]
    have e1 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
        (γ (Multiplicative.ofAdd t)), 1) Ψ z) = fun t : ℝ => ωB (GlobalTheory.SmoothForms.expInf θ W₁ (t • Z), 1) Ψ z := by
      funext t; rw [hg t, hZ t]
    have hz := hder z
    rw [e1] at hz
    rcases isEmpty_or_nonempty D.what₂.Tau with h0 | h0
    · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
      simp only [e] at hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact hz.unique (hasDerivAt_const _ _)
    · let 𝒮 : Set (GA D W₁ → ℂ) := {φ | ∃ f z, IsThetaFunO ψ W₁ X f ∧ φ = fun g => ωB (g, 1) f z}
      have hΘ := isThetaFunO_of_mem_algF hθ hψ A₁ B hΨ
      refine hz.unique (GlobalTheory.OmegaDer.der_sum hθ 𝒮 ?_ ?_ ⟨Ψ, z, hΘ, rfl⟩ Z (fun τ => Ψ' τ z) fun τ => hd τ z)
      · rintro _ ⟨f, z, hf, rfl⟩
        exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
      · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
        obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
        refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
        have := h (g, 1) z
        simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun τ _ => hk τ

end GlobalTheory.CoinvLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationCoefficientsInvariantStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_coefficients_invariant : GlobalTheory.Published.LabesseWaldspurger → ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ Tr, ∃ C Dd : Finset (SV (wittIndex V)) → GA D V → ℂ, (∀ Q ∈ parF (aP P) ∅, Continuous (C Q) ∧ (∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ y, C Q (m * y) = C Q y) ∧ ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ y, C Q (n * y) = C Q y) ∧ (∀ z, Dd ∅ z = 1) ∧ (∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (y * z) : ℂ) = ∑ Q ∈ parF (aP P) ∅, C Q y * Dd Q z) ∧ ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ x, weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (m * x) = weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x := by
  first | exact @GlobalTheory.weight_split_places | exact GlobalTheory.weight_split_places | (intros; apply GlobalTheory.weight_split_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitaryEmbeddingProperties

def ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h : Matrix (Fin r) (Fin r) R) : Matrix (Fin n) (Fin n) R :=
  1 + P * (h - 1) * Q

section Gen

variable {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)

theorem ex_mul_P (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * P = P * h := by
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem ex_mul_N (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * (1 - P * Q) = 1 - P * Q := by
  have e : Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul, sub_self]
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (P * (h - 1)), e, Matrix.mul_zero, add_zero]

theorem ex_mul (hQP : Q * P = 1) (a b : Matrix (Fin r) (Fin r) R) : ex P Q (a * b) = ex P Q a * ex P Q b := by
  have e3 : P * (a - 1) * Q * (P * (b - 1) * Q) = P * ((a - 1) * (b - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have e4 : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [ex, ex, ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, e3, e4]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

theorem ex_one : ex P Q 1 = 1 := by simp [ex]

theorem ex_map {R' : Type} [CommRing R'] (φ : R →+* R') (h : Matrix (Fin r) (Fin r) R) :
    (ex P Q h).map φ = ex (P.map φ) (Q.map φ) (h.map φ) := by
  simp only [ex, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

end Gen

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

def qM (d : HermitianOrthogonalExtensionData A B c ε) : Matrix (Fin A.rank) (Fin B.rank) D.host.E :=
  A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram)

theorem qM_mul (d : HermitianOrthogonalExtensionData A B c ε) : qM d * frameMat B A d.ι = 1 := by
  rw [qM, Matrix.mul_assoc, GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom,
    Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit]

theorem qM_mul_map {R : Type} [CommRing R] (φ : D.host.E →+* R) (d : HermitianOrthogonalExtensionData A B c ε) :
    (qM d).map φ * (frameMat B A d.ι).map φ = 1 := by
  rw [← Matrix.map_mul, qM_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem unitaryEmbedding_matrix_formula (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) :
    (matHom B (stabilizerEmbedding d h)).1 = ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (matHom A h).1 := by
  have hr := (embRel_iff d h _).2 rfl
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * qM d with hN
  have hC : C * N = 0 := by
    rw [hN, qM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B (stabilizerEmbedding d h)).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hr.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  have hNm : N.map (incA D) = (1 : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) -
      HMul.hMul (P.map (incA D)) ((qM d).map (incA D)) := by
    rw [hN, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.AutFunCounterexample.split_gen (incA D) P (qM d) _ _ ?_ ?_
  · rw [h1, hNm, ex_mul_N _ _ (qM_mul_map _ d)]
  · rw [hr.1, ex_mul_P _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_mul (d : HermitianOrthogonalExtensionData A B c ε) (g h : GA D A) : stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h := by
  apply GlobalTheory.AutFunCounterexample.GA_ext
  rw [map_mul, Units.val_mul, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, map_mul, Units.val_mul,
    ex_mul _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_rational (d : HermitianOrthogonalExtensionData A B c ε) (γ : GA D A) (hγ : γ ∈ GQ A) : stabilizerEmbedding d γ ∈ GQ B := by
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have q2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram = A.gram * qM d := by
    rw [qM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul]
  set P := frameMat B A d.ι
  set Q := qM d
  have q3 : Q * P = 1 := qM_mul d
  have q1 : B.gram * P = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Q * A.gram := by
    have := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) q2
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT,
      GlobalTheory.AutFunCounterexample.gram_herm] at this
  let γ' : GL (Fin B.rank) D.host.E := ⟨ex P Q γE, ex P Q (γE⁻¹ : GL (Fin A.rank) D.host.E),
    by rw [← ex_mul _ _ q3, Units.mul_inv, ex_one], by rw [← ex_mul _ _ q3, Units.inv_mul, ex_one]⟩
  have hu : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram :=
    GlobalTheory.AutFunCounterexample.ext_unitary _ B.gram A.gram P Q q1 q2 q3 _ hγE
  refine Subgroup.mem_subgroupOf.2 ⟨γ', hu, Units.ext ?_⟩
  have hA : (matHom A γ).1 = (γE : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  show (ex P Q γE).map (incA D) = (matHom B (stabilizerEmbedding d γ)).1
  rw [unitaryEmbedding_matrix_formula, hA, ex_map]

set_option synthInstance.maxHeartbeats 400000 in

theorem continuous_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) : Continuous (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hf : ∀ {f : GA D A → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}, Continuous f →
      Continuous fun h => ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (f h) := fun hc =>
    continuous_const.add ((continuous_const.matrix_mul (hc.sub continuous_const)).matrix_mul continuous_const)
  have hv : Continuous fun h : GA D A => (matHom A h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun h : GA D A => (matHom A h⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (unitaryEmbedding_mul d)
  have hc : Continuous fun h => matHom B (stabilizerEmbedding d h) := by
    refine Units.continuous_iff.2 ⟨(hf hv).congr fun h => (unitaryEmbedding_matrix_formula d h).symm, (hf hi).congr fun h => ?_⟩
    have e : (stabilizerEmbedding d h)⁻¹ = stabilizerEmbedding d h⁻¹ := (map_inv φ h).symm
    rw [← map_inv (matHom B), e, unitaryEmbedding_matrix_formula]
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig B.gram) hc fun h => (stabilizerEmbedding d h).2

theorem unitaryEmbedding_continuous_hom_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B :=
  fun d => ⟨continuous_unitaryEmbedding d, unitaryEmbedding_mul d, unitaryEmbedding_rational d⟩

end GlobalTheory.UnitaryEmbeddingProperties
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEquivEqSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.BrUnique

variable {ι : Type} [Fintype ι] {N n : ℕ}

def uGL (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin n) ℂ := fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)

def diagU (hN : N = n + 1) (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin N) ℂ :=
  fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))

theorem invTrK_invTrK {K : Type} [Field K] (g : ι → GL (Fin n) K) : invTrK (invTrK g) = g := by
  funext τ
  apply Units.ext
  have hu : IsUnit ((g τ : Matrix (Fin n) (Fin n) K)).det := (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit
  simp [invTrK, inside₂, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]

theorem pairBK_rhoK (σ : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (x y : VV ℂ σ) :
    pairBK σ (rhoK σ g x) (rhoK σ (invTrK g) y) = pairBK σ x y := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]
  have h := pairingBInvariantK_holds ℂ ι n σ (invTrK g) x.1 y.1
  rwa [invTrK_invTrK] at h

theorem unitaryEquiv_eq_smul (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ)) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v)) :
    ∃ c : ℂ, φ = c • Br.brStd hN Λ σ :=
  GlobalTheory.T.exists_eq_smul_brStd_of_equivariant hN hn Λ σ hI hS φ (GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace hN Λ σ φ hφ)

theorem brPair_unique (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ))
    (B : VV ℂ Λ →ₗ[ℂ] (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] ℂ)
    (hB : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ) (f : VV ℂ fun τ => (σ τ).dual),
      B (rhoK Λ (diagU hN u) v) (rhoK (fun τ => (σ τ).dual) (uGL u) f) = B v f) :
    ∃ c : ℂ, B = c • GlobalTheory.FunObj.brPair σ hN Λ := by
  haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)
  have hnd := pairingBNondegenerate_holds ℂ ι n σ
  let φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ :=
    (LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ B.compl₂ (GlobalTheory.FunObj.funEquiv σ).toLinearMap
  have hp : ∀ v y, pairBK σ (φ v) y = B v (GlobalTheory.FunObj.funEquiv σ y) := fun v y => by
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.compl₂_apply]
  have hinv : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) v F,
      B (rhoK Λ (diagU hN u) v) F = B v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F) := fun u v F => by
    have h := hB u v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  have hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v) := fun u v => by
    refine sub_eq_zero.1 (hnd.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hp, hinv]
    obtain ⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK (uGL u)) y' :=
      ⟨rhoK σ (invTrK (uGL u))⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [pairBK_rhoK, hp, GlobalTheory.FunObj.funEquiv_rhoK, ← Module.End.mul_apply, ← map_mul, invTrK_invTrK, inv_mul_cancel,
      map_one, Module.End.one_apply]
  obtain ⟨c, hc⟩ := unitaryEquiv_eq_smul hN hn hI hS φ hφ
  refine ⟨c, LinearMap.ext₂ fun v f => ?_⟩
  have e : f = GlobalTheory.FunObj.funEquiv σ (GlobalTheory.FunObj.covOf σ f) := by rw [GlobalTheory.BrRat.covOf_eq, LinearEquiv.apply_symm_apply]
  rw [e, ← hp, hc, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    ← e]
  simp only [GlobalTheory.FunObj.brPair, LinearMap.compl₁₂_apply]

end GlobalTheory.BrUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockRealMove

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) {x : GA D V} (hx : x ∈ GfC V) :
    compAt θ τ (mt V x) = 1 :=
  GlobalTheory.LocWeil.CompactPart.infMat_of_fin V (θ τ) hx

theorem om_fin_fockVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x ∈ GfC S, ∀ y ∈ GfC T, IsThetaFunO ψ S T (om (x, y) f) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x, y) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sT f hf hvac x hx y hy
  refine ⟨hW.om_pres _ _ hf, fun τ z => ?_⟩
  have hS : sS τ * compAt θ τ (mt S x) = compAt θ τ (mt S x) * sS τ := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, Matrix.mul_one, Matrix.one_mul]
  have hT : sT τ * compAt θ τ (mt T y) = compAt θ τ (mt T y) * sT τ := by
    rw [compAt_mt_of_mem_GfC θ τ T hy, Matrix.mul_one, Matrix.one_mul]
  have key := GlobalTheory.FockMove.om_annih hW hθ x y τ hS hT (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) hf
  rw [hvac τ, map_zero] at key
  have e : compAt θ τ (mt T y) * (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) * compAt θ τ (mt S x⁻¹) = z := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, compAt_mt_of_mem_GfC θ τ S (inv_mem hx),
      compAt_mt_of_mem_GfC θ τ T hy, compAt_mt_of_mem_GfC θ τ T (inv_mem hy)]
    simp
  rw [e] at key
  exact key.symm

end GlobalTheory.FockRealMove

end
end

