import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInertStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ), IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) (eulerFac (bcParam r α) ((z : ℂ) * ((q : ℂ) ^ (t + 1))⁻¹) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹))) * ℓ x) := by
  first | exact @GlobalTheory.ZetaSumU.hasSum_zetaSum_inert | exact GlobalTheory.ZetaSumU.hasSum_zetaSum_inert | (intros; apply GlobalTheory.ZetaSumU.hasSum_zetaSum_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionFinitePlaceLatticeVacuaScal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCompress

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_half_idem (v : FinPl D) (h : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ b : AE D, finPart D b ∈ intAE D ∧ b + b = idem D (.inl v) := by
  have h2 : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
    GlobalTheory.LatVac.half_mem_adicCompletionIntegers D.host.F v h
  have hsum : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ +
      algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v
      (algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹)), ?_, ?_⟩
  · unfold intAE finPart
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v ⟨_, h2⟩, 1, ?_⟩
    simp [GlobalTheory.SplitIdem.placeHom, Algebra.TensorProduct.algebraMap_apply] <;> rfl
  · rw [← map_add, ← map_add, hsum]
    rfl

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem exists_char_act (v : FinPl D) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v)
    (hi : idem D (.inl v) • u = u) :
    ∃ y : AF D.host.F, ∀ f, IsLatVac (heisO ψ S T) (latO S T LS LT fun w => w = v) f →
      heisO ψ S T u f = ψ y • f := by
  classical
  have hidem := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.2.1 v
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨e, hee, hec, hsum, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    have hsum' : e + cA D e = idem D (.inl v) := by rw [hsum]; rfl
    have hsp : IsSplitIdem D e := by
      unfold IsSplitIdem
      exact ⟨hee, hec, v, _, hidem.2.2, hsum⟩
    have hsp' : IsSplitIdem D (cA D e) := isSplitIdem_conj hsp
    have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
    have hint : finPart D e ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
    have hint' : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
    have hm1 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e hint u hu
    have hm2 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ (cA D e) hint' u hu
    have hh1 : IsHalf e (e • u) := (isHalf_iff e (e • u)).2 (by rw [smul_smul, hee])
    have hh2 : IsHalf (cA D e) (cA D e • u) := (isHalf_iff (cA D e) (cA D e • u)).2 (by rw [smul_smul, hcc])
    have hsplit : e • u + cA D e • u = u := by rw [← add_smul, hsum', hi]
    refine ⟨-symplOH S T (e • u) (cA D e • u), fun f hf => ?_⟩
    unfold IsLatVac at hf
    have k1 := hf.2 e hsp _ hm1 hh1
    have k2 := hf.2 _ hsp' _ hm2 hh2
    have key := heisO_heisO ψ S T (e • u) (cA D e • u) f
    rw [k2, k1, hsplit] at key
    conv_rhs => rw [key]
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨b, hb, hbb⟩ := exists_half_idem v h2
    refine ⟨0, fun f hf => ?_⟩
    unfold IsLatVac at hf
    have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ b hb u hu
    have h2u : 2 • (b • u) = u := by rw [two_nsmul, ← add_smul, hbb, hi]
    rw [AddChar.map_zero_eq_one, one_smul, ← h2u]
    exact hf.1 _ hm

private theorem ipO_smul_smul' {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ)
    (f g : Mx D m n → ℂ) : ipO μ 𝓕 (a • f) (b • g) = (a * starRingEnd ℂ b) * ipO μ 𝓕 f g := by
  unfold ipO
  rw [← integral_const_mul]
  congr 1
  ext t
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem compress_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (w : WO S T), ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inl v) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ S T ΛS ΛT μ 𝓕 hψ hS hT hμ v w
  classical
  have hn : ∀ a, ‖ψ a‖ = 1 := by
    have h := hψ
    unfold IsStdChar IsCharAF at h
    exact h.1.2.1
  obtain ⟨hI1, -, hI3, hI4, -⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  obtain ⟨ι, hι⟩ : ∃ ι, ι = idem D (.inl v) := ⟨_, rfl⟩
  have hιι : ι * ι = ι := by rw [hι]; exact hI1 _
  have hcι : cA D ι = ι := by rw [hι]; exact hI3 _
  have hinf : infPart D ι = 0 := by rw [hι]; exact (hI4 v).1
  obtain ⟨x, hx⟩ : ∃ x, x = ι • w := ⟨_, rfl⟩
  rw [wAt_eq_smul, ← hι, ← hx]
  have hιx : ι • x = x := by rw [hx, smul_smul, hιι]
  have hloc : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => Sum.inl.inj h'.2) h
  have hloc' : ∀ u ∈ latO S T ΛS ΛT (fun u => u = v), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun u => u = v) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => h'.1) h
  have hpair : ∀ a, symplO S T (ι • a) x = symplO S T a x := by
    intro a
    rw [symplO_smul, hcι, hιx]
  by_cases hA : ∀ l ∈ latO S T ΛS ΛT (fun u => u = v), ψ (symplO S T l x) = 1
  · have hxg : x ∈ latO S T ΛS ΛT (fun _ => True) := by
      refine ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 x ?_).2 ?_
      · rw [hx]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hinf]
      · intro u' hu'
        rw [symplO_skew, AddChar.map_neg_eq_inv, ← hpair, hA _ (hloc u' hu'), inv_one]
    have hxv : x ∈ latO S T ΛS ΛT (fun u => u = v) := by
      rw [← hιx]
      exact hloc x hxg
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v hxv (by rw [← hι]; exact hιx)
    refine ⟨starRingEnd ℂ (ψ y), fun f g hf hg hvf hvg => ?_⟩
    rw [hy f hvf]
    exact ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g f hg hf).2.2.1 (ψ y)).2
  · push_neg at hA
    obtain ⟨l, hl, hl1⟩ := hA
    have hιl : ι • (ι • l) = ι • l := by rw [smul_smul, hιι]
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v (hloc' l hl) (by rw [← hι]; exact hιl)
    refine ⟨0, fun f g hf hg hvf hvg => ?_⟩
    rw [zero_mul]
    have hxf : IsThetaFunO ψ S T (heisO ψ S T x f) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 x f hf
    have hU := ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g (heisO ψ S T x f) hg hxf).2.2.2.2.2.2.1 (ι • l)).1
    rw [hy g hvg, heisO_comm, hy f hvf, heisO_smul, smul_smul, ipO_smul_smul', map_mul] at hU
    have hc : ψ y * starRingEnd ℂ (ψ y) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num
    have hs : starRingEnd ℂ (ψ (symplO S T (ι • l) x)) ≠ 1 := by
      rw [hpair]
      intro h
      exact hl1 ((starRingEnd ℂ).injective (by rw [h, map_one]))
    have h0 : (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) - 1) * ipO μ 𝓕 g (heisO ψ S T x f) = 0 := by
      linear_combination hU - (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) * ipO μ 𝓕 g (heisO ψ S T x f)) * hc
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hs)

end GlobalTheory.PlaceCompress
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCompress

open GlobalTheory.WeilVacMove

theorem gauss_ode (c : ℝ → ℂ) (a : ℂ) (h : ∀ s : ℝ, HasDerivAt c ((s : ℂ) * a * c s) s) :
    c 1 = Complex.exp (a / 2) * c 0 := by
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * ((t : ℂ) * (t : ℂ)) / 2)) * c t) 0 s := by
    intro s
    have e1 : HasDerivAt (fun x : ℂ => -(a * (x * x) / 2)) (-(a * (1 * (s : ℂ) + (s : ℂ) * 1) / 2)) (s : ℂ) :=
      ((((hasDerivAt_id (s : ℂ)).mul (hasDerivAt_id (s : ℂ))).const_mul a).div_const 2).neg
    have e3 := (e1.cexp.comp_ofReal).mul (h s)
    exact e3.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt) (fun s => (key s).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_div, neg_zero,
    Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add]
  simp

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem wAt_eq_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (w : Mx D m n) :
    wAt (.inr τ) w = lineAt θ τ (compAt θ τ w) 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  obtain ⟨-, -, -, -, hfi, -, hth⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  ext i j
  rw [← sub_eq_zero]
  apply hσ.ext
  · have h1 : finPart D (lineAt θ τ (compAt θ τ w) 1 i j) = 0 := by
      have := congrFun (congrFun (hfin 1) i) j
      simpa [Matrix.map_apply] using this
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, hfi τ, h1]
  · intro τ'
    have h2 := congrFun (congrFun (hcomp 1 τ') i) j
    by_cases hτ : τ' = τ
    · subst hτ
      rw [if_pos rfl, Complex.ofReal_one, one_smul] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ' (compAt θ τ' w) 1 i j)) = θ τ' (infPart D (w i j)) := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, (hth θ hθ τ').1, one_mul, h2']
      exact sub_self _
    · have h3 := (hth θ hθ τ').2 τ (Ne.symm hτ)
      rw [if_neg hτ] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ (compAt θ τ w) 1 i j)) = 0 := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, h3, zero_mul, zero_sub, neg_eq_zero, h2']

theorem dLine_heisO (hψ : IsStdChar D ψ (-1)) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (v : WO S T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    dLine ψ S T L (heisO ψ S T v f) x =
      -2 * phase lam S T (L 1) v * heisO ψ S T v f x + ψ (symplOH S T x v) * dLine ψ S T L f (x + v) := by
  have hG : (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) =
      fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        heisO ψ S T (L t) f (x + v) := by
    funext t
    have e1 := GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 v t
    have hX : Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) =
        (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ * (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring
    have hE := Complex.exp_ne_zero ((t : ℂ) * phase lam S T (L 1) v)
    show ψ (symplOH S T x (L t)) * (ψ (symplOH S T (x + L t) v) * f (x + L t + v)) =
      ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        (ψ (symplOH S T (x + v) (L t)) * f (x + v + L t))
    rw [GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_left,
      GlobalTheory.WeilVacMove.symplOH_skew S T v (L t), AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, e1, add_right_comm x (L t) v, hX]
    field_simp
  have hH := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).1 (x + v)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)))
      (Complex.exp (((0 : ℝ) : ℂ) * (-2 * phase lam S T (L 1) v)) * (1 * (-2 * phase lam S T (L 1) v))) 0 :=
    (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const _).cexp).comp_ofReal
  have hD := (hexp.const_mul (ψ (symplOH S T x v))).mul hH
  show deriv (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) 0 = _
  have hD' : HasDerivAt (fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
      heisO ψ S T (L t) f (x + v)) _ 0 := hD
  rw [hG, hD'.deriv]
  have hv : heisO ψ S T v f x = ψ (symplOH S T x v) * f (x + v) := rfl
  rw [hv, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  ring

private theorem flow_lemma {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (hvf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f)
    (hvg : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g) :
    ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z 1) f) g =
      Complex.exp (-(phase lam S T (lineAt θ τ z 1) (lineAt θ τ z 1) +
        Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * z * sS)) 1) (lineAt θ τ z 1)) / 2) *
        ipO μ 𝓕 f g := by
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  set J := Complex.I • (sT * z * sS) with hJ
  obtain ⟨hLc, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨hLc', hL0', -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ J
  set L := lineAt θ τ z with hLeq
  set L' := lineAt θ τ J with hLJeq
  set Dz := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z with hDz
  set DJ := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ J with hDJ
  have vf : Dz f + Complex.I • DJ f = 0 := hvf z
  have vg : Dz g + Complex.I • DJ g = 0 := hvg z
  have hp : ∀ (u : WO S T) (s : ℝ), phase lam S T u (L s) = (s : ℂ) * phase lam S T u (L 1) := by
    intro u s
    have hc : Continuous ((phase lam S T u).comp L) :=
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hLc continuous_const)
    exact GlobalTheory.WeilVacMove.additive_real _ hc s
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L t) f) g)
      ((s : ℂ) * -(phase lam S T (L 1) (L 1) + Complex.I * phase lam S T (L' 1) (L 1)) *
        ipO μ 𝓕 (heisO ψ S T (L s) f) g) s := by
    intro s
    set h := heisO ψ S T (L s) f with hheq
    have hh : IsThetaFunO ψ S T h := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 s) hf
    obtain ⟨hder, hXs⟩ := GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ z
    have hYs := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ J).2
    have h0 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g) (ipO μ 𝓕 (Dz h) g) (s - s) := by
      rw [sub_self]
      refine hder.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g = ipO μ 𝓕 (heisO ψ S T (L t) h) g
      rw [hheq, GlobalTheory.WeilVacMove.heisO_line_add hψ hLc hL0 t s f]
    have hd := (h0.comp_sub_const s s)
    simp only [sub_add_cancel] at hd
    refine hd.congr_deriv ?_
    have hDzh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hh
    have hDJh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hh
    have hDJg := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hg
    have cA : Dz h + Complex.I • DJ h =
        (-2 * (phase lam S T (L 1) (L s) + Complex.I * phase lam S T (L' 1) (L s))) • h := by
      funext x
      have c1 : Dz h x = -2 * phase lam S T (L 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * Dz f (x + L s) := dLine_heisO hψ hl hlam hLc hL0 (L s) hf x
      have c2 : DJ h x = -2 * phase lam S T (L' 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * DJ f (x + L s) := dLine_heisO hψ hl hlam hLc' hL0' (L s) hf x
      have c3 := congrFun vf (x + L s)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at c3 ⊢
      rw [c1, c2]
      linear_combination ψ (symplOH S T x (L s)) * c3
    have e3 : ipO μ 𝓕 h (Dz g) = Complex.I * ipO μ 𝓕 h (DJ g) := by
      have hz : Dz g = (-Complex.I) • DJ g := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left vg
      rw [hz, ((U h (DJ g) hh hDJg).2.2.1 (-Complex.I)).2]
      simp [Complex.conj_I]
    have e4 : ipO μ 𝓕 (Dz h + Complex.I • DJ h) g = ipO μ 𝓕 (Dz h) g + Complex.I * ipO μ 𝓕 (DJ h) g := by
      rw [((U (Dz h) g hDzh hg).2.2.2.1 _ (GlobalTheory.WeilVacMove.isTheta_smul Complex.I hDJh)).1,
        ((U (DJ h) g hDJh hg).2.2.1 Complex.I).1]
    rw [cA, ((U h g hh hg).2.2.1 _).1, hp (L 1) s, hp (L' 1) s] at e4
    linear_combination (-1 / 2 : ℂ) * e4 + (1 / 2 : ℂ) * hXs - (Complex.I / 2) * hYs - (1 / 2 : ℂ) * e3
  have hfin := gauss_ode _ _ key
  simp only [map_zero, GlobalTheory.WeilVacMove.heisO_zero] at hfin
  exact hfin

theorem compress : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ θ S T μ 𝓕 hψ hθ hμ τ sS sT _ _ w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  refine ⟨starRingEnd ℂ (Complex.exp (-(phase lam S T (lineAt θ τ (compAt θ τ w) 1) (lineAt θ τ (compAt θ τ w) 1) +
      Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * compAt θ τ w * sS)) 1)
        (lineAt θ τ (compAt θ τ w) 1)) / 2)), ?_⟩
  intro f g hf hg hvf hvg
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  obtain ⟨-, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  have h1 := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 1) hf
  rw [wAt_eq_lineAt hθ τ w, (U _ g h1 hg).2.1, (U f g hf hg).2.1,
    flow_lemma hψ hθ hμ hl hlam τ sS sT (compAt θ τ w) hf hg hvf hvg, map_mul]

end GlobalTheory.VacCompress

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorEigenOfThetaVectorAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_eigen_of_thetaVector_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (w : WO S T) (c : ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ x : WO S T, IsHalf e x → symplO S T w x = 0) → (∀ y : WO S T, IsHalf (cA D e) y → symplO S T w y = 0) → heisO ψ S T w f₀ = c • f₀ → ∃ c' : ℂ, heisO ψ S T w f = c' • f := by
  first | exact @GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt | exact GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt | (intros; apply GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFockVacuumCauchyRiemannStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_fockVacuum_cauchyRiemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  first | exact @GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | exact GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | (intros; apply GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_translates_span_dense_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ f' ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T w f₀), nrm2 μ 𝓕 (f - f') < ε := by
  first | exact @GlobalTheory.HeisDense.span_translates_dense | exact GlobalTheory.HeisDense.span_translates_dense | (intros; apply GlobalTheory.HeisDense.span_translates_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianAdjoint_laws_standardCharacter : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  first | exact @GlobalTheory.AdjLawPf.adjLaw | exact GlobalTheory.AdjLawPf.adjLaw | (intros; apply GlobalTheory.AdjLawPf.adjLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumnStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianPairing_fourierJacobi_step_basePoint_columns : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)), hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) = hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  first | exact @GlobalTheory.CharXFB.hA_xFB_col | exact GlobalTheory.CharXFB.hA_xFB_col | (intros; apply GlobalTheory.CharXFB.hA_xFB_col <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicUpToFactorOfLoweringKilledTorusWeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicUpToFactor_of_loweringKilled_torusWeight : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (la : Wt C.X.Ψ T.rank) (m : D.what₂.Tau → ℤ) (φ : GA D T → ℂ), LowKilled C.θ T B φ → (∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), φ (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ - la (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * φ g) → HolUpTo C B la (detPow C.θ T m) φ := by
  first | exact @GlobalTheory.AdSpan.ConjHol.holUpTo_of_lowKilled | exact GlobalTheory.AdSpan.ConjHol.holUpTo_of_lowKilled | (intros; apply GlobalTheory.AdSpan.ConjHol.holUpTo_of_lowKilled <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointIntegralIffDualLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  first | exact @GlobalTheory.DualRed.adj_int_iff | exact GlobalTheory.DualRed.adj_int_iff | (intros; apply GlobalTheory.DualRed.adj_int_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  first | exact @GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | exact GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | (intros; apply GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableConjMonomialBargmannGaussianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧ ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  first | exact @GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss | exact GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss | (intros; apply GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss <;> assumption)
end

