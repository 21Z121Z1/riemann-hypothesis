import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelConjugateTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConvLevel

theorem ccGA_leftInv {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : f ∈ GlobalTheory.Orb.CcGA V) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ y, f (k * y) = f y := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, -, b, hb, rfl⟩ := hf
    obtain ⟨K, hK, hb'⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨K.comap (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram),
      hK.preimage (GlobalTheory.AdelicU.continuous_projFin _ _), fun k hk hk' y => ?_⟩
    have h1 : GlobalTheory.AdelicU.projInf D.sp.cm.sig V.gram k = 1 := GlobalTheory.AdelicU.mem_finPts.1 hk'
    simp only [GlobalTheory.Orb.infFin, map_mul, h1, one_mul]
    rw [(hb' _ hk _).1]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add f f' _ _ h h' =>
    obtain ⟨U, hU, e⟩ := h
    obtain ⟨U', hU', e'⟩ := h'
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hk' y => by
      simp only [Pi.add_apply, e k hk.1 hk' y, e' k hk.2 hk' y]⟩
  | smul c f _ h =>
    obtain ⟨U, hU, e⟩ := h
    exact ⟨U, hU, fun k hk hk' y => by simp only [Pi.smul_apply, e k hk hk' y]⟩

theorem convR_level : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  intro D V μ _ _ f hf
  obtain ⟨U, hU, e⟩ := ccGA_leftInv hf
  refine ⟨U, hU, fun F k hk hk' g => ?_⟩
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq, GlobalTheory.AutomorphicL2Unitary.convR_eq]
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, e _ (U.inv_mem hk) ((GfC V).inv_mem hk')]

end GlobalTheory.ConvLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  first | exact @GlobalTheory.OnePDecay.decay_oneP | exact GlobalTheory.OnePDecay.decay_oneP | (intros; apply GlobalTheory.OnePDecay.decay_oneP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjections
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjLat

variable {D : D7}

theorem tmul_mul_incA (x : AF D.host.F) (y z : D.host.E) : (x ⊗ₜ[D.host.F] y) * incA D z = x ⊗ₜ[D.host.F] (y * z) := by
  show (x ⊗ₜ[D.host.F] y) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem of_tmul_mul_rat {m n k : ℕ} (x : AF D.host.F) (X : Matrix (Fin m) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin k) D.host.E) :
    HMul.hMul (Matrix.of fun i j => x ⊗ₜ[D.host.F] X i j : Mx D m n) (rat M : Mx D n k) =
      Matrix.of fun i j => x ⊗ₜ[D.host.F] (X * M) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, TensorProduct.tmul_sum]

theorem latO_mul_rat {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} (M M' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hadj : M'ᴴ * S.gram = S.gram * M) (hL : ∀ s ∈ LS, M' *ᵥ s ∈ LS) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    HMul.hMul (u : Mx D T.rank S.rank) (rat M : Mx D S.rank S.rank) ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a, ha, M' *ᵥ s, hL s hs, t, ht, ?_⟩
    have h : ∀ l j, ∑ k, star (M' k l) * S.gram k j = ∑ k, S.gram l k * M k j := fun l j => by
      have := congrFun (congrFun hadj l) j
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, ← TensorProduct.tmul_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum, mul_assoc]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp_rw [mul_left_comm (star (M' _ y)) (star (s y))]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h y j]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_rat {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hN : ∀ x ∈ N, x * M ∈ N) {w : Mx D m n} (hw : w ∈ hatMx N) :
    HMul.hMul w (rat M : Mx D n n) ∈ hatMx N := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    exact ⟨α, hα, x * M, hN x hx, of_tmul_mul_rat _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ)
    {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') : x * M ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on (p := fun x => x * M ∈ I • homLat Λ Λ') hx ?_ ?_
  · intro r hr n hn
    show (r • n) * M ∈ _
    rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (fun y hy => by rw [← Matrix.mulVec_mulVec]; exact hn _ (hM y hy))
  · intro x y hx hy
    show (x + y) * M ∈ _
    rw [Matrix.add_mul]; exact add_mem hx hy

theorem proj_adj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e' * d.qY)ᴴ * S.gram = S.gram * (d.e * d.qX) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem proj_adj' {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e * d.qX)ᴴ * S.gram = S.gram * (d.e' * d.qY) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem latRow_mul_rat {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ)
    (Mx₁ Mx₂ : Matrix (Fin (G.V (.grid (i + 1) 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) D.host.E)
    (hadj : Mx₂ᴴ * (G.V (.grid (i + 1) 0)).gram = (G.V (.grid (i + 1) 0)).gram * Mx₁)
    (h1 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₁ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    (h2 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₂ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    {u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))} (hu : u ∈ latRow G i) :
    HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ latRow G i := by
  obtain ⟨hu1, hu2⟩ := hu
  have hadj' : Mx₂ᴴ * (G.pS (.chi i 0)).gram = (G.pS (.chi i 0)).gram * Mx₁ := by
    show Mx₂ᴴ * (-(G.V (.grid (i + 1) 0)).gram) = (-(G.V (.grid (i + 1) 0)).gram) * Mx₁
    rw [Matrix.mul_neg, Matrix.neg_mul, hadj]
  have hu1' : u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) := hu1
  have L1 := @latO_mul_rat D (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) Mx₁ Mx₂ hadj' h2
  have t1 := L1 hu1'
  have t2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ hatMx (G.modul • homLat (G.latS (.chi i 0)) (G.latT (.chi i 0))) := by
    intro e he
    rw [← Matrix.smul_mul]
    exact hatMx_mul_rat _ _ (fun x hx => smul_homLat_mul _ _ _ _ h1 hx) (hu2 e he)
  exact ⟨t1, t2⟩

theorem latRow_proj : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  have hA := hF.hJ (σ + 1) h
  have e : G.Λ (.grid (2 * σ + 2 + 1) 0) = _ := G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)
  have hX : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact GlobalTheory.T.proj_X_preserves_embedding_lattice _ _ hA _ _ _ hv
  have hY : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact GlobalTheory.T.proj_Y_preserves_embedding_lattice _ _ hA _ _ _ hv
  rw [show (F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX = rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) from (rat_mul _ _).symm,
    show (F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY = rat ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) from (rat_mul _ _).symm]
  exact ⟨latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj _) hX hY hu, latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj' _) hY hX hu⟩

end GlobalTheory.ProjLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesCharacterOfParameter
section
noncomputable section

namespace GlobalTheory.DSUFromSU.Small

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.HCChar GlobalTheory.FormalDegree.Model
open GlobalTheory.Dec (IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep IsCharFn IsRegSS)

def Concl {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) (lam : Fin n → ℝ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
    (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsSqIntIrr ε σ),
    (∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
    (∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
      (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
    ∃ Θ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ ∧
      ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

theorem diag_mem_K {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (diagonal fun a => Complex.exp (θ a * Complex.I)) ∈ Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, ?_⟩
  · rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  · simp only [Jm, diagonal_mul_diagonal, mul_comm]

theorem wt_unique {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) {ν ν' : Fin n → ℝ}
    {v v' : ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0) (h : IsWtOn (Kset ε) σ ν v) (h' : IsWtOn (Kset ε) σ ν' v') : ν = ν' := by
  have key : ∀ θ : Fin n → ℝ, Complex.exp ((∑ a, ν a * θ a : ℝ) * Complex.I) =
      Complex.exp ((∑ a, ν' a * θ a : ℝ) * Complex.I) := fun θ => by
    have e := h θ (diag_mem_K ε θ)
    have e' := h' θ (diag_mem_K ε θ)
    set T := σ (diagonal fun a => Complex.exp (θ a * Complex.I))
    have t : ∀ w : ℂ, T w = T 1 * w := fun w => by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [t, smul_eq_mul] at e e'
    exact (mul_right_cancel₀ hv e).symm.trans (mul_right_cancel₀ hv' e')
  funext a
  by_contra hne
  have hd : ν a - ν' a ≠ 0 := sub_ne_zero.2 hne
  have := key (Pi.single a (Real.pi / (ν a - ν' a)))
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  have e : ν a * (Real.pi / (ν a - ν' a)) = ν' a * (Real.pi / (ν a - ν' a)) + Real.pi := by field_simp; ring
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at this
  exact Complex.exp_ne_zero _ (by linear_combination (-1 / 2 : ℂ) * this)

theorem concl_detPow (n : ℕ) (s : Bool) (m : ℤ) (μ : Measure (UJ fun _ : Fin n => s)) [μ.IsHaarMeasure] :
    Formalism.QuantumDeterminants.IsHCParam (lamDet n m) ∧ Concl (fun _ : Fin n => s) μ (lamDet n m) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.HCChar.Model.ds_case n s m μ
  obtain ⟨Θ, h3, h4⟩ := h2 h1.2.2.1
  refine ⟨h0, ℂ, inferInstance, inferInstance, inferInstance, detPow n m,
    ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1⟩, h1.2.2.2.2.2.1, fun ν S hS => ⟨0, by simp, ?_⟩, Θ, h3.1, h4⟩
  obtain ⟨S', hS'⟩ := h1.2.2.2.2.2.1
  obtain ⟨v, -, hv, hw⟩ := hS.2.2.2.1
  obtain ⟨v', -, hv', hw'⟩ := hS'.2.2.2.1
  simpa using wt_unique _ _ hv hv' hw hw'

theorem rank_zero (ε : Fin 0 → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin 0 → ℝ) : Concl ε μ lam := by
  obtain rfl : ε = fun _ => true := Subsingleton.elim _ _
  obtain rfl : lam = lamDet 0 0 := Subsingleton.elim _ _
  exact (concl_detPow 0 true 0 μ).2

theorem rank_one (ε : Fin 1 → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin 1 → ℝ)
    (h : Formalism.QuantumDeterminants.IsHCParam lam) : Concl ε μ lam := by
  obtain ⟨s, rfl⟩ : ∃ s, ε = fun _ => s := ⟨ε 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨m, hm⟩ := h.2 0
  obtain rfl : lam = lamDet 1 m := by
    funext a
    rw [Subsingleton.elim a 0]
    simp [lamDet, Formalism.QuantumDeterminants.rhoStd] at hm ⊢
    exact hm
  exact (concl_detPow 1 s m μ).2

end GlobalTheory.DSUFromSU.Small

end

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.HCChar GlobalTheory.SUChar GlobalTheory.Published
open GlobalTheory.Orb (ujMat ujRep IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset IsParS IsParU IsHCS IsHCU Ext exists_isHaarMeasure_SUJ)
open GlobalTheory.DSId (IsHCDS)
open GlobalTheory.SqIntSU (scalarMul unitScalar)

namespace GlobalTheory.DSUFromSU

variable {n : ℕ}

theorem isRegSS_diagonal_iff (d : Fin n → ℂ) : IsRegSS (diagonal d) ↔ Function.Injective d := by
  rw [IsRegSS, charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]

theorem isRegSS_diagonal_mul (d : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    IsRegSS (diagonal d) → IsRegSS (diagonal fun a => d a * c) := by
  rw [isRegSS_diagonal_iff, isRegSS_diagonal_iff]
  exact fun h a b e => h (mul_right_cancel₀ hc e)

theorem torusPt_eq_scalarMul (ε : Fin n → Bool) (θ : Fin n → ℝ) (φ : ℝ) (h : ∑ a, (θ a - φ) = 0) :
    torusPt ε θ = scalarMul ε (Circle.exp φ, suTorusPt ε (fun a => θ a - φ) h) := by
  apply Subtype.ext
  apply Units.ext
  show diagonal (fun a => Complex.exp (θ a * Complex.I)) =
    (Circle.exp φ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun a => Complex.exp (((θ a - φ : ℝ) : ℂ) * Complex.I))
  rw [Matrix.smul_mul, Matrix.one_mul, ← diagonal_smul]
  congr 1
  funext a
  rw [Pi.smul_apply, smul_eq_mul, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem weylDenom_sub_const (θ : Fin n → ℝ) (φ : ℝ) : weylDenom (fun a => θ a - φ) = weylDenom θ := by
  simp only [weylDenom, sub_sub_sub_cancel_right]

theorem wtVal_twist (hn : n ≠ 0) (lam θ : Fin n → ℝ) (m : ℤ) (hm : ∑ a, lam a = m) (w : Equiv.Perm (Fin n)) :
    wtVal (lam ∘ w.symm) θ = (Circle.exp ((∑ a, θ a) / n) : ℂ) ^ m *
      wtVal ((fun a => lam a - (m : ℝ) / n) ∘ w.symm) (fun a => θ a - (∑ b, θ b) / n) := by
  have hsum : ∑ a, lam (w.symm a) = m := by rw [Equiv.sum_comp w.symm lam]; exact hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [Circle.coe_exp, wtVal, wtVal, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have key : (∑ a, (lam ∘ w.symm) a * θ a) = (m : ℝ) * ((∑ a, θ a) / n) +
      ∑ a, ((fun a => lam a - (m : ℝ) / n) ∘ w.symm) a * (θ a - (∑ b, θ b) / n) := by
    simp only [Function.comp_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
    field_simp
    ring
  rw [key]
  push_cast
  ring

theorem dsChar_twist (ε : Fin n → Bool) (hn : n ≠ 0) (lam θ : Fin n → ℝ) (m : ℤ) (hm : ∑ a, lam a = m) :
    dsChar ε lam θ = (Circle.exp ((∑ a, θ a) / n) : ℂ) ^ m *
      dsChar ε (fun a => lam a - (m : ℝ) / n) (fun a => θ a - (∑ b, θ b) / n) := by
  simp only [dsChar, wtVal_twist hn lam θ m hm, weylDenom_sub_const]
  have : ∀ s : Finset (Equiv.Perm (Fin n)), ∀ (c : ℂ) (f g : Equiv.Perm (Fin n) → ℂ),
      ∑ w ∈ s, f w * (c * g w) = c * ∑ w ∈ s, f w * g w := fun s c f g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

end GlobalTheory.DSUFromSU

namespace GlobalTheory.DSUFromSU

theorem discreteSeriesCharacterOfParameter (hP : DiscreteSeriesCharacterSU) : DiscreteSeriesCharacterOfParameter := by
  intro n ε μ _ lam hlam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Small.rank_zero ε μ lam
    · exact Small.rank_one ε μ lam hlam
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hU : IsParU lam := ⟨hlam.1.injective, hlam.2⟩
  obtain ⟨m, hm, hS, -⟩ := GlobalTheory.SUtoU.extension_main n hn1 ε ℂ (fun _ => 0) lam hU
  obtain ⟨μ', hμ'⟩ := exists_isHaarMeasure_SUJ ε
  obtain ⟨V, i1, i2, i3, σ, hσ, Θ', hΘ', hform⟩ := hP n hn ε μ' _ hS
  obtain ⟨m2, hm2, -, hext⟩ := GlobalTheory.SUtoU.extension_main n hn1 ε V σ lam hU
  have e : m2 = m := by exact_mod_cast hm2.symm.trans hm
  rw [e] at hext
  obtain ⟨π, hE, hHC⟩ := hext hσ
  have hDS : IsHCDS ε lam π := by
    have h := GlobalTheory.DSSU.Chamber.vChamber n ε V π lam 1 (fun a b h _ => h) hlam.1 hHC
    simpa only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Function.comp_id, Matrix.submatrix_id_id] using h
  obtain ⟨Θ, hΘ, hΘf⟩ := GlobalTheory.ExtChar.exists_isCharFn_ext n hn1 ε μ μ' V m σ π hσ.1.2.2.1 hDS.1.2.2.1 hE Θ' hΘ'
  refine ⟨V, i1, i2, i3, π, hDS.1, hDS.2.2.1.exists, hDS.2.2.2, Θ, hΘ, fun θ hreg => ?_⟩
  have hθ' : ∑ a, (θ a - (∑ b, θ b) / n) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hreg' : IsRegSS (suMat ε (suTorusPt ε (fun a => θ a - (∑ b, θ b) / n) hθ')) := by
    rw [suMat_suTorusPt]
    rw [ujMat_torusPt] at hreg
    have h := isRegSS_diagonal_mul _ (Complex.exp_ne_zero ((-((∑ b, θ b) / n : ℝ) : ℂ) * Complex.I)) hreg
    convert h using 3 with a
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hanti : StrictAnti fun a => lam a - (m : ℝ) / n := fun a b h => sub_lt_sub_right (hlam.1 h) _
  rw [torusPt_eq_scalarMul ε θ _ hθ', hΘf _ _ hreg', hform _ hθ' hreg', chamberChar_of_strictAnti ε hanti,
    dsChar_twist ε hn0 lam θ m hm]

end GlobalTheory.DSUFromSU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelConjugateTransferStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_model_conjugate_transfer : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ (M₁ : DSModel (sgn false V) fun τ => dualPar (S τ)) (κ : SmT M₁ ≃+ SmT M), ModelTr (starRingEnd ℂ) false θ M₁ M κ := by
  first | exact @GlobalTheory.ConjModelTr.exists_conjModelTr | exact GlobalTheory.ConjModelTr.exists_conjModelTr | (intros; apply GlobalTheory.ConjModelTr.exists_conjModelTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelParamShiftedWeightOfCoverDiscStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesModelParamShiftedWeight_of_coverDiscreteSeries : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D → DirectBridge D := by
  first | exact @GlobalTheory.ArchRec.Direct.directBridge | exact GlobalTheory.ArchRec.Direct.directBridge | (intros; apply GlobalTheory.ArchRec.Direct.directBridge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  first | exact @GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero | exact GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero | (intros; apply GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMatrixBySymplecticFormHomAtRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymplBound

theorem symplAt_pick {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (i : Fin T.rank) (j : Fin S.rank) (w : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ
      (((tauE D τ D.host.xi0)⁻¹ * w) • ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ)) X =
      2 * (w * starRingEnd ℂ (X i j)).re := by
  have hc : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hT := GlobalTheory.SmoothAutCheck.gramAt_unit T τ
  have hS := GlobalTheory.SmoothAutCheck.gramAt_unit S τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  congr 2
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have e1 : (gramAt D S τ)⁻¹ * Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ) =
      (gramAt D S τ)⁻¹ * (Xᴴ * Matrix.single i j (1 : ℂ)) * gramAt D S τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (gramAt D T τ), mul_nonsing_inv _ hT, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ hS, Matrix.one_mul,
    Matrix.trace_mul_single]
  simp only [Matrix.conjTranspose_apply, MulOpposite.op_one, one_smul, Complex.star_def]
  field_simp

theorem bound : ∀ (D : D7) (S T : HSp D) (τ : D.what₂.Tau), ∃ (n : ℕ) (zs : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ) (κ : ℝ), ∀ X : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∑ i, ∑ j, ‖X i j‖ ≤ κ * ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs l) X| := by
  intro D S T τ
  let g : Fin 2 × Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun p =>
    ((tauE D τ D.host.xi0)⁻¹ * Complex.I ^ (p.1 : ℕ)) •
      ((gramAt D T τ)⁻¹ * Matrix.single p.2.1 p.2.2 (1 : ℂ) * gramAt D S τ)
  let e := Fintype.equivFin (Fin 2 × Fin T.rank × Fin S.rank)
  refine ⟨_, fun l => g (e.symm l), 1, fun X => ?_⟩
  rw [one_mul, Equiv.sum_comp e.symm (fun p => |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (g p) X|),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [g, symplAt_pick, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
  have h1 : (starRingEnd ℂ (X i j)).re = (X i j).re := Complex.conj_re _
  have h2 : (Complex.I * starRingEnd ℂ (X i j)).re = (X i j).im := by simp
  rw [h1, h2, abs_mul, abs_mul, abs_two]
  have := Complex.norm_le_abs_re_add_abs_im (X i j)
  nlinarith [abs_nonneg (X i j).re, abs_nonneg (X i j).im]

end GlobalTheory.SymplBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧ ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K := by
  first | exact @GlobalTheory.ScalarAnnih.exists_compact_of_annih | exact GlobalTheory.ScalarAnnih.exists_compact_of_annih | (intros; apply GlobalTheory.ScalarAnnih.exists_compact_of_annih <;> assumption)
end

