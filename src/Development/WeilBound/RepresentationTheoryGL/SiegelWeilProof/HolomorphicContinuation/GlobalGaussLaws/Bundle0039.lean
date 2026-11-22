import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0038
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.QuadraticOperatorPureTensor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0552

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def cθ (θ : InfFam D) (τ : D.what₂.Tau) : AE D →+* ℂ := (θ τ).comp (infPart D)

theorem compAt_eq {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (w : Mx D m k) : compAt θ τ w = w.map (cθ θ τ) := rfl

theorem compAt_mul' {θ : InfFam D} {τ : D.what₂.Tau} {m k l : ℕ} (x : Mx D m k) (y : Mx D k l) :
    compAt θ τ (x * y : Mx D m l) = compAt θ τ x * compAt θ τ y := by
  simp only [compAt_eq]; exact Matrix.map_mul

theorem compAt_one' {θ : InfFam D} {τ : D.what₂.Tau} {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  simp only [compAt_eq]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_zero' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} : compAt θ τ (0 : Mx D m k) = 0 := by
  ext i j; simp [compAt_eq]

theorem compAt_add' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x y : Mx D m k) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j; simp [compAt_eq]

theorem component_block_matrix {θ : InfFam D} {τ : D.what₂.Tau} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d : Mx D (n + n) (n + n)) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) :=
  GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem ae_ext {θ : InfFam D} (hθ : IsInfFam θ) {z z' : AE D} (h1 : ∀ τ, cθ θ τ z = cθ θ τ z')
    (h2 : finPart D z = finPart D z') : z = z' := by
  have h := (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 (z - z') (fun τ => by
      have := h1 τ
      simp only [cθ, RingHom.comp_apply] at this
      rw [RingHom.map_sub, RingHom.map_sub, this, sub_self])
    (by rw [RingHom.map_sub, h2, sub_self])
  exact sub_eq_zero.mp h

theorem mx_ext {θ : InfFam D} (hθ : IsInfFam θ) {m k : ℕ} {x x' : Mx D m k} (h1 : ∀ τ, compAt θ τ x = compAt θ τ x')
    (h2 : x.map (finPart D) = x'.map (finPart D)) : x = x' := by
  ext i j
  exact ae_ext hθ (fun τ => congrFun (congrFun (h1 τ) i) j) (congrFun (congrFun h2 i) j)

theorem cθ_cA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : AE D) : cθ θ τ (cA D z) = conj (cθ θ τ z) :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 z τ

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) z) =
    (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) z)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
  rfl

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def OpCLM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
        (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

def AwayFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), g = x * ι y ∧ ∀ Ψ, AwayCls θ τ fr Ψ → ∃ Ψ', AwayCls θ τ fr Ψ' ∧
      ∀ (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ) (hS : tens θ τ fr S Ψ ∈ schwartzA θ V.rank n),
        (ω x ⟨tens θ τ fr S Ψ, hS⟩).1 = tens θ τ fr S Ψ'

def SchDeriv : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n),
    ∃ (S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ) (S' : SchwartzMap (Fin m → Fin n → ℂ) ℂ),
      (∀ t y, S t y = fP c P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin m) (Fin m) ℂ) * (Matrix.of y : Matrix (Fin m) (Fin n) ℂ))) ∧
      (∀ y, S' y = fP c (vfX c X P) y) ∧
        Filter.Tendsto (fun t : ℝ => t⁻¹ • (S t - S 0)) (nhdsWithin 0 {0}ᶜ) (nhds S')

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRightOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem convRight_of (hE : EisStrong) : ConvRight := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR
  have hn : 0 < n := by
    obtain ⟨h1, h2, -⟩ := hR
    omega
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hsec : IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) :=
    GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 h𝓕 ω hS.hω l hS.hl s hS.hs Φ
      hS.hΦ
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ :=
    hE D n hn χ V.rank hS.hχ hS.hη H hS.hH (s0 V n) _ hsec (s0 V n)
  refine ⟨σ, fun z hz g => ?_⟩
  obtain ⟨u, hu, hb⟩ := (hconv z hz).1 {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hb g rfl q) hu

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def ptX {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) : Fin m × Fin n × Bool → ℂ := fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

theorem evX_eq_eval {m : ℕ} (Q : PX m n) (u : Matrix (Fin m) (Fin n) ℂ) : evX Q u = eval (ptX u) Q := rfl

theorem ptX_add_smul {m : ℕ} (u w : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ptX (u + (t : ℂ) • w) = ptX u + (t : ℂ) • ptX w := by
  funext k
  simp only [ptX, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

theorem gAway_add_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    gAway V l s τ (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) = gAway V l s τ z := by
  have hz : ∀ τ', τ' ≠ τ → (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) τ' = z τ' := by
    intro τ' h
    rw [Pi.add_apply, Pi.smul_apply, dirAt_ne h, smul_zero, add_zero]
  delta gAway
  beta_reduce
  congr 2
  refine Finset.sum_congr rfl fun τ' hτ' => ?_
  rw [hz τ' (by simpa using hτ')]

theorem gaussian_vacuum_add_line {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) (x : Mx D V.rank n)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    psi0 θ V n l s τ (x + lineAt θ τ X t) = psi0 θ V n l s τ x := by
  obtain ⟨-, hfinL, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  have h1 : (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) =
      (fun τ' => compAt θ τ' x) + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X := by
    funext τ'
    have hadd : compAt θ τ' (x + lineAt θ τ X t) = compAt θ τ' x + compAt θ τ' (lineAt θ τ X t) := by
      ext i j
      show (θ τ') (infPart D ((x + lineAt θ τ X t) i j)) =
        (θ τ') (infPart D (x i j)) + (θ τ') (infPart D (lineAt θ τ X t i j))
      rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add, map_add]
    rw [hadd, hcomp t τ', Pi.add_apply, Pi.smul_apply]
    by_cases h : τ' = τ
    · rw [if_pos h, h, dirAt_self]
    · rw [if_neg h, dirAt_ne h, smul_zero]
  have h2 : (fun i j => finPart D ((x + lineAt θ τ X t) i j)) = (fun i j => finPart D (x i j)) := by
    funext i j
    have h0 : finPart D (lineAt θ τ X t i j) = 0 := congrFun (congrFun (hfinL t) i) j
    rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add, h0, add_zero]
  show gAway V l s τ (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) *
      g0 D V.rank n (fun i j => finPart D ((x + lineAt θ τ X t) i j)) =
    gAway V l s τ (fun τ' => compAt θ τ' x) * g0 D V.rank n (fun i j => finPart D (x i j))
  rw [h1, h2, gAway_add_dirAt]

private theorem hasDerivAt_mvPolynomial_eval_line_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℂ) (a v : σ → ℂ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (a + (t : ℂ) • v) p)
      (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) 0 := by
  induction p using MvPolynomial.induction_on
  next r =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : HasDerivAt (fun t : ℝ => (a + (t : ℂ) • v) i) (v i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have h2 := (h1.mul_const (v i)).const_add (a i)
      simpa using h2
    have h := hp.mul hX
    simp only [map_mul, MvPolynomial.eval_X]
    refine h.congr_deriv ?_
    have hk : ∀ k, MvPolynomial.eval a (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i +
          (if i = k then MvPolynomial.eval a p else 0) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        MvPolynomial.eval_X, Pi.single_apply]
      split_ifs with h
      · simp only [map_one, mul_one]
        ring
      · simp only [map_zero, mul_zero, zero_add, add_zero]
        ring
    have hs1 : ∑ k, v k * (MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i) =
        (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) * a i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs2 : ∑ k, v k * (if i = k then MvPolynomial.eval a p else 0) = MvPolynomial.eval a p * v i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        ring
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hk, mul_add, Finset.sum_add_distrib, hs1, hs2, Complex.ofReal_zero, zero_smul, add_zero]

private theorem hasDerivAt_norm_sq_add_smul_zero (u w : ℂ) :
    HasDerivAt (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) (2 * (star u * w).re) 0 := by
  have h : (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) =
      fun t : ℝ => (u.re + t * w.re) * (u.re + t * w.re) + (u.im + t * w.im) * (u.im + t * w.im) := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => u.re + t * w.re) w.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.re).const_add u.re
  have h2 : HasDerivAt (fun t : ℝ => u.im + t * w.im) w.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.im).const_add u.im
  refine ((h1.mul h1).add (h2.mul h2)).congr_deriv ?_
  show _ = 2 * ((starRingEnd ℂ) u * w).re
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem hasDerivAt_gs_line_zero {m : ℕ} (c : ℝ) (U W : Matrix (Fin m) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gs c (U + (t : ℂ) • W))
      (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) 0 := by
  have hr : HasDerivAt (fun t : ℝ => c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2)
      (c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re) 0 := by
    refine HasDerivAt.const_mul c ?_
    first
      | exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
      | exact HasDerivAt.sum fun a _ => HasDerivAt.sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
  have hn : HasDerivAt (fun t : ℝ => -((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ))
      (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ)) 0 := hr.ofReal_comp.neg
  have hc := hn.cexp
  have e0 : (fun t : ℝ => gs c (U + (t : ℂ) • W)) =
      fun t : ℝ => Complex.exp (-((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ)) := by
    funext t
    rfl
  rw [e0]
  refine hc.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rfl

theorem annS_tens {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (X : Matrix (Fin V.rank) (Fin n) ℂ) (x : Mx D V.rank n) :
    annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) x =
      (∑ k, ptX (fr⁻¹ * X) k * eval (ptX (fr⁻¹ * compAt θ τ x)) (pderiv k Q)) *
        gs (cLoc l τ) (fr⁻¹ * compAt θ τ x) * psi0 θ V n l s τ x := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  set c := cLoc l τ with hc
  set z := compAt θ τ x with hz
  set U : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * z with hU
  set W : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * X with hW
  set Ψx := psi0 θ V n l s τ x with hΨ
  have hadd : ∀ y : Mx D V.rank n, compAt θ τ (x + y) = z + compAt θ τ y := by
    intro y
    ext i j
    show (θ τ) (infPart D ((x + y) i j)) = (θ τ) (infPart D (x i j)) + (θ τ) (infPart D (y i j))
    rw [show (x + y) i j = x i j + y i j from rfl, map_add, map_add]
  have hcz : ∀ t : ℝ, compAt θ τ (x + lineAt θ τ X t) = z + (t : ℂ) • X := by
    intro t
    rw [hadd, hcomp t τ, if_pos rfl]
  have hφ : ∀ t : ℝ, tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t) =
      eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx := by
    intro t
    have e1 : fr⁻¹ * compAt θ τ (x + lineAt θ τ X t) = U + (t : ℂ) • W := by
      rw [hcz t, Matrix.mul_add, Matrix.mul_smul]
    show fP c Q (fr⁻¹ * compAt θ τ (x + lineAt θ τ X t)) * psi0 θ V n l s τ (x + lineAt θ τ X t) = _
    rw [e1, gaussian_vacuum_add_line hθ V l s τ x X t]
    show evX Q (U + (t : ℂ) • W) * gs c (U + (t : ℂ) • W) * Ψx = _
    rw [evX_eq_eval, ptX_add_smul]
  have hderiv : HasDerivAt (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t))
      ((∑ k, ptX W k * eval (ptX U) (pderiv k Q)) * gs c U * Ψx +
        eval (ptX U) Q * (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) * Ψx) 0 := by
    have hP := hasDerivAt_mvPolynomial_eval_line_zero Q (ptX U) (ptX W)
    have hG := hasDerivAt_gs_line_zero c U W
    rw [show (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) =
        fun t : ℝ => eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx from funext hφ]
    refine ((hP.mul hG).mul_const Ψx).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, add_zero]
    ring
  have hφx : tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = eval (ptX U) Q * gs c U * Ψx := by
    have h0 := hφ 0
    simp only [map_zero, add_zero, Complex.ofReal_zero, zero_smul] at h0
    exact h0
  have hdet : IsUnit fr.det := hfr.1
  have hdetH : IsUnit frᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  have hGs : gramAt D V τ * s τ = (fr⁻¹)ᴴ * fr⁻¹ := by
    have h := hfr.2.2
    calc gramAt D V τ * s τ = (frᴴ)⁻¹ * (frᴴ * (gramAt D V τ * s τ) * fr) * fr⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
            ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
      _ = (fr⁻¹)ᴴ * fr⁻¹ := by
          rw [h, Matrix.mul_one, Matrix.conjTranspose_nonsing_inv]
  have e1' : ∑ a, ∑ i, 2 * (star (U a i) * W a i).re = 2 * (Uᴴ * W).trace.re := by
    show _ = 2 * (∑ i, (Uᴴ * W) i i).re
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  have e2' : Uᴴ * W = zᴴ * (gramAt D V τ * s τ) * X := by
    rw [hGs]
    simp only [hU, hW, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e3' : (zᴴ * (gramAt D V τ * s τ) * X).trace.re = (Xᴴ * (gramAt D V τ * s τ) * z).trace.re := by
    have h : Xᴴ * (gramAt D V τ * s τ) * z = (zᴴ * (gramAt D V τ * s τ) * X)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (hM τ).eq, Matrix.mul_assoc]
    rw [h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  have hc' : c = 2 * Real.pi * |l τ| := rfl
  have hlin : GlobalTheory.StdUnn.linF V l s τ X z = ((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ) := by
    show ((4 * Real.pi * |l τ| * (Xᴴ * (gramAt D V τ * s τ) * z).trace.re : ℝ) : ℂ) = _
    congr 1
    rw [e1', e2', e3', hc']
    ring
  show deriv (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) 0 +
      GlobalTheory.StdUnn.linF V l s τ X z * tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = _
  rw [hderiv.deriv, hφx, hlin]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem mat_mOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (A : GL (Fin n) ℂ) :
    mat (ι (mOf A)) = blk4 (unitAt hσ τ A).1 0 0 (adj ((unitAt hσ τ A)⁻¹).1) := by
  have hU : ((unitAt hσ τ A).1).map (finPart D) = 1 := by
    rw [unitAt_val]
    exact finite_part_adelic_point_matrix hσ τ A.1
  have hUi : (((unitAt hσ τ A)⁻¹).1).map (finPart D) = 1 := finite_part_adelic_point_matrix hσ τ (A⁻¹).1
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 (mOf A)).2.2, finite_part_block_matrix_map, hU, finPart_adj _ hUi, Matrix.map_zero _ (map_zero _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 (mOf A)).1, mR_mOf, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_matrix hσ,
        compAt_zero]
      have hUc : compAt θ τ ((unitAt hσ τ A)⁻¹).1 = (A⁻¹).1 := component_adelic_point_matrix hσ τ (A⁻¹).1
      rw [hUc]
      rfl
    · rw [(hι.2 (mOf A)).2.1 τ' e, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_ne hσ e,
        compAt_zero]
      have hUc : compAt θ τ' ((unitAt hσ τ A)⁻¹).1 = 1 := component_adelic_point_ne hσ e (A⁻¹).1
      rw [hUc, Matrix.conjTranspose_one, block_matrix_diagonal_one_eq_one]

theorem mat_nOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (y : PositivityTheory.Rg.Sw.GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks 1 b 0 1) : mat (ι y) = blk4 1 (atT σ τ b) 0 1 := by
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 y).2.2, finite_part_block_matrix_map, finPart_atT_map hσ τ b, Matrix.map_zero _ (map_zero _),
      Matrix.map_one _ (map_zero _) (map_one _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 y).1, hy, component_block_matrix (R := ℂ), compAt_one, compAt_atT hσ, compAt_zero]
      rfl
    · rw [(hι.2 y).2.1 τ' e, component_block_matrix (R := ℂ), compAt_one, compAt_atT_ne hσ e, compAt_zero, block_matrix_diagonal_one_eq_one]

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SchDecay
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def Pk (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) (κ : ℂ) : Prop :=
  ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n)) →
    ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u

def kap (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) : ℂ :=
  Classical.epsilon (Pk μ π B)

set_option synthInstance.maxHeartbeats 800000 in
theorem kap_spec {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Pk μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x) (kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  apply Classical.epsilon_spec
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  exact LocCellT.tauFact μ (piF θ τ fr) (continuous_piF hθ τ fr) (sIns τ fr)
    (fun z u => by rw [(piF θ τ fr).map_add, piF_sIns hθ τ hdet]) (Bw ψ V θ τ fr Ψ x)
    (continuous_Bw hθ hψ hΨ x).measurable (fun z u => Bw_add hθ hdet ψ hΨ x z u)
    (fun u => (1 + ‖u‖) ^ (-rr V.rank n)) hρc (fun u => Real.rpow_pos_of_pos (by positivity) _)
    (hint_int hθ hdet μ hΨ hψ x)

theorem sch_decay (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    ∃ C, ∀ u, ‖f u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n) := by
  obtain ⟨S, rfl⟩ := hf
  set k : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hk
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (Fin m → Fin n → ℂ) ℂ) S, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl S u
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖u‖) ^ k := by positivity
  have e : (1 + ‖u‖) ^ (-rr m n) = ((1 + ‖u‖) ^ k)⁻¹ := by
    rw [rr, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

