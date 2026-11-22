import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0035
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0530
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0036

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockMatrixDiagonalOneEqOne
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem chi_exp {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) (hχ : IsHeckeChar D χ) {m : ℕ}
    (hη : ResEta D χ m) (τ : D.what₂.Tau) :
    ∃ k : ℤ, Even (k - (m : ℤ)) ∧ ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k := by
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ m τ hθ hχ hη
  have ha' := ha
  obtain ⟨k, hk, hall⟩ := ha
  refine ⟨k, ?_, hall.2 θ hθ⟩
  obtain ⟨η, -, hη2, hη3, -⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨k', hk', hall'⟩ := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist ha' (hη2 τ) m
  have ek : k' = k - m := by
    have : (k' : ℚ) = k - m := by rw [hk', hk]; ring
    exact_mod_cast this
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1)
  have ww : w * w = 1 := by
    funext τ'
    simp only [w, Pi.mul_apply, Pi.one_apply, Pi.mulSingle_apply]
    split_ifs <;> simp
  let x0 : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have hx0 : (x0 : AE D) = e w := rfl
  have hfix : cA D (x0 : AE D) = x0 := by
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x0 : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x0 : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig _
      rw [e3, hx0, e1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, hx0, e2]
      simp only [w, Pi.mulSingle_apply]
      split_ifs <;> simp
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_unit D x0 hfix
  obtain ⟨⟨η0, hη0⟩, hχ0⟩ := hη
  have hξ : (χ * (η ^ m)⁻¹) x0 = 1 := by
    rw [← hb, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, hχ0 η0 hη0 b, hη3.2 η0 hη0 b, pow_one,
      mul_inv_cancel]
  have hv := hall'.2 θ hθ x0 (by rw [hx0, e1]) fun τ' h => by rw [hx0, e2]; simp [w, Pi.mulSingle_eq_of_ne h]
  rw [hξ, hx0, e2] at hv
  simp only [w, Pi.mulSingle_eq_same, norm_neg, norm_one, Complex.ofReal_one, div_one, Circle.coe_one] at hv
  rw [← ek]
  have hv' : ((-1 : ℂ)) ^ k' = 1 := by simpa using hv.symm
  rcases Int.even_or_odd k' with h | h
  · exact h
  · exfalso
    rw [h.neg_one_zpow] at hv'
    norm_num at hv'

def mOf (a : GL (Fin n) ℂ) : PositivityTheory.Rg.Sw.GR n where
  val :=
    { val := fromBlocks a.1 0 0 (a⁻¹).1ᴴ
      inv := fromBlocks (a⁻¹).1 0 0 a.1ᴴ
      val_inv := by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← conjTranspose_mul, Units.mul_inv,
          conjTranspose_one]
        exact fromBlocks_one
      inv_val := by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← conjTranspose_mul, Units.inv_mul,
          conjTranspose_one]
        exact fromBlocks_one }
  property := by
    show InG (fromBlocks a.1 0 0 (a⁻¹).1ᴴ)
    simp only [InG, JJ, fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_conjTranspose, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, Units.inv_mul, ← conjTranspose_mul, Units.mul_inv, conjTranspose_one, neg_zero]

theorem mR_mOf (a : GL (Fin n) ℂ) : mR (mOf a) = fromBlocks a.1 0 0 (a⁻¹).1ᴴ := rfl

theorem mR_mOf_inv (a : GL (Fin n) ℂ) : mR (mOf a)⁻¹ = fromBlocks (a⁻¹).1 0 0 a.1ᴴ := rfl

theorem component_block_matrix {R : Type} (θ : InfFam D) (τ : D.what₂.Tau) (a b c d : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  rw [compAt_eq_map, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]; rfl

theorem finite_part_block_matrix_map (a b c d : Matrix (Fin n) (Fin n) (AE D)) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  rw [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [Zero R] [One R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, fromBlocks_one, submatrix_one_equiv]

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (X : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (adj X) = (compAt θ τ X)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.FockCompare.comp_cA hθ]
  rfl

theorem finPart_adj (X : Matrix (Fin n) (Fin n) (AE D)) (hX : X.map (finPart D) = 1) : (adj X).map (finPart D) = 1 := by
  ext i j
  have e3 : finPart D (cA D (X j i)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (X j i)) :=
    GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig _
  have := congrFun (congrFun hX j) i
  simp only [Matrix.map_apply] at this
  simp only [adj, Matrix.map_apply, Matrix.transpose_apply, e3, this, Matrix.one_apply]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FtLocEqKer
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ))

theorem ftLoc_eq_ker (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (v : Fin m → Fin n → ℂ) :
    ftLoc ε t f v = ∫ u, f u * ker ε t v u := rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem integrand_eq {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    tens θ τ fr f Ψ y * ψ (trA (Matrix.trace (inner V x y))) =
      (f (piF θ τ fr y) * ker ε (tLoc l τ) (piF θ τ fr x) (piF θ τ fr y)) * Bw ψ V θ τ fr Ψ x y := by
  have hsplit : inner V x y = inner V x (y - sIns τ fr (piF θ τ fr y)) + inner V x (sIns τ fr (piF θ τ fr y)) := by
    rw [← GlobalTheory.CompanionTheory.EisCovar.Weyl.inner_add_right, sub_add_cancel]
  have hψ2 : ψ (trA (Matrix.trace (inner V x y))) =
      ψ (trA (Matrix.trace (inner V x (y - sIns τ fr (piF θ τ fr y))))) *
        ψ (trA (Matrix.trace (inner V x (sIns τ fr (piF θ τ fr y))))) := by
    rw [hsplit, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Weyl.trA_add, AddChar.map_add_eq_mul]
  rw [hψ2, psi_inner_sIns hθ hl hfr]
  have hp : (fr⁻¹ * compAt θ τ y : Matrix (Fin V.rank) (Fin n) ℂ) = piF θ τ fr y := rfl
  unfold Bw tens ker
  rw [hp]
  ring

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlin : LIlin := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  have hfr : IsUnit fr.det := hC.hfr.1
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  refine ⟨fun y a P Q => ?_, fun P => ?_⟩
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have hlin : phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (a • P + Q) =
        a • phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) Q := by
      apply Subtype.ext
      rw [LocLawH.phiS_val (mem _), Submodule.coe_add, Submodule.coe_smul, LocLawH.phiS_val (mem P), LocLawH.phiS_val (mem Q)]
      funext x
      simp only [tens, fP, evX, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, MvPolynomial.smul_eval]
      ring
    rw [← hL y _ hΨ (a • P + Q), hlin, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, hL y _ hΨ P,
      hL y _ hΨ Q]
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    show a * (L y (fP (cLoc l τ) P) _ * _) + L y (fP (cLoc l τ) Q) _ * _ =
      (a * L y (fP (cLoc l τ) P) _ + L y (fP (cLoc l τ) Q) _) * _
    ring
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have e := hL 1 _ hΨ P
    rw [map_one, map_one, Module.End.one_apply, LocLawH.phiS_val (mem P)] at e
    exact e.symm

theorem lIcont : LIcont := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have key : sLd L (cLoc l τ) P = fun y => (ω (ι y) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 := by
    funext y
    rw [hL y _ hΨ P, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one]
    rfl
  rw [key]
  obtain ⟨𝓕, h𝓕⟩ := hC.hμ
  exact (GlobalTheory.StdUnn.weilSch_apply_zero_continuous D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 h𝓕 ω hC.hω
    (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).comp hC.hι.1

theorem lIkact : LIkact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  have hk' : ω (ι k) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P) =
      phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P) := by
    apply Subtype.ext
    rw [hL k _ hΨ P, hρ k P hk, LocLawH.phiS_val (mem _)]
  have e : (ω (ι (g * k)) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 =
      (ω (ι g) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P))).1 0 := by
    rw [map_mul, map_mul, Module.End.mul_apply, hk']
  rw [hL (g * k) _ hΨ P, hL g _ hΨ (ρ k P), LocLawH.tens_zero, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one, mul_one] at e
  exact e

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoE
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
set_option maxHeartbeats 2000000

open Classical in

def substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    PX m n :=
  aeval (fun v : D.what₂.Tau × Fin m × Fin n × Bool => if v.1 = τ then
      (if v.2.2.2 then ∑ c, C (star (fr v.2.1 c)) * X (c, v.2.2.1, true) else ∑ c, C (fr v.2.1 c) * X (c, v.2.2.1, false))
    else 0) p

theorem evX_substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (u : Matrix (Fin m) (Fin n) ℂ) :
    evX (substP τ fr p) u = evalPoly p (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) := by
  classical
  unfold evX substP evalPoly
  rw [eval_aeval_subst]
  refine congrArg (fun x => MvPolynomial.eval x p) (funext fun v => ?_)
  obtain ⟨τ', a, j, b⟩ := v
  by_cases hτ : τ' = τ
  · subst hτ
    rw [if_pos rfl, dirAt_self]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply]
    · simp only [↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, map_sum, Complex.star_def]
  · rw [if_neg hτ, dirAt_ne hτ]
    cases b <;> simp

theorem slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) :
    ∀ F ∈ fockA θ V n l s, ∃ Q : PX V.rank n, ∀ u : Matrix (Fin V.rank) (Fin n) ℂ,
      F (xL θ τ (fr * u)) = evX Q u * gs (cLoc l τ) u := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, g, -, rfl⟩ := hF
    refine ⟨C (g 0) * substP τ fr p, fun u => ?_⟩
    show evalPoly p (fun τ' => compAt θ τ' (xL θ τ (fr * u))) * gauss V l s (fun τ' => compAt θ τ' (xL θ τ (fr * u))) *
        g (fun i j => finPart D ((xL θ τ (fr * u)) i j)) = _
    rw [compAt_xL hθ, finPart_xL hθ, gauss_dirAt hfr, ← evX_substP]
    simp only [evX, map_mul, eval_C]
    ring
  | zero => exact ⟨0, fun u => by simp [evX]⟩
  | add F G _ _ hF hG =>
    obtain ⟨Q₁, h₁⟩ := hF
    obtain ⟨Q₂, h₂⟩ := hG
    refine ⟨Q₁ + Q₂, fun u => ?_⟩
    simp only [Pi.add_apply, h₁, h₂, evX, map_add]
    ring
  | smul a F _ hF =>
    obtain ⟨Q, h⟩ := hF
    refine ⟨C a * Q, fun u => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, h, evX, map_mul, eval_C]
    ring

theorem tens_slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) (f : (Fin V.rank → Fin n → ℂ) → ℂ)
    (hf : tens θ τ fr f (psi0 θ V n l s τ) ∈ fockA θ V n l s) : ∃ Q : PX V.rank n, f = fP (cLoc l τ) Q := by
  obtain ⟨Q, hQ⟩ := slice hθ hfr l _ hf
  refine ⟨Q, funext fun (u : Matrix (Fin V.rank) (Fin n) ℂ) => ?_⟩
  have h := hQ u
  have hinv : fr⁻¹ * (fr * u) = u := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
  have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
    have := congrFun (compAt_xL hθ τ (fr * u)) τ
    simpa [dirAt_self] using this
  have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
    unfold psi0
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
    simp only [one_mul]
    exact gaussian_at_zero_eq_one D V.rank n
  simp only [tens] at h
  rw [hc, hinv, hp, mul_one] at h
  exact h

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

