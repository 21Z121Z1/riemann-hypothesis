import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0101
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0105
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  first | exact @GlobalTheory.abelianScheme_left_isSeparated_of_affine | exact GlobalTheory.abelianScheme_left_isSeparated_of_affine | (intros; apply GlobalTheory.abelianScheme_left_isSeparated_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvdStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfSquareZeroFrame_invariant_eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  first | exact @GlobalTheory.TauUniq.eq_zero_of_tau_dvd | exact GlobalTheory.TauUniq.eq_zero_of_tau_dvd | (intros; apply GlobalTheory.TauUniq.eq_zero_of_tau_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPol
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

open GlobalTheory.OrbitAnalytic in

theorem analyticOnNhd_orbit_pol : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  intro p q r s T0 T1 T2 F Z hZ P
  set Y := Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z with hY
  let f : ℕ → ℝ → F.H := fun k t => F.Om (T0.expt (t • Z)) (F.ι ((omAct p q r s Y ^ k) P))
  have hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t := fun k t =>
    hasDerivAt_orbit (fun t => F.Om (T0.expt (t • Z)))
      (fun s t => by simp only [T0.expt_add Z hZ, map_mul]) _ _
      (by simpa only [pow_succ', Module.End.mul_apply] using F.der Z hZ ((omAct p q r s Y ^ k) P)) t
  have h0 : (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) = f 0 := by
    funext t; simp [f]
  rw [h0]
  refine ⟨fun a _ => ?_, fun k => ?_⟩
  · set S : ℝ := 4 * ∑ l, ∑ l', ‖Y l l'‖ with hS
    have hS0 : 0 ≤ S := by positivity
    refine analyticAt_of_bound f hf ((2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖) (S + 1)⁻¹
      (by positivity) (fun k t => ?_) a
    have hb := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (isFockIsometry_of_fockData F) Y P.totalDegree k P le_rfl).2
    simp only [f]
    rw [F.isom]
    refine hb.trans ?_
    rw [← hS, inv_pow, div_inv_eq_mul]
    calc _ ≤ (S + 1) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖ := by
          gcongr; linarith
      _ = _ := by ring
  · have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [iteratedDeriv_succ, ih]; funext t; exact (hf k t).deriv
    rw [hit]
    simp [f, T0.expt_zero]

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssocEvalStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEval_comul_assoc_of_isEval : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A)) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, constantCoeff (μ i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A)) (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A))) fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  first | exact @GlobalTheory.Chart.Assoc.assoc_eval | exact GlobalTheory.Chart.Assoc.assoc_eval | (intros; apply GlobalTheory.Chart.Assoc.assoc_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditiveStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.cartierDual_tangent_mod | exact GlobalTheory.cartierDual_tangent_mod | (intros; apply GlobalTheory.cartierDual_tangent_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1FormalLogMapMemKer
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.CobLog

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem hasSubst_inl : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst hasSubst_inl]
  simp

theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst hasSubst_inr]
  simp

theorem constantCoeff_subst_one {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 1) :
    constantCoeff (subst a f) = 1 := by
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha ha0, hf, map_one]

theorem constantCoeff_inL {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inL f) = 1 :=
  constantCoeff_subst_one hasSubst_inl (fun _ => constantCoeff_X _) hf

theorem constantCoeff_inR {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inR f) = 1 :=
  constantCoeff_subst_one hasSubst_inr (fun _ => constantCoeff_X _) hf

end SlopeTestRemainingChoices

theorem cob1_formalLog_mem_ker : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ)
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) →
    ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 →
    subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) →
    In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  intro p _ B O Q _ _ _ _ _ θ hF d μ' hμ g hg hmul
  have hsμ : HasSubst μ' := hasSubst_of_constantCoeff_zero hμ
  have hμQ : ∀ i, constantCoeff (up Q μ' i) = 0 := fun i => by
    simp [up, hμ i]
  have hsμQ : HasSubst (up Q μ') := hasSubst_of_constantCoeff_zero hμQ
  set a : MvPowerSeries (Fin d ⊕ Fin d) B := subst μ' g with ha_def
  set b : MvPowerSeries (Fin d ⊕ Fin d) B := inL g * inR g with hb_def
  have ha1 : constantCoeff a = 1 := constantCoeff_subst_one hsμ hμ hg
  have hbL : constantCoeff (inL g) = 1 := constantCoeff_inL hg
  have hbR : constantCoeff (inR g) = 1 := constantCoeff_inR hg
  have hb1 : constantCoeff b = ((1 : Bˣ) : B) := by simp [hb_def, hbL, hbR]
  set h : MvPowerSeries (Fin d ⊕ Fin d) B := a * invOfUnit b 1 with hh_def
  have hab : a = h * b := by
    rw [hh_def, mul_assoc, invOfUnit_mul b 1 hb1, mul_one]
  have hh1 : constantCoeff h = 1 := by
    rw [hh_def, map_mul, ha1, constantCoeff_invOfUnit]
    simp

  have hG : constantCoeff (map (algebraMap B Q) g) = 1 := by simp [hg]
  have key : cob1 (up Q μ') (formalLog (map (algebraMap B Q) g)) =
      formalLog (map (algebraMap B Q) h) := by
    unfold cob1
    have e1 : subst (up Q μ') (formalLog (map (algebraMap B Q) g)) =
        formalLog (map (algebraMap B Q) a) := by
      rw [subst_formalLog hsμQ hG, ha_def, map_subst hsμ]
      rfl
    have e2 : inL (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inL g)) := by
      rw [map_inL]
      exact subst_formalLog hasSubst_inl hG
    have e3 : inR (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inR g)) := by
      rw [map_inR]
      exact subst_formalLog hasSubst_inr hG
    have hmh : constantCoeff (map (algebraMap B Q) h) = 1 := by simp [hh1]
    have hmL : constantCoeff (map (algebraMap B Q) (inL g)) = 1 := by simp [hbL]
    have hmR : constantCoeff (map (algebraMap B Q) (inR g)) = 1 := by simp [hbR]
    have e4 : formalLog (map (algebraMap B Q) a) = formalLog (map (algebraMap B Q) h) +
        formalLog (map (algebraMap B Q) (inL g)) + formalLog (map (algebraMap B Q) (inR g)) := by
      rw [hab, hb_def, ← mul_assoc, map_mul, map_mul,
        formalLog_mul (by rw [map_mul, hmh, hmL, mul_one]) hmR, formalLog_mul hmh hmL]
    rw [e1, e2, e3, e4]
    abel

  have hθb : IsUnit (map θ b) := isUnit_iff_constantCoeff.mpr (by simp [hb_def, hbL, hbR])
  have hθh : map θ h = 1 := by
    have h1 : map θ a = map θ b := by
      rw [ha_def, map_subst hsμ, hmul, hb_def, map_mul, map_inL, map_inR]
    rw [hab, map_mul] at h1
    exact (IsUnit.mul_left_inj hθb).1 (h1.trans (one_mul _).symm)
  have hJ : ∀ x ∈ RingHom.ker θ, ∃ y ∈ RingHom.ker θ, x ^ p = p * y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
    exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
  have hker : ∀ α, coeff α (h - 1) ∈ RingHom.ker θ := by
    intro α
    rw [RingHom.mem_ker, ← coeff_map, map_sub, hθh, map_one, sub_self, map_zero]
  rw [key]
  exact GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF (RingHom.ker θ) hJ (Fin d ⊕ Fin d) h hh1 hker

end GlobalTheory.CobLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdealStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  first | exact @GlobalTheory.CobRel.cocycle_rel_mod | exact GlobalTheory.CobRel.cocycle_rel_mod | (intros; apply GlobalTheory.CobRel.cocycle_rel_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryFrobeniusCommuteModPQuasiLog
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCongr

variable {Q : Type} [CommRing Q]

theorem frob_eq_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem subst_frob {σ τ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    subst a (frob p s g) = subst (fun i => a i ^ p) (map s g) := by
  rw [frob, subst_comp_subst_apply (HasSubst.X_pow hp) ha]
  congr 1
  funext i
  rw [subst_pow ha, subst_X ha]

theorem frob_subst {σ τ : Type} [Finite σ] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    frob p s (subst a g) = subst (fun i => expand p hp (map s (a i))) (map s g) := by
  have ha' : HasSubst fun i => map s (a i) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by
      rw [constantCoeff_map]; exact (ha.const_coeff i).map s
  rw [frob_eq_expand p hp, map_subst ha, expand_subst p hp ha']

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem coeff_pow_sub_expand_mem {B τ : Type} [CommRing B] (p : ℕ) [hp : Fact p.Prime]
    (hnu : ¬IsUnit (p : B)) (σ : B →+* B) (hσ : ∀ b, (p : B) ∣ σ b - b ^ p)
    (g : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (g ^ p - expand p hp.out.ne_zero (map σ g)) ∈ Ideal.span {(p : B)} := by
  haveI : CharP (B ⧸ Ideal.span {(p : B)}) p := CharP.quotient B p hnu
  set π := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hπσ : π.comp σ = (frobenius (B ⧸ Ideal.span {(p : B)}) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
  change coeff α (map π (g ^ p - expand p hp.out.ne_zero (map σ g))) = 0
  rw [map_sub, map_pow, map_expand, map_map, hπσ, ← map_map, ← map_expand,
    map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem dIn_comb {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (he : ∀ i, DIn (⊤ : Ideal B) (e i)) :
    DIn (⊤ : Ideal B) (comb b e) := by
  intro α j
  choose c _ hc using fun i => he i α j
  refine ⟨∑ i, b i * c i, trivial, ?_⟩
  simp only [comb, map_sum, coeff_smul, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc i]; ring

theorem dIn_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (φ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b)) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) (map s f) := by
  intro α j
  obtain ⟨c, -, hc⟩ := hf α j
  refine ⟨φ c, trivial, ?_⟩
  rw [coeff_map, ← hs, ← hc, map_mul, map_natCast]

theorem frob_cong : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  intro p hp O _ hO _ ε F d μ' hμ ι _ e he b
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set f := comb b e with hfdef
  set M := up F.Q μ' with hM
  have hM0 : ∀ i, constantCoeff (M i) = 0 := fun i => by
    rw [hM, up, constantCoeff_map, hμ.const i, map_zero]
  have hsM : HasSubst M := hasSubst_of_constantCoeff_zero hM0
  have hsL : HasSubst fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

  have hX : ∀ (a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.Q), (∀ i, ∃ j, a i = X j) → HasSubst a →
      subst a (frob p F.s f) = frob p F.s (subst a f) := by
    intro a ha has
    rw [subst_frob p hp0 F.s has, frob_subst p hp0 F.s has]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := ha i
    rw [hj, map_X, expand_X]
  have hL := hX _ (fun i => ⟨_, rfl⟩) hsL
  have hR := hX _ (fun i => ⟨_, rfl⟩) hsR

  set u : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => μ' i ^ p with hu
  set v : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => expand p hp0 (map F.σ (μ' i)) with hv
  have hsalg : F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ :=
    RingHom.ext fun x => F.s_alg x
  have hup_u : up F.Q u = fun i => M i ^ p := by
    funext i; rw [up, hu, hM, up, map_pow]
  have hup_v : up F.Q v = fun i => expand p hp0 (map F.s (M i)) := by
    funext i; rw [up, hv, hM, up, map_expand, map_map, map_map, hsalg]
  have key : cob1 M (frob p F.s f) - frob p F.s (cob1 M f) =
      subst (up F.Q u) (map F.s f) - subst (up F.Q v) (map F.s f) := by
    rw [hup_u, hup_v, ← subst_frob p hp0 F.s hsM, ← frob_subst p hp0 F.s hsM]
    have hfs : ∀ a c : MvPowerSeries (Fin d ⊕ Fin d) F.Q,
        frob p F.s (a - c) = frob p F.s a - frob p F.s c := fun a c => by
      simp only [frob_eq_expand p hp0, map_sub]
    unfold cob1 inL inR
    rw [hfs, hfs, hL, hR]
    abel
  rw [key, ← Ideal.mul_top (Ideal.span {(p : F.B)})]
  have hnu : ¬IsUnit (p : F.B) := fun h => hO.out (by simpa using h.map F.θ)
  refine GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ ?_ (Fin d) (Fin d ⊕ Fin d) ⊤
    (map F.s f) u v ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨z ^ p * (p : F.B) ^ (p - 1),
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.sub_pos_of_lt hp.out.one_lt)), ?_⟩
    rw [mul_pow, mul_left_comm, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  · exact dIn_map F.σ F.s F.s_alg f
      (dIn_comb b e fun i => GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hμ ⊤ (e i) (he i))
  · intro i; rw [hu, map_pow, hμ.const i, zero_pow hp0]
  · intro i; rw [hv, constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero]
  · intro i α
    exact coeff_pow_sub_expand_mem p hnu F.σ F.σ_pow (μ' i) α

end GlobalTheory.FrobCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModPStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundaryOne_teichmullerLift_isCocycle_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f ∈ quasiInt p k (Fin d), cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧ swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ p := by
  first | exact @GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem | exact GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem | (intros; apply GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomialStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_cob1_homog_lift_binomial : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (m : ℕ) (h : MvPowerSeries (Fin d) Q), m ≠ 0 → (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) → ∀ a e : Fin d →₀ ℕ, (a + e).degree ≤ m → coeff (Finsupp.sumElim a e) (cob1 (up Q μ) h) = if a ≠ 0 ∧ e ≠ 0 then (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h else 0 := by
  first | exact @GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial | exact GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial | (intros; apply GlobalTheory.CobHom.coeff_cob1_homogeneous_binomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffQuasiLogarithmIntegralLowDegree
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.QLogInt

theorem coeff_integral_of_QL : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ l : MvPowerSeries (Fin d) Q, QL μ ⊤ l → ∀ α : Fin d →₀ ℕ, α.degree ≤ p → (∀ i, α ≠ Finsupp.single i p) → ∃ b : B, coeff α l = algebraMap B Q b := by
  intro p hpf B O Q _ _ _ _ θ hF d μ hμ l hl α hdeg hne
  have hp : p.Prime := hpf.out
  classical
  by_cases h0 : α = 0
  · refine ⟨0, ?_⟩
    rw [h0, coeff_zero_eq_constantCoeff_apply, hl.1, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Finsupp.ext h)
  have hkle : α k ≤ p := (Finsupp.le_degree k α).trans hdeg
  have hklt : α k < p := by
    refine lt_of_le_of_ne hkle fun hkp => hne k ?_
    have hs : Finsupp.single k p ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    have hsplit : α = Finsupp.single k p + (α - Finsupp.single k p) := (add_tsub_cancel_of_le hs).symm
    have hd : (α - Finsupp.single k p).degree = 0 := by
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at h2
      omega
    rw [(Finsupp.degree_eq_zero_iff _).1 hd, add_zero] at hsplit
    exact hsplit
  have hcop : Nat.Coprime (α k) p :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk) hklt)))
  obtain ⟨u, hu⟩ := hF.unit_coprime (α k) hcop
  obtain ⟨b', -, hb'⟩ := GlobalTheory.QLogDiff.dIn_of_QL p B O Q θ hF d μ hμ ⊤ l hl α k
  refine ⟨(↑u⁻¹ : B) * b', ?_⟩
  have h1 : algebraMap B Q (↑u⁻¹ : B) * (α k : Q) = 1 := by
    rw [← map_natCast (algebraMap B Q) (α k), ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, ← hb']
  linear_combination (-(coeff α l)) * h1

end GlobalTheory.QLogInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeStrip

theorem completedLBoundedInStrips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  intro E _ _ _ I _ φ hφ χ n hu hi hn
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar E χ hu
  have hβ : ∀ β : 𝓞 E, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : E) := by
    intro β h0 h1
    have h0' : (β : E) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, hi (Units.mk0 _ h0')]
    simp only [wt, Units.val_mk0, zpow_neg, Finset.prod_inv_distrib]
  have hle : ∀ a, ‖X a‖ ≤ 1 := fun a => by
    by_cases ha : a = ⊥
    · simp [ha, hX0]
    by_cases ha' : a ⊔ m = ⊤
    · exact (hXn a ha ha').le
    · simp [hXz a ha']
  obtain ⟨r, c, B, M, F, hB, hM, hper, hinv, hdec⟩ := GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries E I φ n m X hm hX0 hXm hXn hXz hβ
  choose Λ hΛd hΛb hΛe using fun k => GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips E I φ hφ n hn (M k) (F k) (hM k) (hper k) (hinv k)
  have hB0 : ∀ k, ((B k : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  refine ⟨fun s => ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * Λ k s, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · intro s
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).mul ((differentiableAt_id.const_cpow (Or.inl (hB0 k))))).mul ((hΛd k).differentiableAt)
  · refine ⟨∑' a : Ideal (𝓞 E), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
    · rw [GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X hX0 hX1 hXm hle s hs]
      convert GlobalTheory.HeckeOne.hasProd_exp hu hs using 1
      simp only [hXP, GlobalTheory.HeckeOne.cf]
    · rw [hdec s hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hΛe k s hs]
      ring
  · intro a b hab
    choose C hC using fun k => hΛb k a b hab
    refine ⟨∑ k, ‖c k‖ * ((B k : ℝ) ^ b * |C k|), fun s h1 h2 => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_natCast_cpow_of_pos (hB k)]
    have hB1 : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB k
    gcongr
    exact (hC k s h1 h2).trans (le_abs_self _)

end GlobalTheory.HeckeStrip
end
end

