import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.HalfDuality

variable {D : D7}

theorem exists_lift (t : Datum.EAf D) : ∃ Z : AE D, infPart D Z = 0 ∧ toEAf D Z = t :=
  ⟨GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm t),
   GlobalTheory.AdForm.infPart_liftFin _, GlobalTheory.AdForm.toEAf_liftFin t⟩

theorem trace_id (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) :=
  GlobalTheory.T.toEAf_orientedHermitianForm_eq_trace_frames S T βS βT k y

theorem local_dual (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) :=
  GlobalTheory.T.exists_dualElement_standardChar_splitPrime ψ hψ e₁ PP he₁

theorem psi_trace_split (ψ : AddChar (AF D.host.F) ℂ) (a Z Z₁ : AE D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z)) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z₁)) * ψ (Algebra.trace (AF D.host.F) (AE D) (a * (Z - Z₁))) := by
  rw [← AddChar.map_add_eq_mul, ← map_add, ← mul_add, add_sub_cancel Z₁ Z]

theorem redM_apply_of_mem (PP : Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) (i : Fin b) (j : Fin a)
    (h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : redM PP N i j = resS D.host.F PP ⟨N i j, h⟩ := by
  simp only [redM]
  exact dif_pos h

set_option maxHeartbeats 800000 in

theorem local_dual_unit (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) (u : Formalism.L2.Herm.intAf D.host.F D.host.E) (hu : resS D.host.F PP u ≠ 0) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c * u →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  obtain ⟨c, h1, h2⟩ := local_dual ψ hψ e₁ PP he₁
  haveI := PP.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := PP.asIdeal) hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
  have hra : resS D.host.F PP (oToS D.host.F D.host.E a) * resS D.host.F PP u = 1 := by
    rw [resS_oToS, ha, mul_comm, hb]
  refine ⟨c * ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D),
    fun Z hZ r hr hZr => ?_, fun Z hZ hZu => ?_⟩
  · refine h1 Z hZ (oToS D.host.F D.host.E a * r) (by rw [map_mul, hr, mul_zero]) ?_
    rw [hZr, MulMemClass.coe_mul, mul_assoc]
  · obtain ⟨Z₁, hZ₁, hZ₁c⟩ := exists_lift (D := D) c
    have hr : resS D.host.F PP (oToS D.host.F D.host.E a * u - 1) = 0 := by
      rw [map_sub, map_mul, hra, map_one, sub_self]
    have h0 := h1 (Z - Z₁) (by rw [map_sub, hZ, hZ₁, sub_zero]) (oToS D.host.F D.host.E a * u - 1) hr (by
      rw [map_sub, hZu, hZ₁c, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, mul_sub, mul_one,
        mul_assoc])
    intro hc
    apply h2 Z₁ hZ₁ hZ₁c
    rw [psi_trace_split ψ _ Z Z₁, h0, mul_one] at hc
    exact hc

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_half_frMapO (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (e : AE D) (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : Datum.EAf D => exists_lift (D := D) t
  let Y : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (Y i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hz' : toEAf D e • z = z := Matrix.ext fun i j => hz i j
    have h3 : toEAf D e • Y = Y := by
      show toEAf D e • HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val = HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz']
    have hY : (Matrix.of fun i j => e * L (Y i j) : WO S T).map (toEAf D) = Y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL]
      exact congrFun (congrFun h3 i) j
    unfold frMapO
    rw [hY]
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val Y) βS.val =
        HMul.hMul (HMul.hMul (HMul.hMul ((βT⁻¹).val) βT.val) z) (HMul.hMul (βS⁻¹).val βS.val) := by
      simp only [Y, Matrix.mul_assoc]
    rw [e1, Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_one]

theorem trace_mul_single {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Datum.EAf D)) (b : Fin n) (a : Fin m) (t0 : Datum.EAf D) :
    Matrix.trace (M * Matrix.single b a t0) = M a b * t0 := by
  rw [Matrix.trace, Finset.sum_eq_single a]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory.HalfDuality

set_option maxHeartbeats 1600000 in
theorem GlobalTheory.HalfDuality.exists_dual_half : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  (∃ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ≠ 0) →
  ∃ y : WO (Vc D i) (Wc D i), IsHalf (cA D (cA D e)) y ∧
    (∀ k : WO (Vc D i) (Wc D i), IsHalf (cA D e) k → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) → (∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) = 0) →
      R.ψ (symplO (Vc D i) (Wc D i) k y) = 1) ∧
    R.ψ (symplO (Vc D i) (Wc D i) x y) ≠ 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx hint hex
  obtain ⟨PP, hPP, hred⟩ := hex
  have hψ : IsStdChar D R.ψ (-1) := hL.2.2.2.2.2.1.std
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  obtain ⟨⟨es, hes, -⟩, -⟩ := he
  obtain ⟨a, b, hab⟩ : ∃ a b, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) a b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hred (Matrix.ext hn)
  have hu : resS D.host.F PP ⟨_, hint a b⟩ ≠ 0 := by
    rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]
    exact hab
  obtain ⟨c₀, h1, h2⟩ := GlobalTheory.HalfDuality.local_dual_unit R.ψ hψ (es PP) PP (hes PP hPP) _ hu
  obtain ⟨y, hyh, hy0, hyz⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e hee
    (Matrix.single b a (toEAf D e * c₀)) (fun i' j' => by
      rw [Matrix.single_apply]
      split_ifs
      · rw [← mul_assoc, ← map_mul, hee]
      · rw [mul_zero])
  have hinf : ∀ k, infPart D (hO (Vc D i) (Wc D i) y k) = 0 := fun k => by
    simp only [hO, map_sum, map_mul, hy0, mul_zero, Finset.sum_const_zero]
  have hfin : ∀ k, IsHalf (cA D e) k → toEAf D (hO (Vc D i) (Wc D i) y k) =
      c₀ * frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k a b := fun k hk => by
    rw [GlobalTheory.HalfDuality.trace_id _ _ (R.βV i) (R.βW i), hyz, GlobalTheory.HalfDuality.trace_mul_single, mul_comm (toEAf D e) c₀, mul_left_comm,
      mul_comm _ (toEAf D e), GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hk]
  have hs : ∀ k, R.ψ (symplO (Vc D i) (Wc D i) k y) =
      (R.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hO (Vc D i) (Wc D i) y k)))⁻¹ := fun k => by
    rw [GlobalTheory.OrientedHeis.symplO_skew y k, AddChar.map_neg_eq_inv]
    rfl
  refine ⟨y, by rw [Formalism.L2.Theta.cA_cA]; exact hyh, fun k hk hki hkr => ?_, ?_⟩
  · rw [hs, h1 _ (hinf k) ⟨_, hki a b⟩ (by rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]; exact congrFun (congrFun (hkr PP hPP) a) b) (hfin k hk), inv_one]
  · rw [hs]
    exact fun h => h2 _ (hinf x) (hfin x hx) (inv_eq_one.1 h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalScalarPrimeToConjPolarisationLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.GenChoice

theorem exists_gen_avoid {R K ι : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : FractionalIdeal (nonZeroDivisors R) K) (hA : A ≠ 0) (Qs : Finset ι)
    (Q : ι → Ideal R) (hQ : ∀ i ∈ Qs, (Q i).IsPrime) (hQ0 : ∀ i ∈ Qs, Q i ≠ ⊥) :
    ∃ γ : K, γ ≠ 0 ∧ ∃ s : R, (∀ i ∈ Qs, s ∉ Q i) ∧
      (∀ c ∈ A, ∃ r : R, algebraMap R K r = algebraMap R K s * γ⁻¹ * c) ∧
      algebraMap R K s * γ ∈ A := by
  obtain ⟨a, I, ha, hAI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul A
  have hI : I ≠ ⊥ := by
    rintro rfl
    apply hA
    rw [hAI, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hinj := IsFractionRing.injective R K
  obtain ⟨g, hgI, hg0, hgQ⟩ : ∃ g ∈ I, g ≠ 0 ∧ ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by
    rcases Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨g, hg, hg0, by simp⟩
    · have hQp0 : (∏ i ∈ Qs, Q i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => hQ0 i hi
      obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_left : I * (∏ i ∈ Qs, Q i) ≤ I)
        (mul_ne_zero hI hQp0)
      have hgI : g ∈ I := by
        rw [← hg]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
      have key : ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by
        intro i hi h
        have hle : (∏ j ∈ Qs, Q j) ≤ Q i := Ideal.prod_le_inf.trans (Finset.inf_le hi)
        have h1 : I ≤ I * Q i := by
          calc I = I * (∏ j ∈ Qs, Q j) ⊔ Ideal.span {g} := hg.symm
            _ ≤ I * Q i := sup_le (Ideal.mul_mono_right hle) h
        have h2 : I * Q i = I * ⊤ := by
          rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h1
        exact (hQ i hi).ne_top (mul_left_cancel₀ hI h2)
      refine ⟨g, hgI, ?_, key⟩
      rintro rfl
      apply key i0 hi0
      rw [Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgI)
  have hJQ : ∀ i ∈ Qs, ¬ J ≤ Q i := fun i hi h => hgQ i hi (by rw [hJ]; exact Ideal.mul_mono_right h)
  obtain ⟨s, hsJ, hsQ⟩ : ∃ s ∈ J, ∀ i ∈ Qs, s ∉ Q i := by
    rcases Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · exact ⟨0, J.zero_mem, by simp⟩
    · by_contra hcon
      push_neg at hcon
      have hsub : (J : Set R) ⊆ ⋃ i ∈ (Qs : Set ι), (Q i : Set R) := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := hcon x hx
        exact Set.mem_biUnion hi hxi
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime i0 i0 (fun i hi _ _ => hQ i hi)).1 hsub
      exact hJQ i hi hle
  have ha' : algebraMap R K a ≠ 0 := by
    intro h; exact ha (hinj (by rw [h, map_zero]))
  have hg' : algebraMap R K g ≠ 0 := by
    intro h; exact hg0 (hinj (by rw [h, map_zero]))
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, mul_ne_zero (inv_ne_zero ha') hg', s, hsQ, ?_, ?_⟩
  · intro c hc
    rw [hAI, FractionalIdeal.mem_singleton_mul] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    have hxs : x * s ∈ Ideal.span {g} := by
      rw [hJ]; exact Ideal.mul_mem_mul hx hsJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hxs
    refine ⟨r, ?_⟩
    have hr' : algebraMap R K r * algebraMap R K g = algebraMap R K x * algebraMap R K s := by
      rw [← map_mul, ← map_mul, hr]
    field_simp
    linear_combination hr'
  · rw [hAI, FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap R K (s * g), FractionalIdeal.mem_coeIdeal_of_mem _ (I.mul_mem_left s hgI), ?_⟩
    rw [map_mul]
    field_simp

theorem exists_global_scalar_prime_to_conj_polarisationLattice : ∀ (D : D7) (n : ℕ) (Λ ΛT : Lt D.host.E n), IsAA Λ ΛT → ∀ P : Finset (Formalism.L2.DIV.Pl D.host.E), ∃ γ : D.host.E, γ ≠ 0 ∧ ∃ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) ∧ (∀ v ∈ Λ, ((s : D.host.E) * γ⁻¹) • v ∈ ΛT) ∧ (∀ v ∈ ΛT, ((s : D.host.E) * γ) • v ∈ Λ) := by
  intro D n Λ ΛT h P
  obtain ⟨γ, hγ, s, hsQ, hint, hmem⟩ := exists_gen_avoid D.host.AA (GlobalTheory.FinPl.LocGen.AA_ne_zero D) P
    (fun PP => conjI PP.asIdeal)
    (fun PP _ => by rw [GlobalTheory.LiftIdeal.conjI_eq_map]; exact (GlobalTheory.LiftIdeal.isMaximal_map D PP).isPrime)
    (fun PP _ => by
      rw [GlobalTheory.LiftIdeal.conjI_eq_map, Ne, Ideal.map_eq_bot_iff_of_injective (f := ((GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))) (GlobalTheory.LiftIdeal.conjO D).injective]
      exact PP.ne_bot)
  refine ⟨γ, hγ, s, hsQ, ?_, ?_⟩
  · intro v hv
    have hv' := (h v).1 hv
    induction hv' using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨c, hc, t, ht, rfl⟩ := hu
      obtain ⟨r, hr⟩ := hint c hc
      rw [smul_smul]
      have : ((s : D.host.E) * γ⁻¹ * c) = algebraMap (𝓞 D.host.E) D.host.E r := by
        rw [hr]
      rw [this, algebraMap_smul]
      exact ΛT.smul_mem r ht
    | zero => rw [smul_zero]; exact ΛT.zero_mem
    | add x y _ _ hx hy =>
      rw [smul_add]; exact ΛT.add_mem (hx ((h x).2 ‹_›)) (hy ((h y).2 ‹_›))
    | neg x _ hx =>
      rw [smul_neg]; exact ΛT.neg_mem (hx ((h x).2 ‹_›))
  · intro v hv
    rw [h]
    exact AddSubgroup.subset_closure ⟨(s : D.host.E) * γ, hmem, v, hv, rfl⟩

end GlobalTheory.GenChoice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeOfMemSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.L2.DIV Formalism.L2.Indef NumberField GlobalTheory.Chain GlobalTheory.Chain.IoLift
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowTest.WVec

variable {D : D7}

theorem tprod_ne_zero {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_inclK_ne {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h : KSm M) :
    ∃ y : KT M, inclK h y ≠ 0 := by
  have hu : ∀ τ, ∃ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, u ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun e => hx0 (congrArg Subtype.val e)⟩
  choose u hu using hu
  refine ⟨PiTensorProduct.tprod ℂ u, fun e => tprod_ne_zero hu ?_⟩
  exact GlobalTheory.Chain.IoLift.FinTensor.inclK_injective h (e.trans (map_zero _).symm)

theorem exists_ne_of_mem_span {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) {s : Set E} {x : E} (hx : x ∈ Submodule.span ℂ s) (h : L x ≠ 0) : ∃ z ∈ s, L z ≠ 0 := by
  by_contra hn
  push_neg at hn
  exact h ((Submodule.span_le (p := LinearMap.ker L)).2 (fun z hz => hn z hz) hx)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnVec_congr (d d' : ChainVec R) : ∀ n, (∀ k < n, d.polY k = d'.polY k) → d.dnVec n = d'.dnVec n
  | 0, _ => rfl
  | n + 1, h => by
    show d.dnVec n ∘ₗ R.ItY n (d.polY n) = d'.dnVec n ∘ₗ R.ItY n (d'.polY n)
    rw [dnVec_congr d d' n fun k hk => h k (by omega), h n (by omega)]

def ofPol (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) : ChainVec R := ⟨p, 0, 0⟩

theorem exists_w_ne (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : ∀ k, ChainPar D k) (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hθ : R.models_inf) :
    ∃ cv : ChainVec R, cv.w ≠ 0 := by
  have hm := D.R.two_le_m
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hch.ωY hch.ωX hch.vY hch.vX
  have stepY : ∀ k, k + 1 < D.R.m → ∃ (h : KSm (R.MY k)) (h' : KSm (R.MY (k + 1))),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItY k φ (inclK h' y) = x} := fun k hk => by
    obtain ⟨hW, hV⟩ := hS.1 A.μ0 ⟨k, by omega⟩ hk
    exact GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors hD hH D ⟨k, by omega⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left (by omega))
      (min_eq_left (by omega)) _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY A.μ0 k) (R.vY A.μ0 k) hW hV (R.ItY k)
      (hch.ItY A.μ0 k hk)
  have stepX : ∃ (h : KSm (R.MY (D.R.m - 1))) (h' : KSm R.MX),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItX φ (inclK h' y) = x} := by
    obtain ⟨hW, hV⟩ := hS.2 A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
    exact GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors hD hH D ⟨D.R.m - 1, by omega⟩ (min (D.R.m - 1) D.R.m) D.R.m (min_eq_left (Nat.sub_le _ _))
      (by show D.R.m = D.R.m - 1 + 1; omega) _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ hθ (hC _) (R.ωX A.μ0) (R.vX A.μ0) hW hV
      R.ItX (hch.ItX A.μ0)
  have key : ∀ n, n + 1 ≤ D.R.m → ∃ (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (h : KSm (R.MY n))
      (y : KT (R.MY n)), (ofPol (R := R) p).dnVec n (inclK h y) ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨h, -, -⟩ := stepY 0 (by omega)
      obtain ⟨y, hy⟩ := exists_inclK_ne h
      exact ⟨fun _ => 0, h, y, hy⟩
    | succ n ih =>
      intro hn
      obtain ⟨p, h, y, hy⟩ := ih (by omega)
      obtain ⟨h1, h2, hsp⟩ := stepY n (by omega)
      obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
      refine ⟨Function.update p n φ, h2, y', ?_⟩
      show (ofPol (R := R) (Function.update p n φ)).dnVec n
        (R.ItY n ((Function.update p n φ) n) (inclK h2 y')) ≠ 0
      rw [Function.update_self, dnVec_congr (ofPol (Function.update p n φ)) (ofPol p) n
        fun k hk => Function.update_of_ne (by omega) _ _]
      exact hz
  obtain ⟨p, h, y, hy⟩ := key (D.R.m - 1) (by omega)
  obtain ⟨h1, h2, hsp⟩ := stepX
  obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
  refine ⟨⟨p, φ, inclK h2 y'⟩, ?_⟩
  show ChainVec.dnVec ⟨p, φ, inclK h2 y'⟩ (D.R.m - 1) (R.ItX φ (inclK h2 y')) ≠ 0
  rwa [dnVec_congr ⟨p, φ, inclK h2 y'⟩ (ofPol p) (D.R.m - 1) fun k _ => rfl]

end GlobalTheory.RowTest.WVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.Published GlobalTheory.Chain.RealIt

namespace GlobalTheory.Chain.ItPairObj

theorem exists_record (hD : DiscreteSeriesCover) (hH : HarishChandraModules) :
    ∃ X : ProvA, ChosenSeries X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X := by
  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam (GlobalTheory.CoverDS.exists_hasParam hD)
  have a1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have a2 : admH2 X := GlobalTheory.JointHarm.fock_polynomials X
  have a3 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hD X hX
  have a5 : admQ5 X := hH.admQ5_of_harishChandraModules X
  have a6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have a7 : admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have a8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have a4 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X a3 a5 a7 a8
  have h1 := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨X, hX, h1, GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X a1 a2 a3 a4 a5 a6 a7 a8 h1⟩

theorem itPair_of_rows (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  obtain ⟨X, hX, h1, h2⟩ := exists_record hD hH
  exact itPair D X hX h1 h2 hF hV hB hC

theorem itPair_holds (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7) : ItPair D :=
  itPair_of_rows hD hH D (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D) (GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D) (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) GlobalTheory.Contr.contraction

end GlobalTheory.Chain.ItPairObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTypeCarriesOnePartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_carriesOnePart : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → UpInj R.toRealDat → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') := by
  first | exact @GlobalTheory.CarriesOne.parts_eq_of_carries | exact GlobalTheory.CarriesOne.parts_eq_of_carries | (intros; apply GlobalTheory.CarriesOne.parts_eq_of_carries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatKernelPairingRationalPointsInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatKernelPairing_rationalPoints_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  first | exact @GlobalTheory.KerRat.flat_kernel_rat | exact GlobalTheory.KerRat.flat_kernel_rat | (intros; apply GlobalTheory.KerRat.flat_kernel_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialTmulSchwartzBruhatMemAlgebraicDataStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomial_tmul_schwartzBruhat_mem_algebraicData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  first | exact @GlobalTheory.SquareAgree.pureA_mem_algD | exact GlobalTheory.SquareAgree.pureA_mem_algD | (intros; apply GlobalTheory.SquareAgree.pureA_mem_algD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_negSpace_frameChange_conjSubst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT v : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ), IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f P = pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (v τ).map (starRingEnd ℂ)) (fun τ => (((u τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.FockNegSubst.pureTensorO_negSp_subst | exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst | (intros; apply GlobalTheory.FockNegSubst.pureTensorO_negSp_subst <;> assumption)
end

