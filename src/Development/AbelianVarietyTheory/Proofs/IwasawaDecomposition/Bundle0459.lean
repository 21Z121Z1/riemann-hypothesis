import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicLiftTypePrimeReductions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepLevel_smaller_at_finite_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  first | exact @GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | exact GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | (intros; apply GlobalTheory.StepLevelShrink.exists_stepLevel_shrink <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TrueTheta

open GlobalTheory.NormSum.UnramHecke GlobalTheory.VacuumScalar

theorem exists_family_of_curve : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  intro D cc δ hc
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).1
  obtain ⟨κ, k1, k2, k3⟩ := exists_kappa D
  obtain ⟨χ, hχ, hdet⟩ := exists_chi D κ k1 k2
  have hv : ∀ N N' : ℕ, ∃ e0 : VC D N N' → ℂ, Even (N * N') → oddE0 D cc δ t0 N N' e0 ∧ e0 ≠ 0 := by
    intro N N'
    by_cases h : Even (N * N')
    · obtain ⟨e0, he⟩ := GlobalTheory.Vacuum.exists_vacuum D cc δ hc t0 ht0 N N' h
      exact ⟨e0, fun _ => he⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose e0 he0 using hv
  let e : FamE D := fun N N' L L' =>
    (χ (detId D (stdL D N) L) ^ ((N' / 2 : ℕ) : ℤ) * χ (detId D (stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))) •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N')
  have hsc : ∀ {N N' : ℕ} (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L →
      Moves D (g' : GL (Fin N') (AE D)) L' → e N N' L L' = ((scal κ g g' : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N') := by
    intro N N' g g' L L' hL hL'
    simp only [e]
    rw [hdet N 1 g _ _ (moves_one D N) hL, hdet N' 1 g' _ _ (moves_one D N') hL', inv_one, inv_one, one_mul, one_mul,
      scal, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  have hW : ∀ N N', Even N → Even N' → ∃ W : WeilO D cc δ N N' (e0 N N'),
      (∀ τ, 2 * (0 : ℤ) = W.ep * W.chV.n τ + (N : ℤ)) ∧ (∀ τ, 2 * (0 : ℤ) = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧
      ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
        ((scal κ g g' : ℂˣ) : ℂ) ∈ Qbar ∧ W.Om g g' (e0 N N') = e N N' L L' := by
    intro N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨W, w1, w2, w3⟩ := k3 cc δ hc N N' hN hN' _ a.1 b
    exact ⟨W, w1, w2, fun g g' L L' hL hL' =>
      ⟨(w3 g g' L L' hL hL').1, by rw [(w3 g g' L L' hL hL').2, hsc g g' L L' hL hL']⟩⟩
  have hTT := fun N N' => (GlobalTheory.ThetaLevels.levels_closed D cc δ hc N N').1
  have hmove : ∀ N N', Even N → Even N' → ∀ (g h : GA D N) (g' h' : GA D N') L L₁ L' L₁',
      Moves D (g : GL (Fin N) (AE D)) L → Moves D (h : GL (Fin N) (AE D)) L₁ →
      Moves D (g' : GL (Fin N') (AE D)) L' → Moves D (h' : GL (Fin N') (AE D)) L₁' →
      e N N' L₁ L₁' = ((scal κ (g⁻¹ * h) (g'⁻¹ * h') : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (e N N' L L') := by
    intro N N' hN hN' g h g' h' L L₁ L' L₁' m1 m2 m3 m4
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨M, hM⟩ := exists_moves (g⁻¹ * h)
    obtain ⟨M', hM'⟩ := exists_moves (g'⁻¹ * h')
    have s0 := sd_of_moves (moves_one D N)
    have s0' := sd_of_moves (moves_one D N')
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
      (Or.inr ⟨_, _, sd_of_moves hM, sd_of_moves hM', rfl⟩) _ a.1).2.1
    have hio := GlobalTheory.WeilInter.om_iop D cc δ hc (GlobalTheory.InertSign.delta_ne_zero hc) N N' _ W g 1 (g⁻¹ * h) g' 1 (g'⁻¹ * h')
      _ L M L₁ _ L' M' L₁' (moves_one D N) (moves_one D N') (by rwa [mul_one]) (by rwa [mul_one]) hM hM'
      (by rwa [mul_inv_cancel_left]) (by rwa [mul_inv_cancel_left]) _ a.1
    rw [← (w h h' _ _ m2 m4).2, ← (w g g' _ _ m1 m3).2, ← hio]
    conv_lhs => rw [← mul_inv_cancel_left g h, ← mul_inv_cancel_left g' h', W.mul _ _ _ _ _ (hTT N N' _ _ s0 s0' _ a.1),
      (w _ _ _ _ hM hM').2, hsc _ _ _ _ hM hM']
    exact W.smul _ _ _ _ (hTT N N' _ _ (sd_of_moves hM) (sd_of_moves hM') _ hI)
  refine ⟨χ, e, hχ, fun N N' L L' ⟨hN, hN', hL, hL'⟩ => ?_, fun N N' L L' hN hN' γ γ' => ?_,
    fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L hL
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L' hL'
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _
      (Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩)
      (Or.inr ⟨_, _, hL, hL', rfl⟩) _ a.1).2.1
    change e N N' L L' ∈ Th D (tor0 D cc δ) L L' ∧ e N N' L L' ≠ 0 ∧ ∃ M : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M
    rw [hsc g g' L L' hg hg']
    exact ⟨GlobalTheory.InertSign.ThSp_smul _ hI, smul_ne_zero (Units.ne_zero _) (lattice_facts hc a.1 b hg hg').1,
      exists_coef_field D cc δ hc t0 ht0 N N' (hN.mul_right _) _ a L L' hL hL' _ (w g g' L L' hg hg').1⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨γA, hγ⟩ := exists_rat γ
    obtain ⟨γA', hγ'⟩ := exists_rat γ'
    obtain ⟨W, w1, w2, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hT := hTT N N' _ _ (sd_of_moves (moves_one D N)) (sd_of_moves (moves_one D N')) _ a.1
    have := GlobalTheory.RatEqui.oddEq_of_even D cc δ hc t0 ht0 N N' hN hN' _ a W γA γA' _ _ (fun _ => 0) (fun _ => 0) hγ hγ' w1 w2
      _ (W.maps g g' _ hT)
    change pull D (tor0 D cc δ) _ _ (e N N' _ _) = e N N' _ _
    rw [← (w _ _ _ _ (moves_smulLat hγ hg) (moves_smulLat hγ' hg')).2, W.mul _ _ _ _ _ hT, this, (w _ _ _ _ hg hg').2]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h', hh'⟩ := exists_moves_of_selfDual D N' L''.1 L''.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g g g' h' _ _ _ _ hg hg hg' hh', hdet _ _ _ _ _ hg' hh', scal, inv_mul_cancel g]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h, hh⟩ := exists_moves_of_selfDual D N L₁.1 L₁.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g h g' g' _ _ _ _ hg hh hg' hg', hdet _ _ _ _ _ hg hh, scal, inv_mul_cancel g']
    funext z
    simp

end GlobalTheory.TrueTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicLiftTypePrimeReductionsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelic_lift_typePrime_reductions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)), ∃ t : GA B n,
      (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
        bc (prV (E := B.host.E) v) t = 1) ∧
      ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelic_twist_diagonal_at_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.Mem.Col2.TwUnit.exists_tw | exact GlobalTheory.Mem.Col2.TwUnit.exists_tw | (intros; apply GlobalTheory.Mem.Col2.TwUnit.exists_tw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exp_two_pi_I_div_mul_eq_stdAddChar_mul (p q : ℕ) [NeZero p] [NeZero q] (hpq : Nat.Coprime p q) (T : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) =
      ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) *
        ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  set A : ℤ := Nat.gcdA q p
  set B : ℤ := Nat.gcdB q p
  have hb : (1 : ℤ) = (q : ℤ) * A + (p : ℤ) * B := by
    have h := Nat.gcd_eq_gcd_ab q p
    rw [Nat.Coprime.gcd_eq_one hpq.symm] at h
    simpa using h
  have hA : ((q : ZMod p))⁻¹ = ((A : ℤ) : ZMod p) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod p)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero] at this
    exact this.symm
  have hB : ((p : ZMod q))⁻¹ = ((B : ℤ) : ZMod q) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod q)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, zero_add] at this
    exact this.symm
  have e1 : ((q : ZMod p))⁻¹ * (T : ZMod p) = ((A * T : ℤ) : ZMod p) := by
    rw [hA]; push_cast; ring
  have e2 : ((p : ZMod q))⁻¹ * (T : ZMod q) = ((B * T : ℤ) : ZMod q) := by
    rw [hB]; push_cast; ring
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hbC : (1 : ℂ) = (q : ℂ) * (A : ℂ) + (p : ℂ) * (B : ℂ) := by exact_mod_cast hb
  push_cast
  field_simp
  linear_combination (T : ℂ) * hbC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_e0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg b j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 b).1
    · exact ((X.weightVectorsIntegral _).2.2 b).2.2.1
  refine wInt_of_zmod X kv.1 hg ?_
  have hb := b.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dif_pos h1, if_neg (by omega), sub_zero]; exact (X.gramIntegral _ _).1
  rw [dif_neg h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dif_pos h2, if_neg (by omega), sub_zero]; exact hW _
  rw [dif_neg h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dif_pos h4, if_neg (by omega), sub_zero]; exact (X.formsAtZero.2 b).1
  rw [dif_neg h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dif_pos h3]
    have h := (X.gramIntegral b ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩).2.2
    by_cases e : j.1 = 2 * D.R.rS + D.R.k - b.1
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by simp only; omega))] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (by have := congrArg Fin.val h'; simp only at this; omega))] at h
  · rw [dif_neg h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.SymFrame GlobalTheory.Mem.SymChar in

theorem GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg hEw hs m j
  have hm := m.2
  have hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2) :=
    fun c hc => wInt_of_zmod X kv.1 hg hc
  have hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2) := by
    intro v hv
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]
    exact hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)
  have hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈
      wInt X (D.naut.plGw kv.1 kv.2) := by
    intro l
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)
    rw [map_sub, apply_ite (sigA X.B.I), map_zero] at h
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]
    by_cases hl : l = m
    · simp only [hl, if_true] at h ⊢
      have := add_mem (hZ _ h) hs
      convert this using 1
      ring
    · simp only [hl, if_false] at h ⊢
      simpa using hZ _ h
  unfold symVec epsW
  rw [if_neg hEw]
  unfold GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dif_pos h1, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1
  rw [dif_neg h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dif_pos h2]
    have e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val := by
      rw [Fin.ext_iff, Fin.val_rev]; simp only [Fin.val_mk]; constructor <;> intro h <;> omega
    have := hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)
    by_cases h' : j.val = D.R.rS + D.R.k - 1 - m.val
    · rw [if_pos h']; rwa [if_pos (e.2 h')] at this
    · rw [if_neg h']; rwa [if_neg (fun hh => h' (e.1 hh))] at this
  rw [dif_neg h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dif_pos h4, if_neg (by omega), sub_zero]
    exact hS _ (X.weightVectorsIntegral m).1
  rw [dif_neg h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dif_pos h3, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 _).2.1
  · rw [dif_neg h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact zero_mem _

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf

namespace GlobalTheory.Mem.SymChar.ZPair
open GlobalTheory.Mem.SymFrame

theorem rank_eq' (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

theorem zmod_hA_z0_symVec (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    ZMod' X.B.I X.B.g (hA X.B.I X.z0 (symVec X w j) - (if j.val = D.R.rS + D.R.k then -1 else 0)) := by
  have hr := rank_eq' D
  have hj := j.2
  unfold symVec GlobalTheory.SeeConjRead.flagV epsW
  split_ifs
  · exfalso; omega
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).2.1
  · rw [sub_neg_eq_add]; exact X.formsAtZero.1
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).2
  · exfalso; omega

theorem hA_z0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg j
  exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 hg (zmod_hA_z0_symVec D X _ j)

end GlobalTheory.Mem.SymChar.ZPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOfEntries
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem sum_ite_val {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : c < m) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = f ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h)
  · simp

theorem sum_ite_val_zero {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : m ≤ c) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = 0 :=
  Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem isBlock_of_frame {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ)
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN (fun i j : Fin N => M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
      (fun a b : Fin n => M' (Fin.cast hq.symm a) (Fin.cast hq.symm b)) 1 := by
  subst hp hq hN
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e := congrFun (congrFun h1 (Br.iC rfl a)) b
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iC rfl a : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := b.2; omega), sum_ite_val _ _ (show ((Br.iC rfl a : Fin (q+1)) : ℕ) < q from a.2)] at e
    exact e
  · have e := congrFun h2 (Br.iC rfl a)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_neg (by have := a.2; simp [Br.iC]; omega)] at e
    exact e
  · have e := congrFun (congrFun h1 (Br.iL rfl)) a
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iL rfl : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := a.2; omega), sum_ite_val_zero _ _ (by simp [Br.iL])] at e
    exact e
  · have e := congrFun h2 (Br.iL rfl)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_pos (by simp [Br.iL])] at e
    exact e

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem isBlock_of_entries {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
    (hA' : ∀ i j, A' i j = M' (Fin.cast hq.symm i) (Fin.cast hq.symm j))
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN A A' 1 := by
  have e1 : A = fun i j => M (Fin.cast hp.symm i) (Fin.cast hp.symm j) := funext fun i => funext fun j => hA i j
  have e2 : A' = fun i j => M' (Fin.cast hq.symm i) (Fin.cast hq.symm j) := funext fun i => funext fun j => hA' i j
  subst e1 e2
  exact isBlock_of_frame hp hq hN M M' h1 h2

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem invMat_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] [Fact (1 < g)]
    (T S : Q →+ Q) (hST : ∀ q, S (T q) = q) (β : ι → Q) (hβ : ∀ i, g • β i = 0)
    (N N' : Matrix ι ι (ZMod g)) (hNN' : N * N' = 1)
    (hT : ∀ i, T (β i) = ∑ j, (N j i).val • β j) (m : ι) :
    S (β m) = ∑ i, (N' i m).val • β i := by
  have e1 : T (∑ i, (N' i m).val • β i) = ∑ l, ((N * N') l m).val • β l := by
    rw [map_sum]
    simp only [map_nsmul, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e2 : ∑ l, (((1 : Matrix ι ι (ZMod g))) l m).val • β l = β m := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.one_apply_eq, ZMod.val_one, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl, ZMod.val_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hNN', e2] at e1
  rw [← e1, hST]

end GlobalTheory.Mem.SymFrame

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  intro D X kv hg u hu k hk N hN m
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  haveI : Fact (1 < D.host.g kv.1) := ⟨(D.host.g_prime kv.1).one_lt⟩
  let W := (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
  have hk' : k⁻¹ ∈ X.B.I.Kset := Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I hk
  let fT := (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
  let fS := (Matrix.mulVecLin (X.B.I.fmat k⁻¹)).toAddMonoidHom
  let T := QuotientAddGroup.map W W fT (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
  let S := QuotientAddGroup.map W W fS (fun v hv => fmat_mulVec_mem_wLf X _ hk' hv)
  have key : ∀ a b : VA X.B.I, a - b ∈ wLf X (D.naut.plGw kv.1 kv.2) ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    show a - b ∈ W ↔ _
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have hST : ∀ q, S (T q) = q := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H v =>
      show QuotientAddGroup.mk' W (X.B.I.fmat k⁻¹ *ᵥ (X.B.I.fmat k *ᵥ v)) = QuotientAddGroup.mk' W v
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul X.B.I k, Matrix.one_mulVec]
  have hβ : ∀ i, D.host.g kv.1 • QuotientAddGroup.mk' W (u i) = 0 := fun i => by
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
      ⟨_, hg, by simp⟩ (y := u i) (hu i)
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
      simp [map_natCast]
    rw [e, Nat.cast_smul_eq_nsmul] at h1
    exact h1
  have hT : ∀ i, T (QuotientAddGroup.mk' W (u i)) =
      ∑ j, ((N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • QuotientAddGroup.mk' W (u j) := by
    intro i
    have := (key _ _).1 (by simpa only [Nat.cast_smul_eq_nsmul] using hN i)
    rw [map_sum] at this
    simp only [map_nsmul] at this
    rw [← this]; rfl
  have h := invMat_quot T S hST (fun i => QuotientAddGroup.mk' W (u i)) hβ
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hT m
  simp only [Nat.cast_smul_eq_nsmul]
  rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

end GlobalTheory.Mem.SymFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0DecorationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPtOf_mul_J0_decoration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG E n SG), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG E n SG) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG E n SG × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.isPtOf_mul_J0 | exact GlobalTheory.Mem.Col2.TopCh.isPtOf_mul_J0 | (intros; apply GlobalTheory.Mem.Col2.TopCh.isPtOf_mul_J0 <;> assumption)
end

