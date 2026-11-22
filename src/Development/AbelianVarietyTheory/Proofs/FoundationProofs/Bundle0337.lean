import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0335

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.UnramDoubleCoset

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
  {ϖ : L} {σ : L →+* L} {q n : ℕ}

def intConj (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  (σ.comp (intL L).subtype).codRestrict (intL L) fun x => by
    show Valued.v (σ x) ≤ 1
    rw [hσ]; exact x.2

open scoped Valued in

theorem exists_dvd_norm_sub_X (hU : IsUnramInv ϖ σ q) (f : Polynomial (intL L)) (hf : f.Monic)
    (hfc : f.map (intConj hU.2.1) = f) (h0 : IsUnit (f.coeff 0)) :
    ∃ p : Polynomial (intL L), f ∣ p * p.map (intConj hU.2.1) - Polynomial.X := by
  haveI := P.fSatake_nontriv hU
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  obtain ⟨hσσ, hσ, h3, h4, ⟨x, hx1, hx2⟩, hq, hcard⟩ := hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  haveI : IsDiscreteValuationRing A := (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    refine NormIntegers.isAdicComplete_of_fg (C := L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let c : A →+* A := intConj hσ
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal A, c x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X A _ c hc hI hω f hf hfc h0

theorem exists_antiJ_frame (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ h ∈ GLint (Fin n) (intL L), cT σ h.1 * 1 * h.1 = antiJ L n := by
  let c := intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hBι : B.map ι = antiJ L n := by
    refine Matrix.ext fun i j => ?_
    show ι (if i.val + j.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite ι, map_one, map_zero]
  have hB : cT c B = B := by
    refine Matrix.ext fun i j => ?_
    show c (if j.val + i.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite c, map_one, map_zero, add_comm j.val]
  have hBB : B * B = 1 := Matrix.map_injective (f := ι) Subtype.val_injective (by
    show (B * B).map ι = (1 : Matrix _ _ _).map ι
    rw [Matrix.map_mul, hBι, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.map_one _ (map_zero ι) (map_one ι)])
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (exists_dvd_norm_sub_X hU) hB
    (IsUnit.of_mul_eq_one _ hBB)
  have h1 : (B * cT c (Polynomial.aeval B p)) * Polynomial.aeval B p = 1 := by rw [Matrix.mul_assoc, hp, hBB]
  refine ⟨bc ι ⟨Polynomial.aeval B p, _, mul_eq_one_comm.1 h1, h1⟩, ⟨_, rfl⟩, ?_⟩
  show cT σ ((Polynomial.aeval B p).map ι) * 1 * (Polynomial.aeval B p).map ι = _
  rw [Matrix.mul_one, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp, hBι]

theorem doubleCoset_one (hU : IsUnramInv ϖ σ q) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L),
    ∀ h ∈ GLint (Fin n) (intL L), ∀ k ∈ GLint (Fin n) (intL L), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors (intL L).subtype (c := intConj hU.2.1) (σ := σ) (fun _ => rfl)
      (fun x => Subtype.ext (hU.1 x)) (exists_dvd_norm_sub_X hU) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hU.2.1 (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2

open GlobalTheory.InertDoubleCoset in

theorem doubleCoset_GU_of_GL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  intro L _ _ _ ϖ σ q n hU g g' a b ha hb e
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := doubleCoset_one hU _
    (conj_mem_UJ σ (inv_frame σ eh) g.2) _ (conj_mem_UJ σ (inv_frame σ eh) g'.2) (h * a * h⁻¹)
    (mul_mem (mul_mem hh ha) (inv_mem hh)) (h * b * h⁻¹) (mul_mem (mul_mem hh hb) (inv_mem hh)) (by rw [e]; group)
  have m : ∀ k ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k' ∈ KU σ n, (k' : GL (Fin n) L) = h⁻¹ * k * h := fun k hk =>
    ⟨⟨_, conj_mem_UJ σ eh hk.1⟩, ⟨conj_mem_UJ σ eh hk.1,
      mul_mem (s := GLint (Fin n) (intL L)) (mul_mem (inv_mem hh) hk.2) hh⟩, rfl⟩
  obtain ⟨l₁, m₁, e₁⟩ := m k₁ h₁
  obtain ⟨l₂, m₂, e₂⟩ := m k₂ h₂
  refine ⟨l₁, m₁, l₂, m₂, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, e₁, e₂]
  calc (g' : GL (Fin n) L) = h⁻¹ * (h⁻¹⁻¹ * g' * h⁻¹) * h := by group
    _ = _ := by rw [e']; group

end GlobalTheory.UnramDoubleCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactor
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.VacMove
open scoped BigOperators Pointwise

namespace GlobalTheory.ArchFree.weilc

theorem exists_scalar {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {L₁ L₁'} (h : Moves D (g : GL (Fin N) (AE D)) L₁)
    (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    ∃ c : ℂ, W.Om g g' e0 = fun z => c *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  have hcc : cc ≠ ⊥ := hc.1.1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := klat _ (moves_one D N) (moves_one D N')
  have k1 := klat (tor0 D cc δ) h h'
  have hT := vac_TT (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc he
  obtain ⟨-, hF, -, hinv⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he
  have hF0 : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 ≠ 0 := by
    intro h0
    rw [h0, iop_zero] at hinv
    exact W.nz hinv.symm
  obtain ⟨hline, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' _ k1
  suffices hG : W.Om g g' e0 ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') from hline _ hG _ hF hF0
  refine ⟨(W.maps g g' e0 hT).1, fun x hx => ?_⟩
  suffices hs : Wd D (tor0 D cc δ) x (W.Om g g' e0) = W.Om g g' e0 by
    rw [hW x hx] at hs; exact congrFun hs
  have hmul : ∀ a ∈ La D (tor0 D cc δ) L₁ L₁', ∀ b ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F,
      Wd D (tor0 D cc δ) a (Wd D (tor0 D cc δ) b F) = Wd D (tor0 D cc δ) (a + b) F := by
    intro a ha b hb F
    obtain ⟨φ, hφ⟩ := wd_wd D (tor0 D cc δ) a b
    have h2 := hφ (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0)
    rw [wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF hb, wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF ha, wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF (add_mem ha hb)] at h2
    have h3 : φ = 1 := by
      by_contra hne
      apply hF0
      have : (φ - 1) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    rw [hφ, h3, one_smul]
  obtain ⟨z', rfl, hz'⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' g g' L₁ L₁' h h' x hx
  have hlatb := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' g g' L₁ L₁' h h'
  have hlat0 := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hlat0
  simp only [← MI_one] at hz' hlatb hlat0
  obtain ⟨m0, hm0, hl0⟩ := W.lift g g' 0 e0 hT
  rw [VacMove.pt_zero, VacMove.wd_zero] at hl0
  set P : Matrix (Fin N') (Fin N') (AE D) := ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP
  set P' : Matrix (Fin N') (Fin N') (AE D) :=
    (((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP'
  set Q : Matrix (Fin N) (Fin N) (AE D) := ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ
  set Q' : Matrix (Fin N) (Fin N) (AE D) :=
    (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ'
  have ePP : P * P' = 1 := Units.mul_inv _
  have eP'P : P' * P = 1 := Units.inv_mul _
  have eQQ : Q * Q' = 1 := Units.mul_inv _
  have eQ'Q : Q' * Q = 1 := Units.inv_mul _
  have e1 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P * (P' * M * Q) * Q' = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ePP, Matrix.one_mul, Matrix.mul_assoc, eQQ, Matrix.mul_one]
  have e2 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P' * (P * M * Q') * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eP'P, Matrix.one_mul, Matrix.mul_assoc, eQ'Q, Matrix.mul_one]
  obtain ⟨n, hn, hb⟩ := MI_bound hcc P Q'
  obtain ⟨n', hn', hb'⟩ := MI_bound hcc P' Q
  obtain ⟨z, hz⟩ := MI_approx hcc (P' * z'.map (inc D) * Q) (n * m0) (Nat.mul_pos hn hm0)
  have hz0 : MI D cc 1 (z.map (inc D)) := by
    simpa using (hz.of_dvd (one_dvd _)).add hz'
  obtain ⟨m, hm, hl⟩ := W.lift g g' z e0 hT
  rw [wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k0 he (hlat0 z hz0)] at hl
  obtain ⟨w, hw⟩ := MI_approx hcc (P * z.map (inc D) * Q') (n' * (m * m0)) (by positivity)
  have hw1 : MI D cc 1 (P' * w.map (inc D) * Q) := by
    have := ((hb' _ _ hw).of_dvd (one_dvd _)).add hz0
    rwa [Matrix.mul_sub, Matrix.sub_mul, e2, sub_add_cancel] at this
  have hd : (w - z').map (inc D) = w.map (inc D) - z'.map (inc D) := by
    ext i j; simp
  have hd' : (z' - w).map (inc D) = z'.map (inc D) - w.map (inc D) := by
    ext i j; simp
  have hdiff : MI D cc m0 ((z' - w).map (inc D)) := by
    have h1 := hb _ _ hz
    rw [Matrix.mul_sub, Matrix.sub_mul, e1] at h1
    have h2 : MI D cc m0 (0 : Matrix (Fin N') (Fin N) (AE D)) := fun i j => ⟨0, zero_mem _, by simp⟩
    have := (h2.sub h1).sub (hw.of_dvd (m := m0) ⟨n' * m, by ring⟩)
    rw [hd']
    convert this using 1
    abel
  have f1 := hl w (hw.of_dvd (m := m) ⟨n' * m0, by ring⟩)
  have f2 := hl0 (z' - w) (by
    intro i j
    have h0 : (0 : Matrix (Fin N') (Fin N) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    exact hdiff i j)
  have hdl : MI D cc 1 (P' * (z' - w).map (inc D) * Q) := by
    rw [hd', Matrix.mul_sub, Matrix.sub_mul]
    exact hz'.sub hw1
  have := hmul _ (hlatb w hw1) _ (hlatb _ hdl) (W.Om g g' e0)
  rw [← f2, ← f1, ← pt_add, add_sub_cancel] at this
  exact this.symm

theorem vacuum_under_adelic_pair : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∃ c : ℂ, Mod1All c ∧ (W.Om g g' e0 = fun z => c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D N'), k' ∈ intG D N' → TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p ((g' * k' : GA D N') : GL (Fin N') (AE D)) → ‖lamC lam c‖ = 1 := by
  intro D cc δ hc N N' hev e0 he W g g' L₁ L₁' h h'
  obtain ⟨c, hce⟩ := exists_scalar hc he W g g' h h'
  have hmod : Mod1All c := by
    obtain ⟨z, x, hz, hx, -⟩ := exists_splitComp D _ (det_norm D g)
    obtain ⟨z', x', hz', hx', -⟩ := exists_splitComp D _ (det_norm D g')
    obtain ⟨sg, hsg, hc2⟩ := (GlobalTheory.T.oddness_condition_holds D cc δ hc N N' hev e0 he W.nz W g g' L₁ L₁' c h h' hce).1 z z' x x' hz hz' hx hx'
    refine modulusOneAllEmbeddings_of_pow (k := 2 * 2) (by norm_num) ?_
    have hs : sg ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
    have h4 : c ^ (2 * 2) = ((W.chV.f x' : ℂˣ) : ℂ) ^ (4 * W.ep) * ((W.chV'.f x : ℂˣ) : ℂ) ^ (4 * W.ep') := by
      rw [pow_mul, hc2, mul_pow, hs, one_mul, ← Units.val_pow_eq_pow_val, ← Units.val_zpow_eq_zpow_val,
        ← Units.val_zpow_eq_zpow_val, ← Units.val_mul, mul_pow]
      congr 2 <;> (rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]; congr 1; push_cast; ring)
    rw [h4]
    exact algebraicModulusOneAll_mul (algebraicModulusOneAll_zpow (GlobalTheory.T.unitaryHeckeCharacter_values D N W.chV x').1 _) (algebraicModulusOneAll_zpow (GlobalTheory.T.unitaryHeckeCharacter_values D N' W.chV' x).1 _)
  refine ⟨c, hmod, hce, fun p _ lam k' hk' ht ht' => ?_⟩
  have hm1 : Moves D (k' : GL (Fin N') (AE D)) (stdL D N') := by
    simpa using moves_mul_int hk' (moves_one D N')
  obtain ⟨a, hae⟩ := exists_scalar hc he W 1 k' (moves_one D N) hm1
  obtain ⟨k, hk, hak⟩ : ∃ k : ℕ, 0 < k ∧ a ^ k = 1 := by
    obtain ⟨z, x, hz, hx, hxi⟩ := exists_splitComp D _ (det_norm D (1 : GA D N))
    obtain ⟨z', x', hz', hx', hxi'⟩ := exists_splitComp D _ (det_norm D k')
    obtain ⟨sg, hsg, hc2⟩ := (GlobalTheory.T.oddness_condition_holds D cc δ hc N N' hev e0 he W.nz W 1 k' _ _ a (moves_one D N) hm1 hae).1
      z z' x x' hz hz' hx hx'
    obtain ⟨m, hm, hxm⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D N' W.chV' x).2.1
      (hxi (det_int D _ (((mem_ratG_intG D N).2.1 1).1 (one_mem _))))
    obtain ⟨m', hm', hxm'⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D N W.chV x').2.1
      (hxi' (det_int D _ (((mem_ratG_intG D N').2.1 k').1 hk')))
    refine ⟨2 * (2 * (m * m')), by positivity, ?_⟩
    have hs : sg ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
    have key : ∀ (u : ℂˣ) (e : ℤ) (r s : ℕ), u ^ r = 1 → r ∣ s → ((u ^ 2) ^ e) ^ s = 1 := by
      rintro u e r _ hu ⟨t, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm e, zpow_mul, zpow_natCast, ← pow_mul, mul_comm 2, mul_assoc,
        pow_mul, hu, one_pow, one_zpow]
    rw [pow_mul, hc2, mul_pow, pow_mul sg, hs, one_pow, one_mul, ← Units.val_pow_eq_pow_val, mul_pow,
      key _ _ m' _ hxm' ⟨2 * m, by ring⟩, key _ _ m _ hxm ⟨2 * m', by ring⟩, one_mul, Units.val_one]
  have hT := vac_TT (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc he
  have hae' : W.Om 1 k' e0 = a • e0 := by
    rw [hae, show La D (tor0 D cc δ) (stdL D N) (stdL D N') = La0 D (tor0 D cc δ) N N' from rfl,
      iop_self D _ (La0 D (tor0 D cc δ) N N') he]
    rfl
  have hprod : W.Om g (g' * k') e0 = fun z => (a * c) *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
    have := W.mul g 1 g' k' e0 hT
    rw [mul_one, hae', W.smul _ _ _ _ hT, hce] at this
    rw [this]
    funext z
    simp [mul_assoc]
  exact norm_lamC_of_root lam hk hak hmod.1
    ((GlobalTheory.T.oddness_condition_holds D cc δ hc N N' hev e0 he W.nz W g (g' * k') L₁ L₁' _ h (moves_mul_int hk' h') hprod).2 p lam ht ht').2

end GlobalTheory.ArchFree.weilc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorVacuumExactConstantEvenRankStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (x x' : (AE D)ˣ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D)) * sgU D x' → Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → W.Om g g' e0 = fun z => ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  first | exact @GlobalTheory.VacuumExact.vacuum_exact | exact GlobalTheory.VacuumExact.vacuum_exact | (intros; apply GlobalTheory.VacuumExact.vacuum_exact <;> assumption)
end

