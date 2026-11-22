import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingAffineLinearMapAddEqAddFrM
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SqrtNegPrimeMemKur
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.SqrtUnram

theorem sqrt_neg_prime_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), q.Prime → q % 4 = 3 → l ≠ q →
    ∀ x : PadicAlgCl l, x ^ 2 = -(q : PadicAlgCl l) → x ∈ Loc.MaximalUnramifiedExtension l := by
  intro l _ q hq h4 hne x hx
  exact GlobalTheory.MemN.SelfGood.sqrt_mem q hq h4 _
    (fun z hz => GlobalTheory.MemN.SelfGood.root_mem_Kur hq.pos
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).1 hd)) hz) x hx

end GlobalTheory.SqrtUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumModGPeriodValues
section
noncomputable section

namespace GlobalTheory.PadicUnfold.Period

open Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData

def extZero {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ) (y : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0)

theorem extZero_single {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) (s : Fin (n' + c')) (l : Fin (n + c)) :
    extZero c' c y (Pi.single s 1) l = if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0 := by
  simp [extZero, Matrix.toLin'_apply]

theorem periodXX1_add_smul {k : Type} [CommRing k] {n' c' n c : ℕ} (a : k)
    (x y : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Loc.FC n' c' n c → k) :
    Loc.xx1 (x + a • y) t = Loc.xx1 x t + a • extZero c' c y := by
  refine hom_ext fun s l => ?_
  rw [LinearMap.add_apply, Pi.add_apply, LinearMap.smul_apply, Pi.smul_apply, linearMap_unfolding_apply_single, linearMap_unfolding_apply_single,
    extZero_single]
  by_cases hf : Loc.IsFree n' n c l.1 s.1
  · have hs : ¬ s.1 < n' := not_lt.2 hf.1
    simp [hf, hs]
  · by_cases hs : s.1 < n'
    · by_cases hl : l.1 < n <;> simp [hf, hs, hl]
    · simp [hf, hs]

theorem chArg_smul_extZero {k : Type} [CommRing k] {n' n c : ℕ} (a : k)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) : Loc.chArg (a • extZero (c + 1) c y) = 0 := by
  rw [chArg_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, extZero_single, dif_neg (by simp; omega), smul_zero]

variable {g : ℕ} [Fact g.Prime]

end GlobalTheory.PadicUnfold.Period
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem tateDual_matRep_crys : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  intro l _ P K LL k M hT hM hC
  haveI : IsTopologicalRing ↥LL.1 := by
    first
      | infer_instance
      | exact Subring.instIsTopologicalRing LL.1.toSubring
      | exact inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  have hχ := GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum P K LL
  have hinv : Continuous fun g : ↥(GK K) => M g⁻¹ := hM.comp continuous_inv
  have hc : Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) := by
    change Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose
    exact hχ.smul hinv.matrix_transpose
  refine ⟨hc, ?_⟩
  exact hT (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) M hM)
    (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) _ hc) (dotProductBilin ↥LL.1 ↥LL.1)
    (TwistDualLoc.isDual1_dot (P.PD K) M) hC

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopRows

theorem nuRow_tauPl_of_isTopPl {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (z : Bool × HH D) (hz : IsTopPl D z) :
    DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) = (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) ∧
    0 ≤ DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ≤ L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨hz1, hz2⟩ := hz
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hτ : (D.eTau (tauPl D z) : D.R.GG) = D.R.tau1 (⟨z.2, hz2⟩ : D.host.TT) := by
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]
  obtain ⟨hu1, huk⟩ := L.top_u (tauPl D z) ⟨z.2, hz2⟩ hk hτ
  obtain ⟨-, hw⟩ := L.win_top (j + 1) (by omega) (by omega) (tauPl D z) ⟨z.2, hz2⟩ hτ
  have ha : aL L z.2 = L.aT ⟨z.2, hz2⟩ := by unfold aL; rw [dif_pos hz2]
  have hb : bL L z.2 = L.bT ⟨z.2, hz2⟩ := by unfold bL; rw [dif_pos hz2]
  have hwe : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  have hkc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have e1 : DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ 0 hk, D.hcW_first u _ hk, ha, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [hu1]
    ring
  have e2 : DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) =
      (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ (D.R.k - 1) (by omega), D.hcW_last u _ hk, hb, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [huk, hkc]
    ring
  refine ⟨e1, e2, (RowWeightLemmas.nuRow_pos D u j hj _ _ (by unfold Ranks.N; omega)).le, ?_⟩
  have hka : 0 ≤ kaJ D (j + 1) := by
    unfold kaJ
    push_cast
    have : (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    positivity
  rw [e2, hb]
  change wPl D (j + 1) z ≤ _ at hw
  linarith

theorem eta_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.etaSz ≤ L.sc.b' / L.sc.x := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h1 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    le_mul_of_one_le_left L.etaSz_pos.le (by nlinarith)
  have h2 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le hx (le_mul_of_one_le_right hx.le hn1)
  exact h1.trans (P.mteta.trans h2)

theorem top_rows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) 0 = (aL (Fm.L x i) z.2 : ℝ) + (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) = (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) - (bL (Fm.L x i) z.2 : ℝ) ∧ 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ≤ 2 * (Fm.L x i).sc.b' / (Fm.L x i).sc.x := by
  intro eps Fm
  refine ⟨0, fun x _ hx1 i u j hj z hz => ?_⟩
  have h4 := eta_le (Fm.params x hx1 i)
  obtain ⟨e1, e2, e3, e4⟩ := nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz
  refine ⟨e1, e2, e3, e4.trans ?_⟩
  rw [mul_div_assoc]
  linarith

end GlobalTheory.TopRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).Box := by
  intro D L C j ε τ φ hR
  have hb := (GlobalTheory.T.roundedSizeBound_window L C hR).1
  have hw := (GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C hR).2.2
  have hnt := fun g => GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR
  have hth := fun g => GlobalTheory.T.floor_size_bounds_at_thick_embedding L g j
  obtain ⟨hC, h100, hroom, hwb, -, hCb⟩ := hR
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := L.t_win.1
  have ht' : 1 ≤ D.R.t := by exact_mod_cast ht
  have hLw : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : 0 ≤ L.sc.b' := by linarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by
    have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hb'
    linarith
  have hw0 : (0 : ℝ) ≤ wHat D := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
  have hE : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold etaHat
    push_cast
    have := Nat.floor_le hη.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ bHat L
    have : (1 : ℝ) ≤ bHat L := by linarith
    exact_mod_cast this
  · show 1 ≤ wHat D
    unfold wHat
    omega
  · show 20 * wHat D ≤ bHat L
    have : (20 : ℝ) * wHat D ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * etaHat L ≤ bHat L
    have : (20 : ℝ) * etaHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * sHat L ≤ bHat L
    have : (20 : ℝ) * sHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · intro i
    show ((etaHat L : ℕ) : ℤ) < szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
    generalize letter τ φ i = g
    have hsz : L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by
      by_cases hT : Thick D.host g
      · have := (hth g hT).1
        linarith
      · exact (hnt g hT).1
    have key : ((etaHat L : ℕ) : ℤ) + D.R.t + 1 < ⌊(hcAt D g).e j⌋ := by
      have : ((etaHat L : ℕ) : ℝ) + D.R.t + 1 < (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    unfold szT
    split_ifs <;> omega

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThick
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_large_of_roomy {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (100 : ℝ) ≤ bHat L ∧ 2 * (etaHat L : ℝ) + sHat L ≤ (bHat L : ℝ) / 10 := by
  obtain ⟨hC, hw, hr, hwb, -, hb⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hCL : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := le_trans (mul_le_mul_of_nonneg_right hCL hb') hb
  have h1 : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    have := Nat.floor_le he.le
    unfold etaHat
    push_cast
    linarith
  have h2 : (sHat L : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have h3 : ⌈L.sc.b⌉₊ ≤ bHat L + D.R.t := by
    unfold bHat
    omega
  have h4 : L.sc.b ≤ (bHat L : ℝ) + D.R.t := by
    have h5 : ((⌈L.sc.b⌉₊ : ℕ) : ℝ) ≤ (bHat L : ℝ) + D.R.t := by exact_mod_cast h3
    exact le_trans (Nat.le_ceil _) h5
  constructor <;> linarith

theorem conjWord_hypAT {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ)
    (hR : Roomy L C) (hl : 11 ≤ l) (hτ : Thick D.host τ) :
    (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  obtain ⟨hord, hplc⟩ := GlobalTheory.T.complexConjugation_orbit_one_realPlace τ
  have hth : ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
    intro i
    rw [GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ (D.R.cc) hR i]
    unfold Thick at hτ ⊢
    rw [hplc i]
    exact hτ
  refine ⟨⟨?_, ?_, ?_⟩, hth⟩
  · rw [hord]; exact even_two
  · exact (GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ (D.R.cc) rfl).2
  · intro M hM i
    obtain ⟨hB, hroom⟩ := bHat_large_of_roomy L C hR
    have hη : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
    have hS : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
    have key : ∀ k, (bHat L : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ∧
        ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ≤ (bHat L : ℝ) + etaHat L := by
      intro k
      obtain ⟨h1, h2⟩ := hth k
      have h1' : ((bHat L : ℕ) : ℤ) ≤ (pageWord L j ε τ (D.R.cc)).sz k := h1
      have h2' : (pageWord L j ε τ (D.R.cc)).sz k ≤ ((bHat L : ℕ) : ℤ) + ((etaHat L : ℕ) : ℤ) := h2
      exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    obtain ⟨k, hk⟩ := hM.1
    have hMk := key k
    rw [hk] at hMk
    have hi := key i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingWord_large_size_numerical_bounds l (bHat L) (etaHat L) (sHat L) (M : ℝ)
      ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) hl hB hη hS hroom
      (abs_le.2 ⟨by linarith [hMk.1], by linarith [hMk.2]⟩)
      (abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    refine ⟨?_, h1, h2⟩
    have : (1 : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) := by linarith [hi.1]
    exact_mod_cast this

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBounds
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem abs_szT_sub_floor_le {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) :
    |((szT P j s : ℤ) : ℝ) - ((⌊P.e j⌋ : ℤ) : ℝ)| ≤ ((R.t : ℝ) + 1) / 2 := by
  have h0 : (0 : ℤ) ≤ ((R.t : ℤ) + 1) / 2 := by omega
  have h1 : 2 * (((R.t : ℤ) + 1) / 2) ≤ (R.t : ℤ) + 1 := by omega
  have h0' : (0 : ℝ) ≤ ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : 2 * ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) ≤ (R.t : ℝ) + 1 := by exact_mod_cast h1
  unfold szT
  generalize ((R.t : ℤ) + 1) / 2 = q at h0' h1'
  cases s
  · simp only [Bool.false_eq_true, if_false, Int.cast_sub]
    rw [abs_le]; constructor <;> linarith
  · simp only [if_true, Int.cast_add]
    rw [abs_le]; constructor <;> linarith

theorem pageWord_not_thick_size : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  intro D L C j ε τ φ hR i hi
  have hnt : ¬ Thick D.host (letter τ φ i) := fun h => hi ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  have h1 := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C (letter τ φ i) j hR hnt
  have h2 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 (letter τ φ i) j hnt
  refine ⟨((⌊(hcAt D (letter τ φ i)).e j⌋ : ℤ) : ℝ), h1.1, ?_, h1.2, ?_⟩
  · exact_mod_cast h2
  · exact abs_szT_sub_floor_le _ j _

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  intro D L C j ε τ φ hR i
  by_cases h : Thick D.host (letter τ φ i)
  · exact Or.inl ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  · right
    have h1 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 _ j h
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) ≤ ((wHat D : ℕ) : ℤ)
    unfold szT wHat
    push_cast
    split_ifs <;> omega

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.YoungDiagramCardEqSumRowLenRange
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem youngDiagram_card_eq_sum_rowLen_range (μ : YoungDiagram) (n : ℕ) (h : μ.colLen 0 ≤ n) :
    μ.card = ∑ r ∈ Finset.range n, μ.rowLen r := by
  have hmap : ∀ c ∈ μ.cells, c.1 ∈ Finset.range n := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) h1
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.1 h2) h
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun c hc => hmap c hc)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.rowLen_eq_card]
  rfl

theorem nuD_card_eq_sum_nuRow : ∀ (D : D7), NuRowOK D → ∀ (u : D.what₂.Word), ∀ j < D.R.m, ∀ (z : Bool × HH D), (((nuD D u j z).card : ℕ) : ℝ) = ∑ r ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) (tauPl D z) r := by
  intro D hD u j hj z
  rw [youngDiagram_card_eq_sum_rowLen_range _ _ (nuD_rows D u j z), Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hD u j hj z r, if_pos (Finset.mem_range.1 hr)]

end GlobalTheory
end

