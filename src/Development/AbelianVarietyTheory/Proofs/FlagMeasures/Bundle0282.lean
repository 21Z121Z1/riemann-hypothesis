import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqMatrixCoeffLeFormalDegree
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllBound

theorem exists_inner_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : E}
    (hv : v ≠ 0) : ∃ ξ : E, ⟪v, ξ⟫_ℂ = 1 ∧ ⟪ξ, v⟫_ℂ = 1 := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  refine ⟨(⟪v, v⟫_ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [inner_smul_right]
    exact inv_mul_cancel₀ hvv
  · rw [inner_smul_left, map_inv₀, inner_conj_symm]
    exact inv_mul_cancel₀ hvv

theorem lintegral_hsNormSq_ell_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν l l' hl hl'

  obtain ⟨w₀, hw₀, hlw₀⟩ := hl.2.1
  obtain ⟨w₀', hw₀', hlw₀'⟩ := hl'.2.1
  obtain ⟨ξ, hξ₁, hξ₂⟩ := exists_inner_eq_one hlw₀
  obtain ⟨ξ', hξ₁', hξ₂'⟩ := exists_inner_eq_one hlw₀'

  have hbe : (⟪ξ, be (psiGen k r z c) π μS σ w₀ w₀ ξ⟫_ℂ).re = 1 := by
    rw [hl.2.2 w₀ hw₀ w₀ hw₀, rankOneInnerOperator_apply, inner_smul_right, hξ₁, hξ₂]
    simp
  have hbe' : (⟪ξ', be (psiGen k r z' c') π' μS' σ w₀' w₀' ξ'⟫_ℂ).re = 1 := by
    rw [hl'.2.2 w₀' hw₀' w₀' hw₀', rankOneInnerOperator_apply, inner_smul_right, hξ₁', hξ₂']
    simp
  have hbound := GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν
    w₀' hw₀' w₀ hw₀ ξ ξ'
  rw [hbe, hbe', mul_one, mul_one] at hbound
  refine le_trans (le_of_eq ?_) hbound

  have hreg : ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' := ae_iff.mpr hν.2.1
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with γ hγ
  rw [(GlobalTheory.T.iint_eq_ell_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' _ hγ).2
    w₀ hw₀ w₀' hw₀' ξ ξ', hξ₁, hξ₂']
  simp

end GlobalTheory.SgInf.EllBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSidesStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_data_both_amplitude_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.Amp.Side.both_sides | exact GlobalTheory.Amp.Side.both_sides | (intros; apply GlobalTheory.Amp.Side.both_sides <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimes
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HL

theorem GCoord.c_eq_one_of_gS_mem : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  intro D X Y T T' F00 F'0 FP G c P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  have hgp : gpart p = D.host.g i := by
    have hne := D.host.g_ne
    fin_cases i
    · simp [gpart, hchar]
    · simp [gpart, hchar, Ne.symm hne]
  have hδ := Y.δ_pin p i hi
  have hne : ∀ j, ((D.host.g j : ℕ) : D.host.E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hneF : ∀ j, ((D.host.g j : ℕ) : D.host.F) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have key := c.c_eq p
  have hone : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((G.c p).val) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [key]
    change algebraMap _ _ (Y.δ p) * _ = _
    rw [hδ, ← (D.s.atP p).compat, ← map_mul, map_one]
    have h1 : algebraMap D.host.F D.host.E ((D.host.g 0 : D.host.F) * D.host.g 1 / D.host.g i) *
        ((uP p : ℚ) : D.host.E) = 1 := by
      simp only [uP, hgp, gS, map_div₀, map_mul, map_natCast]
      push_cast
      have := hne 0; have := hne 1; have := hne i
      field_simp
    rw [h1, map_one]
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hv : ((G.c p).val : (D.s.atP p).Fp) = 1 :=
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective hone
  exact Units.ext hv

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulTheta
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.c_mul_gS_eq_delta_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _
  have hg : gS D ≠ 0 := by
    show D.host.g 0 * D.host.g 1 ≠ 0
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  refine ⟨hg, fun p => ?_⟩

  have hE : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  let cp : (D.s.atP p).Fp := (G.c p).val
  have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := c.c_eq p
  have hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E) := by
    rw [uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]
  have h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    apply (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
    rw [map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]
    congr 1
    rw [← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]

  have h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    have hA := (Y.agree p).2.2.2.2.2
    have hs := D.s_split p
    have wc := c.c p
    rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg
    ·
      have hgg : (G.S p).gg = false := wc.gg_none hM
      have hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hn.1, if_neg hn.2]
      rw [Frames.th, hgg, hgp]
      exact (if_neg (by decide)).trans Nat.cast_one.symm
    · simp [hM, hD] at hA
    · simp [hM, hD] at hA
    · have hgs := wc.gg_some g hM
      simp only [hM, hD] at hA
      have hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      have hq := sg.q_eq
      have hgp : gpart p = Loc.resChar p := by
        unfold gpart
        rcases hn with h | h
        · rw [if_pos h, h]
        · by_cases h0 : Loc.resChar p = D.host.g 0
          · rw [if_pos h0, h0]
          · rw [if_neg h0, if_pos h, h]
      simp only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]
      exact hq
  exact h1.trans (congrArg (Y.δ p * ·) h2.symm)

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermWeightEqCharacterMulInv
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.TermPhase

section Tri

variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {r : ℕ}

def lowSpan (E : Type) [CommRing E] [Module E V] (f : Fin (r + 1) → V) (b : ℕ) : Submodule E V := Submodule.span E (f '' {c | (c : ℕ) < b})

theorem lowSpan_mono (f : Fin (r + 1) → V) {b b' : ℕ} (h : b ≤ b') :
    lowSpan E f b ≤ lowSpan E f b' :=
  Submodule.span_mono (Set.image_mono fun _ hc => lt_of_lt_of_le hc h)

abbrev IsTriW (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop := ∀ b : Fin (r + 1), g (f b) - f b ∈ lowSpan E f b

theorem map_lowSpan {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : IsTriW f g) (b : ℕ) :
    ∀ x ∈ lowSpan E f b, g x ∈ lowSpan E f b := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    have h1 : f c ∈ lowSpan E f b := Submodule.subset_span ⟨c, hc, rfl⟩
    have h2 : g (f c) - f c ∈ lowSpan E f b := lowSpan_mono f (le_of_lt hc) (hg c)
    have := add_mem h2 h1
    simpa using this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem exists_pre_lowSpan {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : IsTriW f g) :
    ∀ b : ℕ, ∀ x ∈ lowSpan E f b, ∃ y ∈ lowSpan E f b, g y = x := by
  intro b
  induction b with
  | zero =>
    intro x hx
    have h0 : lowSpan E f 0 = ⊥ := by simp [lowSpan]
    rw [h0, Submodule.mem_bot] at hx
    exact ⟨0, zero_mem _, by simp [hx]⟩
  | succ b ih =>
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      have hc' : (c : ℕ) < b ∨ (c : ℕ) = b := by
        have : (c : ℕ) < b + 1 := hc
        omega
      rcases hc' with hlt | heq
      · obtain ⟨w, hw, hgw⟩ := ih (f c) (Submodule.subset_span ⟨c, hlt, rfl⟩)
        exact ⟨w, lowSpan_mono f (Nat.le_succ b) hw, hgw⟩
      · obtain ⟨w, hw, hgw⟩ := ih (g (f c) - f c) (by rw [← heq]; exact hg c)
        refine ⟨f c - w, sub_mem (Submodule.subset_span ⟨c, hc, rfl⟩) (lowSpan_mono f (Nat.le_succ b) hw), ?_⟩
        rw [map_sub, hgw]; abel
    | zero => exact ⟨0, zero_mem _, map_zero g⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      exact ⟨y + y', add_mem hy hy', map_add g y y'⟩
    | smul a x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨a • y, Submodule.smul_mem _ a hy, map_smul g a y⟩

def triSub (f : Fin (r + 1) → V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | IsTriW f g}
  one_mem' := by
    rw [Set.mem_setOf_eq]; intro b
    show f b - f b ∈ lowSpan E f b
    simp
  mul_mem' := by
    intro g g' hg hg'
    rw [Set.mem_setOf_eq] at hg hg' ⊢
    intro b
    show g (g' (f b)) - f b ∈ lowSpan E f b
    have : g (g' (f b)) - f b = g (g' (f b) - f b) + (g (f b) - f b) := by rw [map_sub]; abel
    rw [this]
    exact add_mem (map_lowSpan hg b _ (hg' b)) (hg b)
  inv_mem' := by
    intro g hg
    rw [Set.mem_setOf_eq] at hg ⊢
    intro b
    show g.symm (f b) - f b ∈ lowSpan E f b
    obtain ⟨y, hy, hgy⟩ := exists_pre_lowSpan hg b (f b - g (f b)) (by
      have := neg_mem (hg b)
      simpa using this)
    have : g.symm (f b) - f b = g.symm (f b - g (f b)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [this, ← hgy, LinearEquiv.symm_apply_apply]
    exact hy

end Tri

theorem hf_add_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hf L Hm (a • x) y = a * hf L Hm x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem nset_sub {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) :
    Fr.NSet ⊆ ((triSub (E := E) Fr.f : Subgroup (V ≃ₗ[E] V)) : Set (V ≃ₗ[E] V)) := by
  rintro g ⟨-, hF, hP⟩ b
  induction b using Fin.lastCases with
  | last =>
    have hz : Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
      show ∀ x ∈ H.X Fr.f, H.h (Fr.f (Fin.last r)) x = 0
      intro x hx
      have h0 : H.h x (Fr.f (Fin.last r)) = 0 := by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨a, rfl⟩ := hy
          exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
        | zero => exact H.h_zero_left _
        | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
        | smul a x _ hx => rw [H.h_smul_left, hx, mul_zero]
      rw [H.h_herm x, h0, map_zero]
    have h1 := hP _ hz
    have h2 : H.X Fr.f ≤ lowSpan E Fr.f (Fin.last r : ℕ) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a.castSucc, by simp, rfl⟩
    exact h2 h1
  | cast a =>
    have hv : Fr.f a.castSucc ∈ Fr.Fj (a.val + 1) := Submodule.subset_span ⟨a, by simp, rfl⟩
    have h1 := hF (a.val + 1) (by have := a.isLt; omega) _ hv
    simp only [Nat.add_sub_cancel] at h1
    have h2 : Fr.Fj a.val ≤ lowSpan E Fr.f (a.castSucc : ℕ) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨a', ha', rfl⟩
      exact ⟨a'.castSucc, by simpa using ha', rfl⟩
    exact h2 h1

theorem mem_span_of_mem_N {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) : n (Fr.f b) ∈ Submodule.span E (Set.range Fr.f) := by
  have hT : IsTriW Fr.f n := (Subgroup.closure_le (triSub (E := E) Fr.f)).mpr (nset_sub Fr) hn
  have h1 : lowSpan E Fr.f b ≤ Submodule.span E (Set.range Fr.f) :=
    Submodule.span_mono (Set.image_subset_range _ _)
  have := add_mem (h1 (hT b)) (Submodule.subset_span ⟨b, rfl⟩ : Fr.f b ∈ Submodule.span E (Set.range Fr.f))
  simpa using this

theorem coef_eq {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (e : V ≃ₗ[E] (Fin n → E)) (g : Fin (r + 1) → Fin n → E) (gs : Fin r → Fin n → E)
    (hg : ∀ a, g a = e (Fr.f a)) (hd : ∀ a j, hf M.L Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (j : Fin r) (x : V) (hx : x ∈ Submodule.span E (Set.range Fr.f)) :
    H.h x (Fr.es j) = hf M.L Hm (e x) (gs j) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [← hg a, hd a j]
    induction a using Fin.lastCases with
    | last =>
      have h0 : H.h (Fr.f (Fin.last r)) (Fr.es j) = 0 := by
        rw [H.h_herm (Fr.es j) (Fr.f (Fin.last r)), Fr.h_sz j, map_zero]
      rw [h0, if_neg (Fin.castSucc_lt_last j).ne']
    | cast i =>
      rw [Fr.h_es i j]
      simp [Fin.castSucc_inj]
  | zero => rw [H.h_zero_left, map_zero, hf_zero_left']
  | add x y _ _ hx hy => rw [H.h_add_left, map_add, hf_add_left', hx, hy]
  | smul a x _ hx => rw [H.h_smul_left, map_smul, hf_smul_left', hx]

end Loc

theorem om_eq_psi_mul_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r k : ℕ) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : WCoord P S) (d : LocNG.Datum P) (t : Loc.Term V M r), LocNG.IsTermOver P d t → ∀ m m' : S.GLV, (∀ b, c.e (t.f b) = m (S.f b)) → (∀ b, c.e (t.f' b) = m' (S.f' b)) → LocNG.om P t = S.psi m * (S.psi' m')⁻¹ := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r k P S c d t hT m m' hm hm'
  obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := hT
  have hth : LocNG.theta M = S.th := by
    unfold LocNG.theta Frames.th
    cases hs : M.split with
    | none => simp [c.gg_none hs]
    | some g =>
      obtain ⟨h1, h2⟩ := c.gg_some g hs
      simp [h1, h2]
  have h1 : (∑ a : Fin r, H.h (t.f a.succ) (P.A.es a)) = ∑ j, S.h (m (S.f j.succ)) (S.es j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm]
    refine coef_eq P.A S.Hm c.e S.f S.es c.f_eq (fun a j => S.dual a j) j _ ?_
    rw [hfn]; exact mem_span_of_mem_N P.A hn _
  have h2 : (∑ a : Fin r, H.h (t.f' a.succ) (P.B.es a)) = ∑ j, S.h (m' (S.f' j.succ)) (S.es' j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm']
    refine coef_eq P.B S.Hm c.e S.f' S.es' c.f'_eq (fun a j => S.dual' a j) j _ ?_
    rw [hfn']; exact mem_span_of_mem_N P.B hn' _
  simp only [LocNG.om, LocNG.FrameD.psiOf, LocNG.FrameD.coefSum, Frames.psi, Frames.psi', Frames.psiOf,
    Frames.coef, hth, h1, h2]

end GlobalTheory.HL.TermPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalUnitaryTop

theorem linearIndependent_iff_smul_basis {K S V ι α : Type} [Field K] [CommRing S] [Algebra K S]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower K S V] [Fintype ι] [Fintype α]
    (b : Module.Basis ι K S) (X : α → V) :
    LinearIndependent S X ↔ LinearIndependent K fun p : ι × α => b p.1 • X p.2 := by
  refine ⟨fun h => linearIndependent_smul b.linearIndependent h, fun h => ?_⟩
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 := h (fun p => b.repr (g p.2) p.1) (by
    rw [← hg, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr (g j), Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => (smul_assoc _ _ _).symm)
  exact b.ext_elem fun k => by simpa using h0 (k, i)

theorem isOpen_linearIndependent {K S ι α β : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing S] [Algebra K S] [TopologicalSpace S] [IsModuleTopology K S] [IsTopologicalRing S]
    [Fintype ι] [Fintype α] [Fintype β] (b : Module.Basis ι K S) :
    IsOpen {X : α → β → S | LinearIndependent S X} := by
  let e : (β → S) ≃ₗ[K] (β → ι → K) := LinearEquiv.piCongrRight fun _ => b.equivFun
  have hb : Continuous b.equivFun :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc : Continuous fun (X : α → β → S) (p : ι × α) => e (b p.1 • X p.2) := by
    refine continuous_pi fun p => continuous_pi fun j => ?_
    have : Continuous fun X : α → β → S => b p.1 * X p.2 j := by fun_prop
    exact hb.comp this
  have ho := (isOpen_setOfPred_linearIndependent (𝕜 := K) (E := β → ι → K) (ι := ι × α)).preimage hc
  convert ho using 1
  ext X
  rw [Set.mem_ofPred_eq, linearIndependent_iff_smul_basis b]
  exact (e.toLinearMap.linearIndependent_iff e.ker).symm

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  intro F E _ _ _ _ _ σ _ n J _ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Fv F v) σ n J
  refine ⟨hr, e.isClosedEmbedding.locallyCompactSpace, e.isEmbedding.t2Space,
    e.secondCountableTopology, inferInstanceAs (IsTopologicalGroup (HR (Fv F v) σ J)), h1, h3, h2,
    fun a => ⟨?_, ?_⟩⟩
  · letI : NontriviallyNormedField (Fv F v) :=
      Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
    exact isOpen_linearIndependent (K := Fv F v)
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))
  · have hm : Continuous fun g : HA (Fv F v) σ J => HA.mat (Fv F v) σ J g :=
      continuous_subtype_val
    have hv : Continuous fun g : HA (Fv F v) σ J =>
        ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := Units.continuous_val.comp hm
    refine continuous_pi fun b => ?_
    exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.LocalUnitaryTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedRowLatticeTermIsLattice
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem isLattice_map_equiv {E : Type} [Field E] [NumberField E] {V W : Type} [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (e : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E))) := by
  refine ⟨hΛ.fg.map _, ?_⟩
  have h1 : ((Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E)) : Submodule (𝓞 E) W) : Set W) =
      (e : V →ₗ[E] W) '' (Λ : Set V) := by
    simp [Submodule.map_coe]
  rw [h1, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

theorem term_lat_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  intro D X Y u u' Z T T' F0 F0' FP G c t ρ
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hL : Submodule.IsLattice D.host.E t.lam := hrow.1.1
  exact isLattice_map_equiv (ρ.trans c.e) t.lam hL

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_exists_pos_unique : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c := by
  first | exact @GlobalTheory.GaugeConst.gauge_exists_pos_unique | exact GlobalTheory.GaugeConst.gauge_exists_pos_unique | (intros; apply GlobalTheory.GaugeConst.gauge_exists_pos_unique <;> assumption)
end

