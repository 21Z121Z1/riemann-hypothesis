import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostHalfRootAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0926
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsoundQdPlacesUniformConst
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremBTB

theorem localTB : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h) ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := GlobalTheory.T.localCondition_of_local_theorem_hypW

theorem l_ge_three (D : D7) (i : D.nd.Loc) (hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) : 3 ≤ D.nd.l i := by
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
  rcases hl with h | h <;> rw [h]
  · have := D.host.qd_big.1; nlinarith
  · have := D.host.qd_big.2; nlinarith

theorem jointCond_at_qd (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool)
    (h0 : EmbeddingTypeJumps.Conclusion0 D) (hJump : EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂) (hPar : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc) (hQ : EmbeddingTypeJumps.AtQD i)
    (π : D.nd.X i) :
    JointConditionTameBound D HW F i (r i) π ⌊2 * large₂.sc.b⌋₊ ⌊2 * large₂.sc.b⌋₊
      (GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV)) := by
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  have hl3 := l_ge_three D i hl
  refine ⟨by omega, fun w hw => ?_⟩
  obtain ⟨-, hK1, -, hdegK⟩ := h0 i hl w hw
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun C hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, -⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hK0 : Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≠ 0 := Module.finrank_pos.ne'
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    show padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1)) -
      padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1) = 0
    have hpos : (D.nd.l i - 1) / 2 ≠ 0 := by omega
    have hv : padicValNat (D.nd.l i) ((D.nd.l i - 1) / 2) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => by
        have := Nat.le_of_dvd (by omega) h
        omega
    rw [hdegK, padicValNat.mul hpos hK0, hv, zero_add, Nat.sub_self]
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have hb := hPar
  unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hb
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hfl : ∀ z : ℤ, (z : ℝ) ≤ 2 * large₂.sc.b → z ≤ (⌊2 * large₂.sc.b⌋₊ : ℤ) := by
    intro z hz
    rcases le_or_gt z 0 with h | h
    · exact h.trans (Int.natCast_nonneg _)
    · have h2 : ((z.toNat : ℕ) : ℝ) ≤ 2 * large₂.sc.b := by
        rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg h.le]; exact hz
      have := Nat.le_floor h2
      omega
  have ht : D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ := by
    have := hfl (D.R.t : ℤ) (by push_cast; linarith)
    omega
  have key := GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings
    (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y ⌊2 * large₂.sc.b⌋₊ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨s, Jc, Jl, hs1', hs2', hJc, hJl, hlow, hcl, -, -, hiff⟩ := hJump i hQ w hw C τ
      classical
      refine ⟨Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t, ?_, ?_, fun a ha => ?_⟩
      · calc (Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t).card ≤ (Jc ∪ Jl).card + (Finset.Ico (0 : ℤ) D.R.t).card :=
              Finset.card_union_le _ _
          _ ≤ Jc.card + Jl.card + (Finset.Ico (0 : ℤ) D.R.t).card := by
              have := Finset.card_union_le Jc Jl; omega
          _ = D.R.nV := by
              rw [hJc, hJl, Int.card_Ico]
              unfold Ranks.nV Ranks.r
              have := D.R.m_add_three_le_k
              simp only [sub_zero, Int.toNat_natCast]
              omega
      · intro u hu
        simp only [Finset.mem_union, Finset.mem_Ico] at hu
        rcases hu with (hu | hu) | hu
        · rcases hcl with hc' | hc'
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
            · exact hfl (u + 1) (by push_cast; linarith)
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
        · obtain ⟨hb', -, -, -⟩ := hlow u hu
          rcases hb' with ⟨a1, a2⟩ | ⟨a1, a2⟩
          · constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · omega
          · constructor
            · omega
            · exact hfl (u + 1) (by push_cast; linarith)
        · constructor
          · omega
          · omega
      · have := (hiff π a).1 (hY τ a ha)
        simp only [Finset.mem_union, Finset.mem_Ico]
        tauto)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

theorem cBnum_le (l t n r : ℕ) (b : ℝ) (hl : 3 ≤ l) (ht : 1 ≤ t) (hn : 1 ≤ n) (hr : 1 ≤ r) (hb : 1 < b)
    (hL : 1 < Real.log b) :
    (GlobalTheory.HubLoc.cBnum l ⌊2 * b⌋₊ t (4 * n * (r + t)) : ℝ) ≤
      60 * (t : ℝ) * ((2 * n : ℕ) : ℝ) * ((r : ℝ) + (t : ℝ)) * Real.log b := by
  set L := Real.log b with hLdef
  set lam := Nat.log l (2 * ⌊2 * b⌋₊) with hlam
  have hfl2 : 2 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpow : l ^ lam ≤ 2 * ⌊2 * b⌋₊ := Nat.pow_log_le_self l (by omega)
  have h3pow : 3 ^ lam ≤ l ^ lam := Nat.pow_le_pow_left hl lam
  have hfb : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have h3R : (3 : ℝ) ^ lam ≤ 4 * b := by
    have : ((3 ^ lam : ℕ) : ℝ) ≤ ((2 * ⌊2 * b⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3pow.trans hpow
    push_cast at this
    linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlamL : (lam : ℝ) ≤ 4 * L := by
    have h1 : Real.log ((3 : ℝ) ^ lam) ≤ Real.log (4 * b) := Real.log_le_log (by positivity) h3R
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : (lam : ℝ) ≤ (lam : ℝ) * Real.log 3 := by
      have : (0 : ℝ) ≤ lam := by positivity
      nlinarith
    linarith
  unfold GlobalTheory.HubLoc.cBnum
  rw [← hlam]
  push_cast
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlam0 : (0 : ℝ) ≤ lam := by positivity
  set P : ℝ := (t : ℝ) * (2 * n) * (r + t) with hP
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
    nlinarith
  have hA : 3 + (lam : ℝ) + 3 ≤ 10 * P * L := by nlinarith
  have hB : 4 * (t : ℝ) + 3 * t ≤ 7 * P * L := by
    have : (t : ℝ) ≤ P := by
      have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
      nlinarith
    nlinarith
  have hC : (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) ≤ 24 * P * L := by
    have h4 : (4 : ℝ) + 2 * lam ≤ 12 * L := by linarith
    have hq : (0 : ℝ) ≤ (t : ℝ) * (4 * n * (r + t)) := by positivity
    calc (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) = ((t : ℝ) * (4 * n * (r + t))) * (4 + 2 * lam) := by ring
      _ ≤ ((t : ℝ) * (4 * n * (r + t))) * (12 * L) := mul_le_mul_of_nonneg_left h4 hq
      _ = 24 * P * L := by rw [hP]; ring
  have hPL : 0 ≤ P * L := by positivity
  nlinarith

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := by
  intro D HW F r ρ large₂ ep h0 _h1 hW hTB hJump _hFon _hG2 _hSet hLit hPar i hQ π _hπ
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  refine ⟨GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV), ?_, ?_⟩
  · exact localTB D HW F i (r i) π _ _ _ hTB (fun w hw C h => hW i hQ w hw C h) (hLit i hQ).2.2.2.1
      (jointCond_at_qd D HW F r large₂ ep h0 hJump hPar i hQ π)
  · have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
    have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have hn1 : 1 ≤ D.R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
    have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
    have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
    have hLb : 1 < Real.log large₂.sc.b := by
      unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
      exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
    have key := cBnum_le (D.nd.l i) D.R.t D.R.n D.R.r large₂.sc.b (l_ge_three D i hl) ht1 hn1 hr1 hb1 hLb
    have hnV : D.R.nV = D.R.r + D.R.t := rfl
    have hf : D.R.f = 2 * D.R.n := rfl
    rw [hnV, hf]
    exact key

end GlobalTheory.TheoremBTB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDictionaryFrameMemOpenFrames
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open scoped ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DictDom

theorem frame_mem_dom : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  intro D H Dw l Xo c σ V U dict io g e F ik φ th x₀ hσ hA hU hW hD hth hx₀ h
  obtain ⟨γ, -, -, -, hmat⟩ := hD.2 h
  have hX := hW (dict h).1
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ (U.X (dict h).1).p0 (U.X (dict h).1).Ψ
    (U.X (dict h).1).Gm (U.X (dict h).1).Gm_herm).2.1 _ fun τ => ?_).1
  rw [← hx₀ (dict h).1 τ.1 τ.2, hmat τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary V (hth (dict h).1 τ) (γ * h)
  have e1 : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram).transpose).map τ.1).transpose =
      -(V.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end GlobalTheory.DictDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetupStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_column_row_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → EmbeddingTypes.LiftExponentColumn i (X.r i) (X.dc i) (X.eS i) ∧ EmbeddingTypes.LiftExponentDualPlaces i (X.r i) (X.dc i) (X.eS i) := by
  first | exact @GlobalTheory.LiftExpSplit.main | exact GlobalTheory.LiftExpSplit.main | (intros; apply GlobalTheory.LiftExpSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisationStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.longOrbits_rowColength_inertLocalisation : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  first | exact @GlobalTheory.RowBLong.main | exact GlobalTheory.RowBLong.main | (intros; apply GlobalTheory.RowBLong.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLift
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescHf

theorem exists_retraction {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧
      (∀ a : ↥LL.1, p (IntermediateField.inclusion h a) = a) ∧ (∀ x : ↥LL'.1, x ∈ OL LL' → p x ∈ OL LL) := by
  obtain ⟨r, hr, hr1⟩ := GlobalTheory.T.exists_integral_retraction_localIntegers h
  obtain ⟨p, hp, hpr⟩ := GlobalTheory.T.exists_fieldExtension_of_integral_retraction h r hr hr1
  have h1 : p 1 = 1 := by
    have := hpr 1
    rw [hr1] at this
    exact this
  refine ⟨p, hp, fun a => ?_, fun x hx => ?_⟩
  · have := hp a 1
    rw [mul_one, h1, mul_one] at this
    exact this
  · have := hpr ⟨x, hx⟩
    rw [show p x = _ from this]
    exact (r ⟨x, hx⟩).2

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem descHf : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  intro D i w hw C k M z hz
  obtain ⟨p, hpm, hp1, hpO⟩ := exists_retraction C.le
  obtain ⟨c, hc, m, hcm⟩ := (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).1 hz
  have hent : ∀ g a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g) a b =
      IntermediateField.inclusion C.le (Br.loc D.nbr i w hw M g a b) := fun g a b => rfl
  have hp : ∀ g (v : Fin k → ↥C.LL.1),
      (fun j => p ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v j)) =
        (Br.loc D.nbr i w hw M g).mulVec fun j => p (v j) := by
    intro g v
    funext a
    simp only [Matrix.mulVec, dotProduct, map_sum, hent, hpm]
  have hc' := GlobalTheory.TwistedSelmerCompare.crystallineCocycle_transport_conjugation (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).Kw C.LL
    (D.nbr i w hw).LL (MonoidHom.id _) continuous_id 1 (fun g => by simp) _ (Br.loc D.nbr i w hw M) p hp c hc
  refine (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).2 ⟨_, hc', fun j => p (m j), fun g => ?_⟩
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (z g)
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (c g + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m - m)) := by
    refine (liftQ_mk C.le k u).symm.trans ?_
    refine Eq.trans ?_ (hcm g)
    exact congrArg (liftQ C.le k) hu
  obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (stdG ↥(OL C.LL) ↥C.LL.1 k)).1 h1
  refine hu.symm.trans ((Submodule.Quotient.eq (stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k)).2 ?_)
  refine ⟨fun j => ⟨p (n j), hpO _ (n j).2⟩, ?_⟩
  funext j
  have h2 := congrArg p (congrFun hn j)
  have h3 := congrFun (hp g m) j
  change p ((n j : ↥C.LL.1)) = p (IntermediateField.inclusion C.le (u j) - (c g j + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m j - m j))) at h2
  change (p (n j) : Br.LL D.nbr i w hw) = u j - (p (c g j) + ((Br.loc D.nbr i w hw M g).mulVec (fun j => p (m j)) j - p (m j)))
  rw [h2, map_sub, map_add, map_sub, hp1, ← h3]

end GlobalTheory.UseLoc.DescHf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntegralFormsOfRationalAndLocalSpans
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.SpanInt

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f g : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (f + g) = C.rd a f + C.rd a g := by
  simp only [Cover.rd, map_add, smul_add]

theorem rd_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (x : C.d.c₂.F) (f : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (x • f) = C.σ₂ x • C.rd a f := by
  simp only [Cover.rd, LinearMap.map_smulₛₗ, map_smul]
  exact smul_comm _ _ _

theorem rd_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : C.rd a 0 = 0 := by
  simp only [Cover.rd, map_zero, smul_zero]

theorem vAdd_nonneg {k : Type} [Field k] [NumberField k] (la : HeightOneSpectrum (𝓞 k)) {x : k} (hx0 : x ≠ 0)
    (hx : la.valuation k x ≤ 1) : 0 ≤ vAdd la x := by
  unfold vAdd
  have h2 : (la.valuation k) x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr hx
  rw [WithZero.log_one] at h3
  omega

theorem cuspSec_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {f g : Rul C.d.Xo₂ C.d.c₂}
    (hf : f ∈ C.cuspSec a n) (hg : g ∈ C.cuspSec a n) : f + g ∈ C.cuspSec a n :=
  ⟨add_mem hf.1 hg.1, by rw [map_add]; exact add_mem hf.2 hg.2⟩

theorem cuspSec_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {f : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ C.cuspSec a n) : x • f ∈ C.cuspSec a n :=
  ⟨Submodule.smul_mem _ x hf.1, by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩

theorem cuspSec_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (0 : Rul C.d.Xo₂ C.d.c₂) ∈ C.cuspSec a n :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem exists_of_mem_span_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ Submodule.span C.σ₂.range (C.ratForms a n)) :
    ∃ f ∈ C.cuspSec a n, C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, cuspSec_zero C a n, rd_zero C a⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg, rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨s, y, rfl⟩ := s
    exact ⟨y • f, cuspSec_smul C a n y hf, by rw [rd_smul]; rfl⟩

theorem exists_of_mem_span_intForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) {φ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms a n {la})) :
    ∃ f ∈ C.cuspSec a n, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f) ∧ C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, ⟨hf, hv⟩, rfl⟩ := hx
    exact ⟨f, hf, hv la rfl, rfl⟩
  | zero =>
    refine ⟨0, cuspSec_zero C a n, fun v hv => ?_, rd_zero C a⟩
    rw [(isVal_valSet la v hv).zero]
    exact le_top
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨g, hg, hvg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg,
      fun v hv => (le_min (hvf v hv) (hvg v hv)).trans ((isVal_valSet la v hv).add _ _), rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨s, y, hy, rfl⟩ := s
    refine ⟨y • f, cuspSec_smul C a n y hf, fun v hv => ?_, by rw [rd_smul]; rfl⟩
    by_cases h0 : y = 0
    · rw [h0, zero_smul, (isVal_valSet la v hv).zero]
      exact le_top
    · rw [(isVal_valSet la v hv).smul y f h0]
      exact add_nonneg (by exact_mod_cast vAdd_nonneg la h0 hy) (hvf v hv)

theorem eq_of_rd_eq (D : D7) (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : Formalism.L2.Pj.InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (C : Cover T j σ) (hC : C.IsUnif) (hcc : CUnit C.cc₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ha : Dom a n) {f g : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ sec C.d.Xo₂ C.d.c₂ a n) (hg : g ∈ sec C.d.Xo₂ C.d.c₂ a n)
    (h : C.rd a f = C.rd a g) : f = g := by
  by_contra hne
  have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f - g) :=
    LinearIndependent.of_subsingleton 0 (sub_ne_zero.2 hne)
  have h2 := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hT j hj σ hσ C hC hcc a n ha 1 (fun _ => f - g)
    (fun _ => sub_mem hf hg) hli
  have h3 : C.rd a (f - g) = 0 := by
    have e := rd_add C a (f - g) g
    rw [sub_add_cancel, h] at e
    calc C.rd a (f - g) = (C.rd a (f - g) + C.rd a g) - C.rd a g := by abel
      _ = 0 := by rw [← e, sub_self]
  exact h2.ne_zero 0 h3

theorem mem_intForms_of_spans : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom wa n → ∀ (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) (φ : GA D (T.V j σ) → ℂ), φ ∈ Submodule.span C.σ₂.range (C.ratForms wa n) → (∀ la ∈ S, φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms wa n {la})) → φ ∈ C.intForms wa n S := by
  intro D T hT j hj σ hσ C hC hcc wa n hn S φ hφ hS
  obtain ⟨f, hf, rfl⟩ := exists_of_mem_span_ratForms C wa n hφ
  refine ⟨f, ⟨hf, fun la hla => ?_⟩, rfl⟩
  obtain ⟨g, hg, hvg, hfg⟩ := exists_of_mem_span_intForms C wa n la (hS la hla)
  rw [eq_of_rd_eq D T hT j hj σ hσ C hC hcc wa n hn hf.1 hg.1 hfg.symm]
  exact hvg

end GlobalTheory.LevelSeries.SpanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBoundsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsCD_rowCondition_localBounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  first | exact @GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond | exact GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond | (intros; apply GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOneStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → F (x : ℂ) = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) ∧ (ω = ω' → F 1 = c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ) ∧ (ω ≠ ω' → F 1 = 0) := by
  first | exact @GlobalTheory.RSThetaCont.theta_integral_continuation | exact GlobalTheory.RSThetaCont.theta_integral_continuation | (intros; apply GlobalTheory.RSThetaCont.theta_integral_continuation <;> assumption)
end

