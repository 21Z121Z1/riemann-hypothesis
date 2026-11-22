import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun.LeafMMTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Spread

open GlobalTheory.SignedHC

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

theorem weightX_zero_bounds {x : ℚ} (hx : x ∈ (num D C τ).weightX 0) :
    ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ x ∧ x ≤ (num D C τ).a 0 := by
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg : (0 : ℚ) ≤ (num D C τ).ga := by positivity
  have hvk := v_le_two D C τ hk le_rfl
  have ham : (num D C τ).a (num D C τ).m = (num D C τ).v 2 + (num D C τ).ga + 1 / 2 := (num D C τ).a_m
  have hlow : ∀ i, i ≤ D.R.m → ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ (num D C τ).a i := fun i hi => by
    have := a_le D C τ hi
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  have h0 : ((num D C τ).v 2 : ℚ) + 1 / 2 ≤ (num D C τ).a 0 := by
    have h1 := a_le D C τ (Nat.zero_le D.R.m)
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, -⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    exact ⟨hlow i hi, a_le D C τ (Nat.zero_le i)⟩
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have hi := v_le_two D C τ h1 h2
    have hik : ((num D C τ).v D.R.k : ℚ) ≤ (num D C τ).v i := by
      rcases h2.eq_or_lt with e | e
      · rw [e]; exact le_rfl
      · exact_mod_cast ((num D C τ).v_anti i D.R.k h1 e le_rfl).le
    simp only [GridData.vHalf]
    constructor <;> linarith
  · have hb := blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 h
    have hp := (num D C τ).a_pred h1
    have hq := a_le D C τ (Nat.zero_le (i - 1))
    exact ⟨(hlow i h2).trans hb.1.le, by linarith [hb.2]⟩
  · omega

theorem La_sub_le (i j : Fin (rankP D D.R.m)) :
    (((La D C τ).w i - (La D C τ).w j : ℤ) : ℚ) ≤
      (((num D C τ).v 2 - (num D C τ).v D.R.k : ℤ) : ℚ) + 1 + ((D.R.m : ℚ) + 1) * (gap D C : ℚ) + (rankP D D.R.m : ℚ) := by
  push_cast
  rw [La_cast, La_cast]
  simp only [highestWeight]
  have hi := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) i)
  have hj := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) j)
  have ea : (num D C τ).a 0 = (num D C τ).v 2 + 1 / 2 + ((D.R.m : ℚ) + 1 - ((0 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have hi' : ((i : ℕ) : ℚ) ≤ (rankP D D.R.m : ℚ) := by exact_mod_cast i.2.le
  have hj' : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := by positivity
  rw [ea] at hi hj
  push_cast at hi hj
  linarith [hi.1, hi.2, hj.1, hj.2]

end Spread

section Leaf

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem np_eq {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : ((rankP D D.R.m : ℕ) : ℝ) = d.O.np := by
  have hm := D.R.two_le_m
  have e1 : D.R.r + 6 - 1 = D.R.k + D.R.m + 4 := by unfold Ranks.r; omega
  have e2 : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; omega
  have e : rankP D D.R.m = (D.R.k + D.R.m) + D.R.m * (D.R.k + D.R.m + 4) := by
    unfold rankP nRk sLen
    rw [e1, e2]
  rw [e]
  show _ = ((D.R.k : ℝ) + D.R.m - 1 + 1) + D.R.m * (((D.R.k : ℝ) + D.R.m - 1) + 5)
  push_cast
  ring

theorem leafMM_of_test {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieTest d a) {C : ℝ}
    (hC : 1 ≤ C) : Formalism.L2.Indef.Tree.LeafMM d.O C := by
  obtain ⟨v₀, hv⟩ := (GlobalTheory.ptField_main D).2.1
  have hga : (gap D 1 : ℝ) ≤ d.O.ga C := by
    rw [← GlobalTheory.BigTop.Fun.Model.ga_eq d 1]
    exact_mod_cast GlobalTheory.SizeLeafCheck.ga_mono _ hC
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) + 1 := by positivity
  have hRp : d.O.Rp C = ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) + d.O.Lc + d.O.np := rfl
  have hnp : (0 : ℝ) ≤ d.O.np := by rw [← np_eq d]; positivity
  have hR1 : 1 ≤ d.O.Rp C := by
    rw [hRp]
    have : (1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) + 1 := by linarith [(Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ D.R.m)]
      have h2 : (1 : ℝ) ≤ (d.O.ga C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (d.O.ga C) : (0 : ℝ) ≤ d.O.ga C)]
      nlinarith
    have : (0 : ℝ) ≤ d.O.Lc := Nat.cast_nonneg _
    linarith
  have hSp : GlobalTheory.TestLat.SpreadLe (LaP d.G) (d.O.Rp C) := by
    intro τ i j
    show (((La D 1 τ).w (Fin.cast (rank_Xp d.G) i) - (La D 1 τ).w (Fin.cast (rank_Xp d.G) j) : ℤ) : ℝ) ≤ _
    have hq := La_sub_le D 1 τ (Fin.cast (rank_Xp d.G) i) (Fin.cast (rank_Xp d.G) j)
    have hr := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hr
    have hL : ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat ≤ cloudLen D :=
      Finset.le_sup (f := fun τ => ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 -
        (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat) (Finset.mem_univ τ)
    have hL' : (((num D 1 τ).v 2 : ℝ) - (num D 1 τ).v D.R.k) ≤ d.O.Lc := by
      rw [GlobalTheory.BigTop.Fun.Model.Lc_eq d]
      have h1 := Int.self_le_toNat ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k)
      have h2 : (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k : ℤ) : ℝ) ≤ (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℤ) := by
        exact_mod_cast h1
      have h3 : ((((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℕ) : ℝ) ≤ (cloudLen D : ℝ) := by exact_mod_cast hL
      push_cast at h2
      linarith
    have hmul := mul_le_mul_of_nonneg_left (by linarith : (gap D 1 : ℝ) + 1 ≤ (d.O.ga C : ℝ) + 1) hm0
    have hexp : ((D.R.m : ℝ) + 1) * ((gap D 1 : ℝ) + 1) = ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) + ((D.R.m : ℝ) + 1) := by ring
    have hm1 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    rw [hRp, ← np_eq d]
    push_cast
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := IsTestLat.gridTestLattice_largestSlope_bound GlobalTheory.TestLat.slope_holds.2 hv hR1 hSp h
  refine ⟨h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  unfold GlobalTheory.TestLat.bound Formalism.L2.Indef.Tree.FunData.EMM
  rw [rank_Xp, np_eq d, D.what₂.card_Tau]
  rfl

end Leaf

theorem mm_tie : GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.BigTop.Fun.MM @GlobalTheory.BigTop.Fun.Comparison₂ := fun h =>
  ⟨0, fun _ _ => h.imp fun _ _ _ _ _ => ⟨1, fun _ hC => EvPt.of_forall fun _ _ _ _ _ d hd =>
    let ⟨_, a, ha⟩ := hd
    leafMM_of_test d a ha.test hC⟩⟩

end GlobalTheory.BigTop.Fun.LeafMMTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

noncomputable section

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem xiH_base : p.R.toRealDat.toLevCh.xiH p.P.A3.A.μ0 = 1 := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  rw [← h0, p.tupXi _ (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one]

theorem xiH_twisted (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0) :
    TwistedAt D (D.plEq.symm w) ∧ p.R.toRealDat.toLevCh.xiH (p.R.mu w) =
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  have e1 : p.R.mu w = p.tupT (D.what₂.muAt (D.plEq.symm w)) := by rw [p.tupAt]; simp
  have htw : D.what₂.muAt (D.plEq.symm w) ≠ D.what₂.mu0 := fun e => hw (by rw [e1, e, h0])
  have hmt : D.what₂.muAt (D.plEq.symm w) = D.what₂.muTw (D.plEq.symm w) := (D.what₂.muAt_or _).resolve_left htw
  refine ⟨htw, ?_⟩
  rw [e1, p.tupXi _ (Or.inr ⟨_, rfl⟩), hmt, p.Tp.xi_tw]

end

theorem resChar_eq {D : D7} (w : D.what₂.places.Pl) {l : ℕ} (hl : l.Prime)
    (h : ((l : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = l := by
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    intro hin
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hl).2 hq)
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
        (b : 𝓞 D.what₂.LL) * ((l : ℕ) : 𝓞 D.what₂.LL) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hin) (Ideal.mul_mem_left _ _ h)
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
  have h2 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h2
  have h3 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h2
  have h4 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 0 := by
    unfold vAdd
    rw [show ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) by simp, h1]
    simp
  have := D.what₂.places.ramIdx_pos w
  omega

theorem nuH_twisted {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0)
    (i j : Fin D.R.m) : nuH G (p.R.mu w) i j = nuH G p.P.A3.A.μ0 i j *
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  unfold nuH
  rw [(xiH_twisted p w hw).2, xiH_base p, mul_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end GlobalTheory.ThmAUpper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.NumSizes

theorem r_log_div_le (r t q : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hq : 4 * t * r + 1 < q) :
    (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  set Q : ℝ := 4 * t * r + 2 with hQ
  have hqQ : Q ≤ q := by rw [hQ]; exact_mod_cast (by omega : 4 * t * r + 2 ≤ q)
  have hQ6 : (6:ℝ) ≤ Q := by rw [hQ]; nlinarith
  have he : Real.exp 1 ≤ Q := by have := Real.exp_one_lt_d9; linarith
  have hant : Real.log q / q ≤ Real.log Q / Q :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hqQ)) hqQ
  have hq0 : (0:ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have s1 : (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ (r : ℝ) * Real.log q / ((q : ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have s2 : (r : ℝ) * Real.log q / ((q : ℝ) / 2) = 2 * r * (Real.log q / q) := by
    field_simp
  have s3 : 2 * (r : ℝ) * (Real.log Q / Q) ≤ 2 * Real.log Q := by
    have hrQ : (r : ℝ) ≤ Q := by rw [hQ]; nlinarith
    have hQ0 : (0:ℝ) < Q := by linarith
    rw [mul_div_assoc', div_le_iff₀ hQ0]
    nlinarith
  have s4 : Real.log Q ≤ Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
    have h6 : Q ≤ 6 * ((r : ℝ) + t) ^ 2 := by rw [hQ]; nlinarith
    calc Real.log Q ≤ Real.log (6 * ((r : ℝ) + t) ^ 2) := Real.log_le_log (by linarith) h6
      _ = Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  calc (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * r * (Real.log q / q) := s1.trans s2.le
    _ ≤ 2 * r * (Real.log Q / Q) := mul_le_mul_of_nonneg_left hant (by positivity)
    _ ≤ 2 * Real.log Q := s3
    _ ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by linarith

theorem sq_le_dim (f r m : ℕ) (hf : 2 ≤ f) (hr : 2 ≤ r) (hm : 2 ≤ m) : r ^ 2 ≤ m * (f * r.choose 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h : (s + 2).choose 2 * 2 = (s + 2) * (s + 1) := by
    have := Nat.add_one_mul_choose_eq (s + 1) 1
    rw [Nat.choose_one_right] at this
    exact this.symm
  have h4 : 2 * (2 * (s + 2).choose 2) ≤ m * (f * (s + 2).choose 2) :=
    Nat.mul_le_mul hm (Nat.mul_le_mul hf le_rfl)
  nlinarith

variable {D : D7} {L : SizeData₂ D}

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem ranks_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    1 ≤ T.PP ∧ (D.R.f : ℝ) * D.R.r ≤ L.sc.b ∧ (D.R.r : ℝ) + D.R.t ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hL := one_le_L L.sc
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : (D.R.f : ℝ) * D.R.r ≤ zBase L := le_mul_of_one_le_right (by positivity) hL
  have hZ1 : 1 ≤ zBase L := hfr.trans hZ
  have hZP : zBase L ≤ T.PP := by
    rw [T.PP_eq]
    have a : zBase L ≤ zBase L ^ T.eP := Real.self_le_rpow_of_one_le hZ1 (by linarith [T.eP_ge])
    exact a.trans (le_mul_of_one_le_left (by linarith) T.one_le_CP)
  have hPP : 1 ≤ T.PP := hZ1.trans hZP
  have hTO : (1 : ℝ) ≤ T.TO := by exact_mod_cast (by have := T.TO_40; omega : 1 ≤ T.TO)
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hs : (T.TO : ℝ) * T.PP ≤ L.sc.b := T.TO_PP'.trans (Real.rpow_le_self_of_one_le hb (by norm_num))
  have hP2 : T.PP ≤ (T.TO : ℝ) * T.PP := le_mul_of_one_le_left (by linarith) hTO
  refine ⟨hPP, by linarith, ?_⟩
  have e1 : (D.R.r : ℝ) + D.R.t = T.nP + T.TO * T.nWn := by exact_mod_cast T.split
  have e2 : (T.nP : ℝ) ≤ T.nWn := by exact_mod_cast T.nW_lo.2.2
  have e3 : (T.TO : ℝ) * T.nWn ≤ T.TO * T.PP := mul_le_mul_of_nonneg_left T.nW_le (by linarith)
  linarith [T.nW_le]

variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem unitE_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem dim_eq : GlobalTheory.CompHt.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  exact GlobalTheory.SlopeRec.dimFlag_eq p.fw.laws.pins ⟨Nat.le_add_left 1 i, i.2⟩

theorem lenT_mul_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3 ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hsq := sq_le_dim D.R.f D.R.r D.R.m (by unfold Ranks.f; omega) hr2 h1
  rw [← T.Dp_eq] at hsq
  have hD1 : 1 ≤ T.Dp := by
    rcases Nat.eq_zero_or_pos T.Dp with h | h
    · rw [h] at hsq; nlinarith
    · exact h
  have hsq' : (D.R.r : ℝ) ^ 2 ≤ D.R.m * T.Dp := by exact_mod_cast hsq
  have hD : (1 : ℝ) ≤ T.Dp := by exact_mod_cast hD1
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hPP := (ranks_le T).1
  have hW : (1 : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) (one_le_pow₀ hD)) hk
  have hlen : (lenT p i T.PP : ℝ) ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) := by
    unfold lenT
    rw [dim_eq, ← T.Dp_eq]
    have a := (Nat.ceil_lt_add_one (a := T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m) (by positivity)).le
    have b : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k := div_le_self (by linarith) hm
    linarith
  have hr3 : (D.R.r : ℝ) ^ 3 ≤ D.R.r * (D.R.m * T.Dp) := by
    rw [pow_succ']; exact mul_le_mul_of_nonneg_left hsq' (by positivity)
  have hb : (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 ≤ L.sc.b := by
    refine le_trans ?_ T.b_ge
    have : T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 =
      T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) T.CbN_ge
  calc (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3
      ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) * (D.R.r * (D.R.m * T.Dp)) :=
        mul_le_mul hlen hr3 (by positivity) (by linarith)
    _ = 2 * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    _ ≤ 2 * L.sc.b := by linarith

theorem numAt {P : ParameterChoice' D L} (T : ParamsT D L P) (hll : 1 ≤ Real.log (Real.log L.sc.x)) :
    NumAt p i T.PP (|L.Ct| + 20) := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hL := one_le_L L.sc
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hC := abs_nonneg L.Ct
  obtain ⟨-, hfr, hrt⟩ := ranks_le T
  have hCL : 20 * L.sc.L ≤ (|L.Ct| + 20) * L.sc.L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlr : Real.log D.R.r ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_left (by linarith) hf).trans hfr)
  have hlf : Real.log D.R.f ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_right (by linarith) hr).trans hfr)
  refine ⟨hL, hb, by linarith, hll, ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [unitE_eq]
    refine le_mul_of_one_le_left ?_ (by linarith)
    have : 0 ≤ L.sc.L := by linarith
    have : 0 ≤ Real.log (Real.log L.sc.x) := by linarith
    positivity
  · have hx := L.sc.one_lt_alt
    have hlx : 0 < Real.log L.sc.x := Real.log_pos hx
    have hk : (2 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 2 ≤ D.R.k)
    have hkt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
    have a : Real.log D.R.k ≤ L.Ct * Real.log L.sc.x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (hkt.trans L.t_win.2)
    have b : Real.log D.R.k ≤ (|L.Ct| + 1) * Real.log L.sc.x :=
      a.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L.Ct]) hlx.le)
    have c := Real.log_le_log (Real.log_pos (by linarith)) b
    rw [Real.log_mul (by linarith) hlx.ne'] at c
    have d := Real.log_le_sub_one_of_pos (by linarith : 0 < |L.Ct| + 1)
    nlinarith
  · have hQ : (D.host.QS : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by
      have := D.host.QS_le
      exact_mod_cast this.trans (Nat.pow_le_pow_left (by unfold Ranks.f; omega) 2)
    have hQ0 : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
    have a := Real.log_le_log hQ0 hQ
    rw [Real.log_pow] at a
    push_cast at a
    have h2' := Real.log_two_gt_d9
    unfold Formalism.MainNotions.DIV.Cons.vd2
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  · exact (lenT_mul_le p i T).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · intro q hq
    have hq' : 4 * D.R.t * D.R.r + 1 < q := by
      rcases Finset.mem_insert.1 hq with h | h
      · exact h ▸ D.host.qd_big.1
      · exact (Finset.mem_singleton.1 h) ▸ D.host.qd_big.2
    have a := r_log_div_le D.R.r D.R.t q hr1 (by omega) hq'
    have b : Real.log ((D.R.r : ℝ) + D.R.t) ≤ Real.log 2 + L.sc.L := by
      rw [← hlb, ← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) hrt
    have c := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    have d := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have e : (|L.Ct| + 20) * L.sc.L ≤ (|L.Ct| + 20) * D.R.m * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hm) (by linarith)
    linarith

theorem numPt : NumPt := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨|Fm.Ct| + 20, by positivity,
    Real.exp (Real.exp 1), fun x hx hle ι p _ i _ => ?_⟩⟩⟩
  rw [← Fm.Ct_eq x ι]
  refine numAt p i (Fm.parT x hx ι) ?_
  rw [Fm.L_x x ι hx, Real.le_log_iff_exp_le, Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hle)]
  · exact hle
  · exact Real.log_pos ((Real.one_lt_exp_iff.2 (Real.exp_pos 1)).trans_le hle)

theorem numPt_of_size : Size → NumPt := fun _ => numPt

end GlobalTheory.RefSum.NumSizes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHypothesisAllPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

theorem parOf_hyp : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j => ?_⟩⟩⟩
  have P := Fm.params x hx i
  have hrk := (Fm.D x i).sp.V_rank ((j : ℕ) + 1) (Nat.le_add_left _ _) j.2
  have h2 := (Fm.D x i).R.two_le_m
  have h3 := (Fm.D x i).R.m_add_three_le_k
  have h5 := (Fm.D x i).R.rank_add_five_le
  have h6 := (Fm.D x i).R.three_m_lt_t
  have hlst : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar (parOf (Fm.L x i) j) = Formalism.BasicNotions.LevelStarExponents.lStar (Fm.L x i) := by
    simp only [Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar, Formalism.BasicNotions.LevelStarExponents.lStar, Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.N, Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.b, parOf,
      Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Scale.b]
    push_cast
    ring
  have hb : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.b (parOf (Fm.L x i) j) = (Fm.L x i).sc.b := rfl
  refine
    { x_ge := (Fm.L x i).sc.one_lt_alt.le
      b'_pos := (Fm.L x i).sc.b'_pos
      m_pos := by show 1 ≤ (Fm.D x i).R.m; omega
      n_pos := (Fm.D x i).R.ord_pos
      f_pos := by show 1 ≤ 2 * (Fm.D x i).R.ord; have := (Fm.D x i).R.ord_pos; omega
      t_ge := by show (Fm.D x i).R.k + (Fm.D x i).R.m + 4 ≤ (Fm.D x i).R.t; omega
      t_gt := h6
      m_le := by show (Fm.D x i).R.m ≤ (Fm.D x i).R.k; omega
      η_le := by rw [hb]; exact P.eta_le
      Nr_eq := by
        show (Vc (Fm.D x i) j).rank + 1 = (Fm.D x i).R.k + (Fm.D x i).R.m + (Fm.D x i).R.t
        rw [hrk]
        show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t + 1 = (Fm.D x i).R.k + (Fm.D x i).R.m + (Fm.D x i).R.t
        omega
      t_le := P.t_le_eta
      S_nonneg := (Fm.L x i).Sc_pos.le
      sum_lt := by rw [hlst, hb]; exact P.lstar1
      win_lt := by rw [hlst, hb]; exact P.lstar2 }

end GlobalTheory.ExpTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConstStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslation_lift_eq_levelMove_unit_const : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∃ z : (T.U ((i : ℕ) + 1) σ).Comp → G → ℂ, (∀ x g, ‖z x g‖ = 1) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ h, rdU (T.U ((i : ℕ) + 1) σ) (actLev T.Q.c (O i).lev2 g f) (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 = z (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g * rdU (T.U ((i : ℕ) + 1) σ) f (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).2 := by
  first | exact @GlobalTheory.DictMove.rdU_actLev_eq | exact GlobalTheory.DictMove.rdU_actLev_eq | (intros; apply GlobalTheory.DictMove.rdU_actLev_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatementStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_expansion_statement : SumExpSt := by
  first | exact @GlobalTheory.ExpTie.sumExpSt | exact GlobalTheory.ExpTie.sumExpSt | (intros; apply GlobalTheory.ExpTie.sumExpSt <;> assumption)
end

