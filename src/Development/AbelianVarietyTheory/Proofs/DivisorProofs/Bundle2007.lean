import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberReferenceTuple
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

open GlobalTheory.BotPairSmall in

theorem smallPair_exists : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (D.host.conj • condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L μ₀ i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L μ₀ i j) (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • condE G.pl) (botBig D i j) ∧ IsBlockLevel P' (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χα hα χν hν hn
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have hd : Even (botBig D i j + botSmall D i j) :=
    ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, hv, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht (botSmall D i j) (botBig D i j + botSmall D i j)
    (hd.mul_left _)
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 hv.1 h0 χα χν
  have hm := condE_ne_bot G.pl
  have hcop := GlobalTheory.FunObj.SqNum.condE_sup_conj G.pl
  have hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) →
      W.chV'.f u = 1 := by
    intro u hu h
    rw [hW2, hν, GlobalTheory.BotPairSmall.CondNu.nuH_inv_eq_one_of_cong hL G i j u hu h]
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.CongReps.exists_reps D (botSmall D i j) _ (conj_smul_ne_bot D hm)
  have hTT := GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hK := GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hS := GlobalTheory.StdSumFix.stdSum_fix_eig D δ _ _ e0 W _ _ hTT hK R hR1 hR2
  have hN := GlobalTheory.ModulusNorm.absNorm_condE G.pl
  have hidx := GlobalTheory.BotPairSmall.blockJ_relIndex D (condE G.pl) hm (botBig D i j) (botBig D i j + botSmall D i j)
  have hQ : 1 ≤ levQ G.pl := by
    rw [← hN]; exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 hm)
  have heig : ∀ h ∈ blockJ D (condE G.pl) (botBig D i j) (botBig D i j + botSmall D i j), ∃ c : ℂ, ‖c‖ = 1 ∧
      W.Om 1 h (∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j) (botSmall D i j)
        (botBig D i j + botSmall D i j) e0)) = c • ∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j)
          (botSmall D i j) (botBig D i j + botSmall D i j) e0) := by
    intro h hh
    obtain ⟨k, hk, c, hc1, e⟩ := GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl h hh
    exact ⟨c, hc1, hS.2 h k c hk e⟩
  refine ⟨{
      crv := hc, pt0 := ht, a := botSmall D i j, d := botBig D i j + botSmall D i j, a_le := Nat.le_add_left _ _,
      d_even := hd, e0 := e0, vac := hv, W := W,
      n := fun τ => ((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat, wt := ?_,
      F := ∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j) (botSmall D i j)
      (botBig D i j + botSmall D i j) e0),
      pres := GlobalTheory.T.conjugateModulus_standardTheta_presentation D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hb hcond (botBig D i j) rfl _ hN R hR1 hR2,
      fix := hS.1,
      J := blockJ D (condE G.pl) (botBig D i j) (botBig D i j + botSmall D i j),
      J_le := blockJ_le _ _ _ _,
      idx_ne := hidx.1,
      idx_le := hidx.2.trans (by rw [hN]; exact Nat.pow_le_pow_right hQ (by omega)),
      eig := heig }, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩,
    fun h => GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet _ _ _ _ h⟩
  · intro τ
    show 2 * (((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat : ℤ) = W.ep' * W.chV'.n τ - _
    rw [hW4, hW2]
    obtain ⟨r, hr⟩ := χν.par τ
    have := hn τ
    omega
  · show W.chV.f x ^ W.ep = _
    rw [hW3, zpow_one, hW1, hα]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW4, zpow_one, hW2, hν]

end GlobalTheory.BotPairSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTuple
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem nuH_inv_eq_one {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) (u : (AE D)ˣ)
    (hu : IntU D u) (h : (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t)) :
    (nuH G t i j)⁻¹.1 (finIdl D u) = 1 := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one, div_eq_mul_inv]; exact mul_right_comm _ _ _
  have h0 := GlobalTheory.BotPairSmall.CondNu.nuH_inv_eq_one_of_cong hL G i j u hu (hatId_mono (modT_mul_conj_le G t) h)
  have h1 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu h
  rw [e, mul_inv]
  change ((nuH G μ₀ i j)⁻¹.1 * (L.xiH t)⁻¹.1) (finIdl D u) = 1
  rw [MonoidHom.mul_apply, h0, one_mul]
  change ((L.xiH t).1 (finIdl D u))⁻¹ = 1
  rw [h1, inv_one]

theorem conj_isCoprime_halfDifferent {I : Ideal (𝓞 D.host.E)}
    (h : IsCoprime I (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)})) : IsCoprime (D.host.conj • I) D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  have h2 : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ M := GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb)
  obtain ⟨a, ha, b, hb', e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
  have e1 := congrArg (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) e
  rw [map_add, map_mul, map_natCast, map_one] at e1
  refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e1]
  exact M.add_mem (hle (Ideal.mem_sup_left (Ideal.smul_mem_pointwise_smul D.host.conj _ _ ha))) (M.mul_mem_left _ h2)

theorem modT_isCoprime_two_q {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q)) (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (G : GridData L sc) (t : T) : IsCoprime (modT G t) (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)}) := by
  classical
  unfold modT
  refine IsCoprime.mul_left ?_ (IsCoprime.prod_left fun w hw => ?_)
  · obtain ⟨N, hN, hm⟩ := GlobalTheory.FunObj.StdDatum.HalfDiff.exists_nat_mem_condE G.pl ⟨hpq, hpq'⟩
    obtain ⟨x, y, e⟩ : IsCoprime ((N : ℕ) : 𝓞 D.host.E) ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hN
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, ← e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hm))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
    have hP : w ∈ L.Q t := hw.1.resolve_left hw.2
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := w.isMaximal.eq_of_le hne le_sup_left
    have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal :=
      heq.symm.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    refine (hL.Q_off t w hP).1 ?_
    rw [show D.host.QS * D.host.q * D.host.d * D.sp.T = (D.host.QS * D.host.q) * (D.host.d * D.sp.T) by ring, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h2q

theorem conj_modT_isCoprime_halfDifferent {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q)) (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (G : GridData L sc) (t : T) : IsCoprime (D.host.conj • modT G t) D.host.𝔟 :=
  conj_isCoprime_halfDifferent (modT_isCoprime_two_q hL hpq hpq' G t)

theorem smallPair_exists_tw : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.NormSum.Inp D → L.Is μ₀ → Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → ∀ (G : GridData L sc) (t : T) {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L t i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl * Qn G t), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L t i j) (nuH G t i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • modT G t) (botBig D i j) ∧ IsBlockLevel P' (modT G t) (botBig D i j) := by
  intro D T L sc μ₀ _ hL hpq hpq' G t δ t0 hc ht i j χα hα χν hν hn
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have hd : Even (botBig D i j + botSmall D i j) :=
    ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, hv, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht (botSmall D i j) (botBig D i j + botSmall D i j)
    (hd.mul_left _)
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 hv.1 h0 χα χν
  have hm := modT_ne_bot G t
  have hcop := GlobalTheory.SqTop.modT_sup_conj hL G t
  have hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) →
      W.chV'.f u = 1 := by
    intro u hu h
    rw [hW2, hν, nuH_inv_eq_one hL G t i j u hu h]
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.CongReps.exists_reps D (botSmall D i j) _ (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  have hTT := GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hK := GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hS := GlobalTheory.StdSumFix.stdSum_fix_eig D δ _ _ e0 W _ _ hTT hK R hR1 hR2
  have hN := absNorm_modT G t
  have hidx := GlobalTheory.BotPairSmall.blockJ_relIndex D (modT G t) hm (botBig D i j) (botBig D i j + botSmall D i j)
  have hQ : 1 ≤ levQ G.pl * Qn G t := by
    rw [← hN]; exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 hm)
  have heig : ∀ h ∈ GlobalTheory.BotPairSmall.blockJ D (modT G t) (botBig D i j) (botBig D i j + botSmall D i j), ∃ c : ℂ, ‖c‖ = 1 ∧
      W.Om 1 h (∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t) (botBig D i j) (botSmall D i j)
        (botBig D i j + botSmall D i j) e0)) = c • ∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t)
          (botBig D i j) (botSmall D i j) (botBig D i j + botSmall D i j) e0) := by
    intro h hh
    obtain ⟨k, hk, c, hc1, e⟩ := GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl h hh
    exact ⟨c, hc1, hS.2 h k c hk e⟩
  refine ⟨{
      crv := hc, pt0 := ht, a := botSmall D i j, d := botBig D i j + botSmall D i j, a_le := Nat.le_add_left _ _,
      d_even := hd, e0 := e0, vac := hv, W := W,
      n := fun τ => ((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat, wt := ?_,
      F := ∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t) (botBig D i j) (botSmall D i j)
      (botBig D i j + botSmall D i j) e0),
      pres := GlobalTheory.T.conjugateModulus_standardTheta_presentation D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop (conj_modT_isCoprime_halfDifferent hL hpq hpq' G t) hcond (botBig D i j) rfl _ hN R hR1 hR2,
      fix := hS.1,
      J := GlobalTheory.BotPairSmall.blockJ D (modT G t) (botBig D i j) (botBig D i j + botSmall D i j),
      J_le := GlobalTheory.BotPairSmall.blockJ_le _ _ _ _,
      idx_ne := hidx.1,
      idx_le := hidx.2.trans (by rw [hN]; exact Nat.pow_le_pow_right hQ (by omega)),
      eig := heig }, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩,
    fun h => GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet _ _ _ _ h⟩
  · intro τ
    show 2 * (((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat : ℤ) = W.ep' * W.chV'.n τ - _
    rw [hW4, hW2]
    obtain ⟨r, hr⟩ := χν.par τ
    have := hn τ
    omega
  · show W.chV.f x ^ W.ep = _
    rw [hW3, zpow_one, hW1, hα]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW4, zpow_one, hW2, hν]

end GlobalTheory.BotPairSmallTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.SWLit.WittStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := ((IsAlgClosed.lift : E →ₐ[ℚ] ℂ) : E →+* ℂ)
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_isWittBasis (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {n : ℕ} (l : E) (J : Matrix (Fin n) (Fin n) E)
    (hl : l ≠ 0) (hJ : J.det ≠ 0) : ∃ T : GL (Fin (n + n)) E, IsWittBasis σ J l T := by
  set Z : Matrix (Fin n) (Fin n) E := ((l / 2) • J⁻¹).map σ with hZ
  have hZσ : Z.map σ = (l / 2) • J⁻¹ := by
    ext i j
    simp [hZ, sigma_sigma h]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hrel : (2 : E) • (J * Z.map σ) = l • (1 : Matrix (Fin n) (Fin n) E) := by
    rw [hZσ, Matrix.mul_smul, Matrix.mul_nonsing_inv J hJu, smul_smul]
    congr 1
    field_simp
  have hZdet : Z.det ≠ 0 := by
    intro h0
    have := (σ : E →+* E).map_det ((l / 2) • J⁻¹)
    rw [show (σ : E →+* E).mapMatrix ((l / 2) • J⁻¹) = Z from rfl, h0, map_eq_zero] at this
    simp [Matrix.det_smul, Matrix.det_nonsing_inv, hl, hJ] at this
  have hM : (blk 1 Z 1 (-Z)).det ≠ 0 := by
    rw [blk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_one₁₁, Matrix.one_mul,
      show -Z - Z = (-2 : E) • Z by rw [neg_smul, two_smul]; abel, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hZdet
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, Z, hrel, rfl⟩

theorem incM_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

variable (σ : E →ₐ[F] E) {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E)

theorem incM_inv_mul : incM F (T⁻¹).1 * incM F T.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]

theorem incM_mul_inv : incM F T.1 * incM F (T⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]

theorem inBasis_mul (g h : UA σ J₂) : inBasis σ T (g * h) = inBasis σ T g * inBasis σ T h := by
  simp only [inBasis]
  rw [show mat (g * h) = mat g * mat h from rfl]
  calc incM F (T⁻¹).1 * (mat g * mat h) * incM F T.1
      = incM F (T⁻¹).1 * mat g * (incM F T.1 * incM F (T⁻¹).1) * mat h * incM F T.1 := by
        rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inBasis_one : inBasis σ T (1 : UA σ J₂) = 1 := by
  simp only [inBasis]
  rw [show mat (1 : UA σ J₂) = 1 from rfl, Matrix.mul_one, incM_inv_mul]

theorem entry_mul_mem (v : HeightOneSpectrum (𝓞 F)) {A B : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)}
    (hA : ∀ i j, compFin F E v (A i j) ∈ intLoc F E v) (hB : ∀ i j, compFin F E v (B i j) ∈ intLoc F E v) (i j) :
    compFin F E v ((A * B) i j) ∈ intLoc F E v := by
  rw [Matrix.mul_apply, map_sum]
  exact Subring.sum_mem _ fun k _ => by rw [map_mul]; exact Subring.mul_mem _ (hA i k) (hB k j)

def stdK : Subgroup (UA σ J₂) where
  carrier := {g | (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧
      compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ}
  one_mem' := by
    refine ⟨fun v i j => ?_, fun w τ => ?_⟩
    · rw [inv_one, inBasis_one, Matrix.one_apply]
      split_ifs <;> simp [one_mem, zero_mem]
    · rw [inBasis_one, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
  mul_mem' := by
    intro g h hg hh
    refine ⟨fun v i j => ⟨?_, ?_⟩, fun w τ => ?_⟩
    · rw [inBasis_mul]
      exact entry_mul_mem v (fun i j => (hg.1 v i j).1) (fun i j => (hh.1 v i j).1) i j
    · rw [mul_inv_rev, inBasis_mul]
      exact entry_mul_mem v (fun i j => (hh.1 v i j).2) (fun i j => (hg.1 v i j).2) i j
    · rw [inBasis_mul, Matrix.map_mul]
      exact mul_mem (hg.2 w τ) (hh.2 w τ)
  inv_mem' := by
    intro g hg
    refine ⟨fun v i j => ⟨(hg.1 v i j).2, by rw [inv_inv]; exact (hg.1 v i j).1⟩, fun w τ => ?_⟩
    have hU := hg.2 w τ
    set U := (inBasis σ T g).map (piInf τ)
    set V := (inBasis σ T g⁻¹).map (piInf τ)
    have hVU : V * U = 1 := by
      simp only [V, U]
      rw [← Matrix.map_mul, ← inBasis_mul, inv_mul_cancel, inBasis_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hV : V = star U := by
      calc V = V * (U * star U) := by rw [Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mul_one]
        _ = (V * U) * star U := by rw [Matrix.mul_assoc]
        _ = star U := by rw [hVU, Matrix.one_mul]
    show V ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ
    rw [hV, Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.1 hU

theorem mem_stdK_iff (g : UA σ J₂) : g ∈ stdK σ T ↔
    (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧ compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ :=
  Iff.rfl

theorem isStdK_stdK : IsStdK σ T (stdK σ T : Subgroup (UA σ J₂)) := fun g => mem_stdK_iff σ T g

omit [NumberField F] [NumberField E] in

theorem opNorm_le_one {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm U ≤ 1 := by
  have h1 : opNorm (star U * U) ≤ 1 := by
    rw [Matrix.mem_unitaryGroup_iff'.1 hU]; exact opNorm_one_le
  unfold opNorm at h1 ⊢
  rw [map_mul, map_star, CStarRing.nnnorm_star_mul_self, ← sq] at h1
  exact (pow_le_one_iff_of_nonneg zero_le two_ne_zero).1 h1

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F)
    (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
      change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
      rw [infEmb_tmul, map_one, mul_one]; rfl

omit [NumberField F] [NumberField E] in
theorem bc_val {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (f : A →+* B)
    (x : GL m A) : ((Formalism.UG.bc f x : GL m B) : Matrix m m B) = (x : Matrix m m A).map f := rfl

theorem piInf_eq {w : InfinitePlace F} (τ : EmbOver E w) : ⇑(piInf τ) = ⇑(infEmb τ) ∘ ⇑(compInf F E w) := rfl

def basGL : GL (Fin (n + n)) (AE F E) := Formalism.UG.bc (inclR (F := F) (AF F)) T

def conjB (g : UA σ J₂) : GL (Fin (n + n)) (AE F E) := (basGL T)⁻¹ * g.1 * basGL T

theorem conjB_val (g : UA σ J₂) :
    ((conjB σ T g : GL (Fin (n + n)) (AE F E)) : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) = inBasis σ T g := by
  rw [conjB, Units.val_mul, Units.val_mul, basGL, ← map_inv, bc_val, bc_val]
  rfl

theorem conjB_inv (g : UA σ J₂) : (conjB σ T g)⁻¹ = conjB σ T g⁻¹ := by
  simp only [conjB, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]

theorem height_conjB_le {g : UA σ J₂} (hg : g ∈ stdK σ T) : heightGL F (conjB σ T g) ≤ 1 := by
  have hg' : g⁻¹ ∈ stdK σ T := inv_mem hg
  refine le_of_eq ((heightGL_eq_one_iff F).2 ⟨fun w => ?_, fun v => ?_⟩)
  · have e1 : ((Formalism.UG.bc (compInf F E w)) (conjB σ T g))⁻¹ = Formalism.UG.bc (compInf F E w) (conjB σ T g⁻¹) := by
      rw [← map_inv, conjB_inv]
    refine htOf_eq_one.2 ⟨(normInf_le_iff F w).2 fun τ => ?_, (normInf_le_iff F w).2 fun τ => ?_⟩
    · rw [bc_val, Matrix.map_map, conjB_val, ← piInf_eq]
      exact opNorm_le_one (hg.2 w τ)
    · rw [e1, bc_val, Matrix.map_map, conjB_val, ← piInf_eq]
      exact opNorm_le_one (hg'.2 w τ)
  · have e1 : ((Formalism.UG.bc (compFin F E v)) (conjB σ T g))⁻¹ = Formalism.UG.bc (compFin F E v) (conjB σ T g⁻¹) := by
      rw [← map_inv, conjB_inv]
    refine htOf_eq_one.2 ⟨(normFin_le_iff F v).2 fun i j => ?_, (normFin_le_iff F v).2 fun i j => ?_⟩
    · rw [bc_val, Matrix.map_apply, conjB_val]
      exact absFin_le_one_of_mem_intLoc (hg.1 v i j).1
    · rw [e1, bc_val, Matrix.map_apply, conjB_val]
      exact absFin_le_one_of_mem_intLoc (hg'.1 v i j).1

theorem isCompact_stdK (h : IsCMExt F E σ) : IsCompact ((stdK σ T : Subgroup (UA σ J₂)) : Set (UA σ J₂)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hcl : IsClosed (UG (cA σ) (incM F J₂) : Set (GL (Fin (n + n)) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin (n + n)) (AE F E) => (g : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) :=
      Units.continuous_val
    have hc : Continuous (cA σ : AE F E → AE F E) :=
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (F := F) (E := E) (AF F) σ).congr fun z => (GlobalTheory.IwLine.cA_eq_sigR σ z).symm
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hc))
      continuous_const
  have hemb : Topology.IsClosedEmbedding (conjB σ T (J₂ := J₂)) :=
    ((Homeomorph.mulLeft (basGL T)⁻¹).trans (Homeomorph.mulRight (basGL T))).isClosedEmbedding.comp
      hcl.isClosedEmbedding_subtypeVal
  have hcont : Continuous fun g : UA σ J₂ => inBasis σ T g :=
    (Units.continuous_val.comp hemb.continuous).congr (conjB_val σ T)
  have hcont' : Continuous fun g : UA σ J₂ => inBasis σ T g⁻¹ := hcont.comp continuous_inv
  have hOc : ∀ v : HeightOneSpectrum (𝓞 F), IsClosed (intLoc F E v : Set (Fv F v ⊗[F] E)) := fun v => by
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) _
    exact AddSubgroup.isClosed_of_isOpen (intLoc F E v).toAddSubgroup (GlobalTheory.ThK.isCompact_isOpen_intLoc v).2
  have hKc : IsClosed ((stdK σ T : Subgroup (UA σ J₂)) : Set (UA σ J₂)) := by
    have e0 : ((stdK σ T : Subgroup (UA σ J₂)) : Set (UA σ J₂)) =
        (⋂ v, ⋂ i, ⋂ j, ((fun g : UA σ J₂ => compFin F E v (inBasis σ T g i j)) ⁻¹' (intLoc F E v : Set _) ∩
          (fun g : UA σ J₂ => compFin F E v (inBasis σ T g⁻¹ i j)) ⁻¹' (intLoc F E v : Set _))) ∩
        ⋂ w, ⋂ τ : EmbOver E w, (fun g : UA σ J₂ => (inBasis σ T g).map (piInf τ)) ⁻¹'
          (Matrix.unitaryGroup (Fin (n + n)) ℂ : Set (Matrix (Fin (n + n)) (Fin (n + n)) ℂ)) := by
      ext g
      simp only [SetLike.mem_coe, mem_stdK_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rw [e0]
    refine IsClosed.inter (isClosed_iInter fun v => isClosed_iInter fun i => isClosed_iInter fun j =>
      IsClosed.inter ?_ ?_) (isClosed_iInter fun w => isClosed_iInter fun τ => ?_)
    · exact (hOc v).preimage ((GlobalTheory.ThK.LemF.QuotInv.continuous_compFinV v).comp
        ((continuous_apply j).comp ((continuous_apply i).comp hcont)))
    · exact (hOc v).preimage ((GlobalTheory.ThK.LemF.QuotInv.continuous_compFinV v).comp
        ((continuous_apply j).comp ((continuous_apply i).comp hcont')))
    · exact isClosed_unitary.preimage (hcont.matrix_map (continuous_piInf τ))
  exact (hemb.isCompact_preimage (isCompact_heightGL_le F 1)).of_isClosed_subset hKc
    fun g hg => height_conjB_le σ T hg

theorem exists_wittBasis_stdK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (l : E) (J : Matrix (Fin n) (Fin n) E)
    (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E), l ≠ 0 → J.det ≠ 0 → J₂ = dblGram finSumFinEquiv J →
    ∃ (T : GL (Fin (n + n)) E) (K : Subgroup (UA σ J₂)), IsWittBasis σ J l T ∧ IsStdK σ T K ∧
      IsCompact (K : Set (UA σ J₂)) := by
  intro F E _ _ _ _ _ σ h n l J J₂ hl hJ _
  obtain ⟨T, hT⟩ := exists_isWittBasis σ h l J hl hJ
  exact ⟨T, stdK σ T, hT, isStdK_stdK σ T, isCompact_stdK σ T h⟩

end GlobalTheory.SWLit.WittStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlaceStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_bar_good_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι := by
  first | exact @GlobalTheory.LinBarAt.exists_isLinBar_at | exact GlobalTheory.LinBarAt.exists_isLinBar_at | (intros; apply GlobalTheory.LinBarAt.exists_isLinBar_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_witt_model_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  first | exact @GlobalTheory.LinWSplit.exists_isLinW_at | exact GlobalTheory.LinWSplit.exists_isLinW_at | (intros; apply GlobalTheory.LinWSplit.exists_isLinW_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaIdentityStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_identity : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks), ∀ (Qr : RealRec Q), Q.Rl.toRealDat.ExAt → Formalism.IndefR.RecTie.ThetaFireRow (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.hTop Qr.hinj) Qr.IL := by
  first | exact @GlobalTheory.thetaFireRow_recTie | exact GlobalTheory.thetaFireRow_recTie | (intros; apply GlobalTheory.thetaFireRow_recTie <;> assumption)
end

