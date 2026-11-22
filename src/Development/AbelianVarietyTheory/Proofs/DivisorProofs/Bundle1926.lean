import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongrStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.FrameTransport.Cong.conj_mem_congLev | exact GlobalTheory.FrameTransport.Cong.conj_mem_congLev | (intros; apply GlobalTheory.FrameTransport.Cong.conj_mem_congLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StdPairPlaces

theorem coprime_of_splitK {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by
  have hn : ¬ p ∣ H.condN := not_dvd_of_splitK hp h
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn

theorem natCast_two_q_d_notMem : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D large₂ hR T L sc G μ₀ hL t w hw
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  have hsp : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp h =>
    coprime_of_splitK hp (Pm.level_split p h)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ LevelStarExponents.condE D := dvd_rfl
  rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine GlobalTheory.HalfCompare.not_mem_of_coprime w (b := q0 D) ?_ ((GlobalTheory.FunObj.Good.natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      exact (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1 (hdvd.mul_left _)).symm
    · simp only [S1_mem_OmF, GlobalTheory.FunObj.Good.natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 0) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 1) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde_prime D.host.pde_level.1).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde'_prime D.host.pde_level.2).symm a
  · exact fun h => (hL.Q_off t w b).1 (GlobalTheory.HalfCompare.mem_of_dvd h ⟨D.sp.T, by ring⟩)

end GlobalTheory.StdPairPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

namespace GlobalTheory.BotSmallDict

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in

theorem cosetFn_isSBHalf : ∀ {D : D7} (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Submodule.IsLattice D.host.E LS → Submodule.IsLattice D.host.E LT → ∀ (a : Formalism.L2.Theta.AE D), infPart D a = 0 →
    ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ x : WO S T, IsHalf a x →
      IsSBHalf a (latO S T LS LT fun _ => True) (cosetFn a I x) := by
  intro D S T LS LT hS hT a hinf I hI x _
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT (S := S) (T := T)
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_common_nsmul (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup
    (fun p : Fin T.rank × Fin S.rank => toEAf D (x p.1 p.2)) fun p => GlobalTheory.PlaceVec.exists_nsmul_mem_int _
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  have hsupp : ∀ t, cosetFn a I x t ≠ 0 →
      IsHalf a t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j)) := fun t ht => by
    unfold cosetFn at ht
    by_contra h
    exact ht (if_neg h)
  refine ⟨fun t ht => (hsupp t ht).1, n₀ * k₁ * (k₄ * d), by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  ·
    have hw : ∀ i j, ((k₄ * d) • (k₁ • u.map (toEAf D))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun i j => nsmul_mem (h₁ u hu i j) _
    have hsh : ∀ i j, toEAf D ((t + (n₀ * k₁ * (k₄ * d)) • u : WO S T) i j - x i j) =
        toEAf D (t i j - x i j) + (n₀ : EAf D) * ((k₄ * d) • (k₁ • u.map (toEAf D))) i j := fun i j => by
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, RingHom.map_sub,
        RingHom.map_sub, RingHom.map_add, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    have hH : IsHalf a (t + (n₀ * k₁ * (k₄ * d)) • u) ↔ IsHalf a t := by
      rw [GlobalTheory.PlaceModel.isHalf_iff S T, GlobalTheory.PlaceModel.isHalf_iff S T]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh) _)
    have hC : (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D ((t + (n₀ * k₁ * (k₄ * d)) • u : WO S T) i j - x i j))) ↔
        ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j)) :=
      ⟨fun H i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hnI (neg_mem (hw i j))
          (by rw [hsh, mul_neg, add_neg_cancel_right]) (H i j),
        fun H i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hnI (hw i j) (hsh i j) (H i j)⟩
    unfold cosetFn
    by_cases hc : IsHalf a t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j))
    · rw [if_pos hc, if_pos ⟨hH.2 hc.1, hC.2 hc.2⟩]
    · rw [if_neg hc, if_neg fun h' => hc ⟨hH.1 h'.1, hC.1 h'.2⟩]
  ·
    obtain ⟨hth, htc⟩ := hsupp t ht
    have hint : IsIntM ((d • t).map (toEAf D)) := fun i j => by
      have e : ((d • t).map (toEAf D)) i j = d • toEAf D (t i j - x i j) + d • toEAf D (x i j) := by
        rw [GlobalTheory.PlaceVec.map_toEAf_nsmul, Matrix.smul_apply, Matrix.map_apply, ← smul_add, RingHom.map_sub, sub_add_cancel]
      rw [e]
      exact add_mem (nsmul_mem (htc i j).1 d) (show d • toEAf D (x i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E from hx (i, j))
    have hinf' : (d • t).map (infPart D) = 0 :=
      GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hth) d)
    have h := nsmul_mem (h₄ (d • t) hinf' hint) (n₀ * k₁)
    rw [smul_smul, smul_smul] at h
    rwa [← mul_assoc (n₀ * k₁)]

end GlobalTheory.BotSmallDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFiniteMulSupportIdealFac
section
noncomputable section

namespace GlobalTheory.EulerIdeal

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.L2.Host (aboveF)
open scoped nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_count (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w 𝔞 ≠ 0}.Finite :=
  Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)

theorem hasFiniteMulSupport_zpow {M : Type} [DivInvMonoid M] (x : HeightOneSpectrum (𝓞 E) → M)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    Function.HasFiniteMulSupport fun w => x w ^ FractionalIdeal.count E w 𝔞 :=
  (finite_count 𝔞).subset fun w hw h0 => hw (by simp only [h0, zpow_zero])

theorem idealVal_mul (χ : Chr F E) {𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) (h𝔠 : 𝔠 ≠ 0) :
    idealVal χ (𝔟 * 𝔠) = idealVal χ 𝔟 * idealVal χ 𝔠 := by
  unfold idealVal
  simp only [FractionalIdeal.count_mul E _ h𝔟 h𝔠, zpow_add]
  exact finprod_mul_distrib (hasFiniteMulSupport_zpow _ _) (hasFiniteMulSupport_zpow _ _)

theorem idealVal_inv (χ : Chr F E) (𝔟 : FractionalIdeal (𝓞 E)⁰ E) : idealVal χ 𝔟⁻¹ = (idealVal χ 𝔟)⁻¹ := by
  unfold idealVal
  simp only [FractionalIdeal.count_inv, zpow_neg]
  exact finprod_inv_distrib _

def idealFac (χ : Chr F E) (𝔪 𝔞 : FractionalIdeal (𝓞 E)⁰ E) (s : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  (val χ w : ℂ) ^ FractionalIdeal.count E w 𝔪 *
    ((((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ FractionalIdeal.count E w 𝔞) ^ s)⁻¹

section Constants

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def diffK : FractionalIdeal (𝓞 K)⁰ K := (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)

end Constants

def kaLoc (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) (a' d : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (∏ w ∈ aboveF (L := E) F v, ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count E w 𝔟) ^ (-(d : ℝ) / 2) *
    ((∏ w ∈ aboveF (L := E) F v, ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count E w 𝔠) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count F v (diffK F)) ^ (-((a' : ℝ) - 2) / 2)

def kaGlob (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) (a' d : ℕ) : ℝ :=
  (FractionalIdeal.absNorm 𝔟 : ℝ) ^ (-(d : ℝ) / 2) *
    ((FractionalIdeal.absNorm 𝔠 : ℝ) * |(discr F : ℝ)|) ^ (-((a' : ℝ) - 2) / 2)

open GlobalTheory.ThK

variable {σ : E →ₐ[F] E}

end GlobalTheory.EulerIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharRestrictsEtaPowOfSign
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeSignEta

theorem idF_ratF (D : D7) (a : D.host.Fˣ) :
    idF D (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) =
      Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom a) := by
  refine Units.ext ?_
  show algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (a : D.host.F)) =
    incA D (algebraMap D.host.F D.host.E (a : D.host.F))
  show _ = Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E (a : D.host.F))
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]

theorem resEta_of_sign : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (N : ℕ), IsHeckeChar D χ →
    (∀ x y : (AE D)ˣ, (y : AE D) = x * cA D x → χ y = 1) →
    ∀ θ : InfFam D, IsInfFam θ →
    (∀ (τ : D.what₂.Tau) (x : (AE D)ˣ), finPart D (x : AE D) = 1 → θ τ (infPart D (x : AE D)) = -1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) → ((χ x : Circle) : ℂ) = (-1) ^ N) →
    ResEta D χ N := by
  intro D χ N hχ hnorm θ hθ hsign
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun ε hε => ?_⟩

  set ψ : (AF D.host.F)ˣ →* Circle := χ.comp (idF D) * (ε ^ N)⁻¹ with hψ
  have hψa : ∀ a, ψ a = χ (idF D a) * (ε a ^ N)⁻¹ := fun a => rfl
  have hker : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normGroup D ≤ ψ.ker := by
    rw [GlobalTheory.VolHeckeCompare.normGroup_eq]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      show ψ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1
      rw [hψa, idF_ratF, hχ.2, hε.2.1 a, one_pow, inv_one, mul_one]
    · rintro _ ⟨x, rfl⟩
      obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
      have e : (idF D (GlobalTheory.VolHeckeCompare.normU D x) : AE D) = (x : AE D) * cA D (x : AE D) := by
        have e0 : idF D (GlobalTheory.VolHeckeCompare.normU D x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normId D x := hN x
        rw [e0]; rfl
      show ψ (GlobalTheory.VolHeckeCompare.normU D x) = 1
      rw [hψa, hnorm x _ e, hε.2.2.1 x, one_pow, inv_one, mul_one]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := hsign τ x x1 xτ xo
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := GlobalTheory.SplitParity.exists_idF_of_fixed D x hfix

  have hneg : ∀ ε', IsEta D ε' → ((ε' y : Circle) : ℂ) = -1 := fun ε' hε' => by
    have c2 := hη1.2 ε' hε' y
    rw [hy, pow_one] at c2
    rw [← c2, hηc]
  have hψy : ψ y = 1 := by
    refine Circle.ext ?_
    rw [hψa, hy, Circle.coe_mul, Circle.coe_inv, Circle.coe_pow, hcx, hneg ε hε, Circle.coe_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  have hψ1 : ψ = 1 := by
    by_contra hne
    have hψE : IsEta D ψ := (GlobalTheory.VolHeckeCompare.isEta_iff_normGroup D ψ).2 ⟨hker, hne⟩
    have := hneg ψ hψE
    rw [hψy, Circle.coe_one] at this
    norm_num at this
  intro a
  have ha : ψ a = 1 := by rw [hψ1]; rfl
  rw [hψa, mul_inv_eq_one] at ha
  exact ha

end GlobalTheory.HeckeSignEta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeFockVectorsUniformOperator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockDerUnif

open GlobalTheory.ChainFr Formalism.IndefR.Datum GlobalTheory.FockCreaDir

theorem dRho_ptF_uniform : ∀ {D : D7} {V W : HSp D} (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Δ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ P, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f (Δ P) := by
  classical
  intro D V W A B θ ψ hψ hθ τ z
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨e, rfl⟩ : ∃ e : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, e i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  set zz := ∑ i, ∑ j, e i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j with hzz
  have hc0 : ∀ k : FVar D W.rank V.rank, ∃ ck : ℂ, ∀ g, IsThetaFunO ψ V W g →
      annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz
        (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb k g) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb k
        (annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz g) + ck • g :=
    fun k => ⟨_, fun g h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ zz hS hT k.1 _ h⟩
  choose c hc using hc0
  let Δ₁ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank :=
    ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) •
      LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D W.rank V.rank)
  let Δ₂ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank :=
    ∑ k, c k • (MvPolynomial.pderiv k : Derivation ℂ (PolF D W.rank V.rank) (PolF D W.rank V.rank)).toLinearMap
  refine ⟨(1 / 2 : ℂ) • (Δ₁ + Δ₂), fun f hf P => ?_⟩

  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf.1 Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf.1 P
  have hΔ₁ : Δ₁ P = ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) • (MvPolynomial.X (τ, i, j) * P) := by
    first
      | simp only [Δ₁, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
      | simp [Δ₁, LinearMap.sum_apply]
  have hΔ₂ : Δ₂ P = ∑ k, c k • MvPolynomial.pderiv k P := by
    first
      | simp only [Δ₂, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
      | simp [Δ₂, LinearMap.sum_apply]
  have hcr : crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz (GlobalTheory.ChainFr.ptF ψ θ A B f P) =
      GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₁ P) := by
    have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
        crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
          ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g :=
      fun y g => by
        rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
    rw [h1, hΔ₁]
    have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
        (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) • (MvPolynomial.X (τ, i, j) * P)) =
        ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) •
          Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
            (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
      unfold GlobalTheory.ChainFr.ptF pureTensorO
      simp only [map_smul, map_sum, hX]
      rfl
    rw [h2]
    congr 1
    rw [hzz, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
  have han : annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz (GlobalTheory.ChainFr.ptF ψ θ A B f P) =
      GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₂ P) := by
    rw [hΔ₂]
    exact GlobalTheory.ArchRec.DerFock.pure_deriv (P := IsThetaFunO ψ V W)
      (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb)
      (B := annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz)
      hadd hsm hth
      (fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h)
      (fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h')
      (fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h)
      (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ h h')
      (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ a h)
      (fun j g h => hc j g h) hf.1 (hf.2 τ zz) P
  have hsplit : GlobalTheory.ChainFr.ptF ψ θ A B f (((1 / 2 : ℂ) • (Δ₁ + Δ₂)) P) =
      (1 / 2 : ℂ) • (GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₁ P) + GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₂ P)) := by
    rw [LinearMap.smul_apply, LinearMap.add_apply]
    unfold GlobalTheory.ChainFr.ptF
    rw [map_smul, map_add]
  rw [hsplit, ← hcr, ← han, crea, annih]
  module

end GlobalTheory.FockDerUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergStableRelation_of_vacua : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ {ι : Type} (P : Finset ι) (pl : ι → HeightOneSpectrum (𝓞 F)), Set.InjOn pl P →
    ∀ (Z : ι → Type) [∀ w, TopologicalSpace (Z w)] [∀ w, Add (Z w)]
      (A A' : ι → Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
      (co : ∀ w, Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z w)
      (I : ∀ w, ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ] (Z w → ℂ))
      (H : AddSubgroup (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
      (R : Submodule ℂ ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)))
      (f : SInf F (Fin n × Fin d)),
    (∀ w ∈ P, IsLagrModel M ψ (pl w) (A w) (A' w) (co w) (I w)) →
    (∀ w ∈ P, ∀ u ∈ A w, At (evFin F (pl w)) u ∧ u ∈ H) → (∀ w ∈ P, ∀ u ∈ A' w, At (evFin F (pl w)) u) →
    (∀ w ∈ P, ∀ u, At (evFin F (pl w)) u → ∃ x ∈ A w, ∃ y ∈ A' w, u = x + y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ u, co w (u + x) = co w u + co w x) →
    (∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x ∈ A w, ∀ u, co w' (u + x) = co w' u) →
    (∀ w ∈ P, ∀ u, ∃ x ∈ A w, co w x = co w u ∧ ∀ y ∈ A' w,
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y =
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ p ∈ R, (fun u => p.1 (u + x), M.co.rho ψ x p.2) ∈ R) →
    (∀ w ∈ P, ∀ y ∈ A' w, ∀ p ∈ R, (fun u => ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) * p.1 u, M.co.rho ψ y p.2) ∈ R) →
    (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) ∈ R →
    ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R := by
  first | exact @GlobalTheory.InductLagr.rel_of_vac | exact GlobalTheory.InductLagr.rel_of_vac | (intros; apply GlobalTheory.InductLagr.rel_of_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelComponentShortBasisBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_component_short_basis_bound : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  first | exact @GlobalTheory.HSShort.hsClaimS_component_geo | exact GlobalTheory.HSShort.hsClaimS_component_geo | (intros; apply GlobalTheory.HSShort.hsClaimS_component_geo <;> assumption)
end

