import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupSymplecticAnnihilatorLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruentStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalIdempotent_divisible_congruent : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit | exact GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit | (intros; apply GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTrace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.UnramTraceDenom

theorem exists_not_mem_mul_isIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl F) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  intro F E _ _ _ _ _ hU v e h
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hU
  haveI := v.isPrime
  let b := NumberField.RingOfIntegers.basis E
  have hloc : ∀ i, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F s * Algebra.trace F E ((b i : E) * e) = algebraMap (𝓞 F) F r := by
    intro i
    apply GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem
    have hi := h (b i)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hi
    have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Algebra.trace F E ((b i : E) * e))
    exact e1 ▸ hi
  choose s hs r hr using hloc
  refine ⟨∏ i, s i, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hs i hi
  · have key : ∀ i, algebraMap (𝓞 F) F (∏ j, s j) * Algebra.trace F E ((b i : E) * e) ∈
        (algebraMap (𝓞 F) F).range := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap (𝓞 F) F (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    have htr : ∀ a : 𝓞 E, Algebra.trace F E (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * a) ∈
        (algebraMap (𝓞 F) F).range := by
      intro a
      have ha : (a : E) = ∑ i, ((b.repr a i : ℤ) : E) * (b i : E) := by
        have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr a)
        simpa [map_sum, zsmul_eq_mul] using this.symm
      rw [ha, Finset.mul_sum, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      have e2 : algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * (((b.repr a i : ℤ) : E) * (b i : E)) =
          algebraMap F E (((b.repr a i : ℤ) : F) * algebraMap (𝓞 F) F (∏ j, s j)) * ((b i : E) * e) := by
        have hc : ((∏ i, s i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∏ j, s j) := rfl
        rw [hc, map_mul, map_intCast]; ring
      rw [e2, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_assoc]
      exact Subring.mul_mem _ (intCast_mem _ _) (key i)
    obtain ⟨y, hy⟩ := GlobalTheory.InertSelfDual.mem_of_trace (F := F) (E := E)
      (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e) htr
    rw [← hy]; exact RingOfIntegers.isIntegral_coe y

end GlobalTheory.UnramTraceDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionMaxLevelUnitaryModIdeal
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.LevelRed

open GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem mk_eq_iff (h𝔪 : 𝔪 ≠ ⊥) (r b : 𝓞 D.host.E) :
    Ideal.Quotient.mk 𝔪 r = Ideal.Quotient.mk 𝔪 b ↔
      inc D (r : D.host.E) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  have e : inc D (r : D.host.E) - inc D (b : D.host.E) = inc D ((r - b : 𝓞 D.host.E) : D.host.E) := by
    push_cast
    rw [map_sub]
  rw [Ideal.Quotient.eq, e]
  constructor
  · intro h
    simpa using gen_mem_hatId D 𝔪 h (one_mem (OhE D))
  · intro h
    obtain ⟨c, hc, e'⟩ := (FractionalIdeal.mem_coeIdeal _).1 (GlobalTheory.HeisTranslate.mem_of_inc_mem_hatId h𝔪 h)
    have : c = r - b := RingOfIntegers.coe_injective e'
    exact this ▸ hc

theorem exists_redHom (h𝔪 : 𝔪 ≠ ⊥) : ∃ red : OhE D →+* 𝓞 D.host.E ⧸ 𝔪, ∀ (x : OhE D) (b : 𝓞 D.host.E),
    red x = Ideal.Quotient.mk 𝔪 b ↔ (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  choose r hr using fun x : OhE D => exists_red D 𝔪 h𝔪 (x : AE D) x.2
  have key : ∀ (x : OhE D) (b : 𝓞 D.host.E), Ideal.Quotient.mk 𝔪 (r x) = Ideal.Quotient.mk 𝔪 b ↔
      (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
    intro x b
    rw [mk_eq_iff D 𝔪 h𝔪]
    constructor
    · intro h
      have := add_mem (hr x) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hr x)
      rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := fun x => Ideal.Quotient.mk 𝔪 (r x)
            map_one' := ?_
            map_mul' := fun x y => ?_
            map_zero' := ?_
            map_add' := fun x y => ?_ }, key⟩
  · rw [← map_one (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_mul, key]
    have := add_mem (mul_mem_hatId D 𝔪 y.2 (hr x))
      (mul_mem_hatId D 𝔪 (VacMove.inc_int D (r x)) (hr y))
    convert this using 1
    push_cast
    rw [map_mul]
    ring
  · rw [← map_zero (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_add, key]
    have := add_mem (hr x) (hr y)
    convert this using 1
    push_cast
    rw [map_add]
    ring

def intMat (N : ℕ) : ↥(intG D N) →* Matrix (Fin N) (Fin N) (OhE D) where
  toFun k := Matrix.of fun i j =>
    ⟨(((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j, (((mem_intG _).1 k.2) i j).1⟩
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  map_mul' x y := by
    ext i j
    simp [Matrix.mul_apply]

theorem exists_levelRed : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  intro D 𝔪 h𝔪 N
  obtain ⟨red, hred⟩ := exists_redHom D 𝔪 h𝔪
  exact ⟨((red.mapMatrix (m := Fin N)).toMonoidHom.comp (intMat D N)).toHomUnits,
    fun k i j b => hred (intMat D N k i j) b⟩

end GlobalTheory.LevelRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRichRecordOverChoices
section
noncomputable section

namespace GlobalTheory.BigOn.Inhab

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
open GlobalTheory.FieldSize GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.Pj Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.RunJoin
open GlobalTheory.Mem
open GlobalTheory.EX.OB

def RichRec (D : D7) : Prop :=
  GlobalTheory.Mem.Chr.SplitsC D.host.E D.host.pde ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E D.host.pde' ∧
    (∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) ∧
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber D.host.E) ∈ FO D

set_option maxHeartbeats 1000000 in

theorem exists_rich_record_over_choices (hR : GlobalTheory.NT.RayField) (eps cD ch : ℝ) (C : FC) (h0 : 0 < eps) (h1 : eps < 1 / 52)
    (hC : Std C) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ)
      (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P), s.eps = eps → x0 ≤ s.x →
      ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R →
      ∃ D : D7, (JointQ D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber D.host.E) ∈ FO D) ∧ Nonempty (ErrX D) ∧ DV.KapDef D ∧ HostArith D.host ∧
        ∃ L : SizeData₂ D, L.sc = s ∧ Val C cD ch L := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv hs hx hP hG
  obtain ⟨F, hfd, hrich, hsz⟩ := exists_rich_small_of_rayField hR (StdFrameObj.coordPre P Lv)
  obtain ⟨B, hB, hF, -⟩ := exists_base_of_rich _ F hfd hrich ∅ ∅ (by simp) (by simp)
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hDel : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < Delv s cD := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (StdFrameObj.coordPre P Lv).level_split
  have key : ∀ Q : Pre, Q = StdFrameObj.coordPre P Lv → ∃ letter : Q.Word → Fin (Q.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ w τ (l : ℕ) (h : l + 1 < Q.R.k - 1),
        (Q.hcW w τ).v ⟨l, by omega⟩ - (Q.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv s cD : ℚ)) ∧
      ∀ w τ (l : ℕ) (h : l < Q.R.k - 2), (Q.hcW w τ).u ⟨l + 1, by omega⟩ =
        (Q.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv s cD : ℚ) else 0) := by
    rintro Q rfl
    refine ⟨c, hP.inj, fun w τ l h => ?_, fun w τ l h => hP.code w τ l h⟩
    have h' : l + 1 < P.R.k - 1 := h
    have a1 := (hP.hc w).1 τ ⟨l, by omega⟩
    have a2 := (hP.hc w).1 τ ⟨l + 1, h'⟩
    refine (congrArg₂ (· - ·) a1 a2).trans ?_
    have : P.R.k - 2 - l = (P.R.k - 2 - (l + 1)) + 1 := by omega
    simp only [this]
    push_cast
    ring
  obtain ⟨letter, k1, k2, k3⟩ := key B.toPre hB
  obtain ⟨X, rfl, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_stages_with_delta B (Delv s cD : ℚ) letter (6 * s.x ^ (-C.P.CF)) hDel (by positivity) k1 k2 k3
  clear key k1 k2 k3 letter
  have hJ : JointQ X.toD7 := jointQ_of_small_field X F (hB ▸ hrich)
    ((congrArg (fun Q : Pre => ∀ L : ℝ, HostSz Q.host L → Sz F (poR Q.R L) (poR Q.R L)) hB).mpr hsz) hF
  have hZ := (fieldOK0_and_zeta_mem X F (hB ▸ hrich) hF _ (Or.inl rfl)).2
  have hE : Nonempty (ErrX X.toD7) := GlobalTheory.T.error_data_of_norm_generators X
    ((congrArg (fun Q : Pre => ∀ i, ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E)) hB).mpr hP.arith.1)
  clear hF hrich hsz
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  refine ⟨D, ⟨hJ, hZ⟩, hE, e3, ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_⟩
  obtain ⟨L, l1, -, -, l4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog e1 hP.ct2
    hP.card e2 (fun u => by
      have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
      rw [e, hG, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) e4
  exact ⟨L, l1, l4⟩

theorem exists_richRec_of_zeroFreeRegion : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → GlobalTheory.NT.RayField → ∀ x : ℝ, ∃ D : D7, RecOK D x ∧ RichRec D := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 p9 hR x
  have hH := DC.hostExQ_of_hostEx (smallPrimeOne_of_tzRat p6) (hostEx_of_zeroFreeRegion p1 p2 p3 p4 p5 p6 p7 p8 p9)
  have hLP := (normPrimes_and_levelPrime p9).2
  have he : (0 : ℝ) < 1 / 53 := by norm_num
  have he52 : (1 / 53 : ℝ) < 1 / 52 := by norm_num
  obtain ⟨CT2, C8, C5, c6, Cb, hC8, -, -, -, hK⟩ := exists_chGood_unb hH _ he he52
  obtain ⟨C, hStd, hCT2, hCp, -⟩ := exists_std_large ⟨0, 0, fun _ => 0, fun _ => 0⟩
    ⟨0, 0, fun _ => 0, fun _ => 0⟩ CT2 C8 hC8
  obtain ⟨c1, hN⟩ := szRow_numAt _ he he52 C hStd
  obtain ⟨c2, hN⟩ := hN (max c1 0) (le_max_left _ _)
  obtain ⟨x1, hN⟩ := hN (max c2 402) (le_max_left _ _)
  have hK := hK C hStd hCT2 hCp (max c1 0) (le_max_right _ _) (max c2 402) (le_max_right _ _)
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP _ 1 C he he52 one_pos hStd
  obtain ⟨x4, h4⟩ := exists_rich_record_over_choices hR _ (max c1 0) (max c2 402) C he he52 hStd (le_max_right _ _) (le_max_right _ _)
  obtain ⟨s, hs, hy, hK⟩ := hK (max (10 ^ 60) (max x1 (max x3 (max x4 (max x (C.T.CP ^ 20))))))
  simp only [max_le_iff] at hy
  obtain ⟨hy60, hy1, hy3, hy4, hyx, hyP⟩ := hy
  obtain ⟨P, a, b, c, hP, -⟩ := hK 0
  have hfk : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := by
    have h1 := P.R.m_add_three_le_k
    have h2 : 0 < P.R.f := by have := P.R.ord_pos; show 0 < 2 * P.R.ord; omega
    have h3 : 0 < P.R.k := by omega
    positivity
  obtain ⟨Ds, hDs, hlog⟩ := exists_window_start _ (1 * P.R.m * s.L) (GamS C s P.R) hfk (Real.exp_pos _)
  obtain ⟨Lv, -, -, l3⟩ := h3 _ _ s P _ a b c (fun _ => 1) Ds hs hy3 hP.ok (fun _ => one_pos) hDs (fun _ => hlog)
  obtain ⟨D, ⟨⟨h1, h2, h3, h4, h5⟩, hZ⟩, hE, hkap, hA, L, hsc, hV⟩ := h4 s P _ a b c Lv hs hy4 hP.ok l3
  have hsx : L.sc.x = s.x := by rw [hsc]
  have hse : L.sc.eps = 1 / 53 := by rw [hsc, hs]
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy1.trans hsx.ge) hV hA
  have hCP : N.parT.CP = C.T.CP := (List.cons.inj N.parT_K).1
  have hg : ∀ j, Real.log (D.host.g j) ≤ 9 * L.sc.L + 1 := fun j => by
    have hL : 0 ≤ L.sc.L := by
      unfold Scale.L; exact Real.rpow_nonneg (zero_le_one.trans L.sc.one_lt_alt.le) _
    have hlo : 0 < ((D.host.g j : ℕ) : ℝ) := by exact_mod_cast (D.host.g_prime j).pos
    have := (Real.log_le_iff_le_exp hlo).2 (N.g_le j)
    linarith
  obtain ⟨hHS, hFS⟩ := hostSz_of_sizes D L N.params N.parT N.sizes hg (hy60.trans hsx.ge)
  refine ⟨D, ⟨h1, h2, h3, h4, hE, L, N.params, N.parT, hkap, N.sizes,
    N.CnW_eq.trans hStd.1.2.2.2.2.2.2.2.1, hg, ?_, ?_, hyx.trans hsx.ge, hFS (h5 _ hHS)⟩,
    (GlobalTheory.Mem.Chr.ncard_places_eq_primesOver D.host.pde_prime).trans hA.2.2.1.1,
    (GlobalTheory.Mem.Chr.ncard_places_eq_primesOver D.host.pde'_prime).trans hA.2.2.1.2, hV.hc.2.2.2, hZ⟩
  · rw [hCP]; exact hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hCP]
    exact hyP.trans (hsx.ge.trans (x_le_zBase_of_pow_le_n L N.win.1.1))

end GlobalTheory.BigOn.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_schroedingerFixed_localField : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  first | exact @GlobalTheory.SchrTestVec.exists_fixed | exact GlobalTheory.SchrTestVec.exists_fixed | (intros; apply GlobalTheory.SchrTestVec.exists_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedOppositeLagrangianCoordinateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)),
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧ GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  first | exact @GlobalTheory.VacShape.exists_at_coBar_eq | exact GlobalTheory.VacShape.exists_at_coBar_eq | (intros; apply GlobalTheory.VacShape.exists_at_coBar_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupSymplecticAnnihilatorLocalFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subgroup_symplecticAnnihilator_localField : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ {κ : Type} [Fintype κ] (N : Set ((κ → Fv F v) × (κ → Fv F v))), N ∈ nhds 0 →
    ∃ Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)),
      (∀ w' : (κ → Fv F v) × (κ → Fv F v), (∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1) → w' ∈ N) ∧
      ∃ N' ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w' ∈ N', ∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1 := by
  first | exact @GlobalTheory.SympDualNbhd.exists_dual_nbhd | exact GlobalTheory.SympDualNbhd.exists_dual_nbhd | (intros; apply GlobalTheory.SympDualNbhd.exists_dual_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductionsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typeFrame_cover_levelMaps_reductions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  first | exact @GlobalTheory.TypeFrameCover.typeFrame_cover | exact GlobalTheory.TypeFrameCover.typeFrame_cover | (intros; apply GlobalTheory.TypeFrameCover.typeFrame_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoordsStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentRadical_point_with_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  first | exact @GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd | exact GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd | (intros; apply GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDetPowCharacterSeparatesWeights
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem GlobalTheory.MinorFrame.exists_unitary_detChar_ne : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  intro ι _ a ha n n₀ hne
  classical
  obtain ⟨τ₀, hτ⟩ := Function.ne_iff.mp hne
  have hN : n τ₀ + n₀ τ₀ + 1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1) :=
    Complex.isPrimitiveRoot_exp _ hN
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := hz.norm'_eq_one hN
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]; simp
  let d : Fin a → ℂ := Function.update 1 ⟨0, ha⟩ z
  have hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [d, Function.update_apply, Pi.star_apply]
    split_ifs
    · exact hzz
    · simp
  let g : ι → Matrix.unitaryGroup (Fin a) ℂ := fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1
  refine ⟨g, ?_⟩
  have key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀ := by
    intro m
    unfold GlobalTheory.MinorFrame.detChar
    rw [Finset.prod_eq_single τ₀]
    · simp only [g, if_pos rfl, Matrix.det_diagonal, d]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [key, key]
  intro h
  exact hτ (hz.pow_inj (by omega) (by omega) h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNormStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (x : AE F E),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  first | exact @GlobalTheory.NormAtPlace.evFin_norm_eq | exact GlobalTheory.NormAtPlace.evFin_norm_eq | (intros; apply GlobalTheory.NormAtPlace.evFin_norm_eq <;> assumption)
end

