import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem delta_ne_zero (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1

theorem area_pos (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [GlobalTheory.MomDict.area_lamOf D cc δ h.1.1]
  have h1 : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h.1.1)
  have h2 := Complex.normSq_pos.2 (delta_ne_zero h)
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem xiR_pos (D : D7) : 0 < Formalism.L2.Pj.xiR D := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [hxi]
  have h1 : (0 : ℝ) < Ideal.absNorm D.host.ccK := by linarith
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem normSq_scale (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    Complex.normSq (δ * embT D τ r) = 2 * Formalism.L2.Pj.xiR D * area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hcj : embT D τ (D.host.conj r) = starRingEnd ℂ (embT D τ r) := by
    have := D.host.isCMField_hostE
    have h : NumberField.IsCMField.complexConj D.host.E r = D.host.conj r := by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [← h, NumberField.IsCMField.complexEmbedding_complexConj]
  have h1 := congrArg (embT D τ) h
  rw [map_mul, map_mul, hcj, Complex.mul_conj, map_natCast, map_natCast] at h1
  have h2 : Complex.normSq (embT D τ r) * (Ideal.absNorm D.host.ccK : ℝ) = (Ideal.absNorm cc : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.MomDict.area_lamOf D cc δ hc, hxi, map_mul, ← h2]
  have h3 : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have h4 : Real.sqrt D.host.d ≠ 0 := by linarith
  field_simp

theorem IsScale.ne_zero (hc : cc ≠ ⊥) (h : IsScale D cc r) : r ≠ 0 := by
  rintro rfl
  have h1 : ((Ideal.absNorm cc : ℕ) : D.host.E) = 0 := by rw [← h]; simp
  exact hc (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem norm_period_sq (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    ‖period D δ r τ‖ ^ 2 = area (lamOf D cc δ) / Real.pi := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [period, norm_div, div_pow, ← Complex.normSq_eq_norm_sq, normSq_scale hc h, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  field_simp

theorem Hf_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (Z X : VC D a d) :
    Hf D (tor0 D cc δ) (fun τ i j => δ * embT D τ r * Z τ i j) (fun τ i j => δ * embT D τ r * X τ i j) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
  have hA : ((area (lamOf D cc δ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (area_pos hc).ne'
  have hL : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  rw [Hf, hL, div_eq_iff hA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : δ * embT D τ r * starRingEnd ℂ (δ * embT D τ r) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, normSq_scale hc.1.1 h]; push_cast; ring
  rw [map_mul (starRingEnd ℂ) (δ * embT D τ r)]
  linear_combination (Z τ i j * starRingEnd ℂ (X τ i j)) * h1

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_iff (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) (G : VC D S.rank T.rank → ℂ) (f : WO S T → ℂ) :
    Reads ψ θ rfl rfl cc δ r G f ↔ IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ 1 1 w *
        (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) (GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ w : WO S T, GlobalTheory.FockPos.zCo θ 1 1 w = fun τ => compAt θ τ w := fun w => by
    funext τ
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  refine and_congr_right fun _ => forall₂_congr fun w _ => ?_
  have e1 : coordY θ rfl rfl δ r w = fun τ i j => δ * embT D τ r * compAt θ τ w i j := rfl
  have e2 := Hf_scale hc h (fun τ i j => compAt θ τ w i j) (fun τ i j => compAt θ τ w i j)
  rw [e1, e2, GlobalTheory.FockPos.gaussO, hz]
  simp only [Complex.mul_conj']
  congr! 3
  push_cast
  ring

variable {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {G : VC D a d → ℂ} {f f' : WO S T → ℂ}

theorem Reads.smul (h : Reads ψ θ hS hT cc δ r G f) (c : ℂ) : Reads ψ θ hS hT cc δ r (c • G) (c • f) :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem c h.1, fun w hw => by
    rw [Pi.smul_apply, Pi.smul_apply, h.2 w hw, smul_eq_mul, smul_eq_mul]; ring⟩

theorem Reads.add {G' : VC D a d → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f') :
    Reads ψ θ hS hT cc δ r (G + G') (f + f') :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem h.1 h'.1, fun w hw => by
    rw [Pi.add_apply, Pi.add_apply, h.2 w hw, h'.2 w hw]; ring⟩

theorem Reads.unique (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G f') : f = f' :=
  sub_eq_zero.1 (GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real ((GlobalTheory.FinWeilO.thetaSub ψ S T).sub_mem h.1 h'.1)
    fun w hw => by rw [Pi.sub_apply, h.2 w hw, h'.2 w hw, sub_self])

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairIntAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ w, Away ch.G t w →
  ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t →
    (∀ l : ℕ, l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → padicValNat l k ≤ depL ch.G l) →
    ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (a : ℝ) v,
      InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + dl w) (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v)

end Claims

def PairIntK : Prop := BigC fun _ ch C b => PairIntAt ch C b

theorem BigC.mono {Q Q' : ChQ} (h : BigC Q)
    (hQ : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
      {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ),
      Q F ch C b → Q' F ch C b) : BigC Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  exact hQ F ch C _ (h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3)

theorem BigC.and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF ((le_max_left _ _).trans hCF)
  obtain ⟨C0', h'⟩ := h' CF ((le_max_right _ _).trans hCF)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  obtain ⟨x0', h'⟩ := h' ε C ((le_max_right _ _).trans hC)
  refine ⟨max x0 x0', fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ⟨?_, ?_⟩⟩
  · exact h D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3
  · exact h' D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch h1 h2 h3

end GlobalTheory.SumSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.SizesOfRows

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  intro D large₂ h
  obtain ⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have hbig2 : bigN D ≤ 2 * D.R.N D.R.m := by
    simp only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1 := by omega
    have h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ h1
    have e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6) := by ring
    omega
  have hmR : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
  have hdR : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast hd
  have hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ) := by exact_mod_cast hbig2
  have hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      have : D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)
    linarith
  have hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
  have hrd1 : 1 ≤ D.host.rdE := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by
    show Real.log (Real.exp large₂.sc.L) = large₂.sc.L
    exact Real.log_exp _
  refine ⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩
  · rw [hlogb]; linarith
  · have : (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
    linarith

end GlobalTheory.SizesOfRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem nuH_not_unrAt_above {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) ∈ G.pl.S0) : ¬ (nuH G t i j).UnrAt P := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [← div_eq_mul_inv, nuH, div_div_cancel]
  intro hn
  rcases G.pl.mem_S0_of_sum_eq.1 hP with hv | hv
  · have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      rw [hv] at h
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt P := by
      by_contra hc
      rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h hv
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
    apply (G.ch.lev0 _ hm.1 hm.2 _ hv).2
    rw [e]
    exact (hmu.mul hxi).mul hn.inv
  · apply (G.ch.lev1 _ hm.1 hm.2 P hv).2
    rw [e]
    exact (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame P) (hL.xi_tame t P)).mul (hn.levelLe 1).inv

theorem heckeL_eq_of_ram {K : Type} [Field K] [NumberField K] {χ : HChar K} {S : Set (HeightOneSpectrum (𝓞 K))}
    (hr : ∀ w ∈ S, ¬ χ.UnrAt w) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    GlobalTheory.LFun.heckeL S χ s = Λ s := by
  have e : ({w | w ∉ S} : Set (HeightOneSpectrum (𝓞 K))).mulIndicator (GlobalTheory.CMVal.eulerFactor χ s) =
      GlobalTheory.CMVal.eulerFactor χ s :=
    Set.mulIndicator_eq_self.2 fun w hw => by
      by_contra h
      exact hw (if_neg (hr w (not_not.1 h)))
  have h := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ S}) (f := GlobalTheory.CMVal.eulerFactor χ s)).2
    (by rw [e]; exact hΛ.2 s hs)
  unfold GlobalTheory.LFun.heckeL GlobalTheory.LFun.eulerProd
  simp only [GlobalTheory.LFun.locL_heckeFam]
  exact h.tprod_eq

theorem chs_nu (G : GridData L sc) (i j : Fin D.R.m) (t : T) : (chs G i j t).ν = G.nu t i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem charL_chs_eq : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G i j t s Λ hs hΛ => ?_⟩⟩
  rw [chs_nu, GlobalTheory.LFun.charL_eq_of_chrEq (chrEq_nu G t i j hL)]
  refine heckeL_eq_of_ram (fun w hw => nuH_not_unrAt_above hL G t i j w hw) hΛ ?_
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < s)

end GlobalTheory.SqStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeSz {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) : ℝ :=
  (cosExp G w : ℝ) * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)

theorem placeSz_nonneg {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) :
    0 ≤ placeSz G w :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C : ℝ)

def DatAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ (w : locPl ch.G A.μ0) x y,
  AbsLe σ ((ch.S.term A.μ0 Φ β w).datum (ch.S.colAt A.μ0 w x) (ch.S.rowAt A.μ0 w y))
    (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def FlipAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ (w : locPl ch.G A.μ0) z,
  AbsLe σ (Tflip ch.W ch.S.B A.μ0 Φ w z) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def CoefAt : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ w : locPl ch.G A.μ0,
  |((ch.S.term A.μ0 Φ β w).coef : ℝ)| ≤ Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

end Claims

section Abs

variable {D : D7}

theorem absLe_mono {σ : D.what₂.LL →+* ℂ} {z : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (hB : B ≤ B') : AbsLe σ z B' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.trans (Real.exp_le_exp.2 hB)⟩

theorem absLe_mul {σ : D.what₂.LL →+* ℂ} {z z' : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (h' : AbsLe σ z' B') :
    AbsLe σ (z * z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  refine ⟨y * y', by rw [map_mul, e, e'], ?_⟩
  rw [map_mul, norm_mul, Real.exp_add]
  exact mul_le_mul hy hy' (norm_nonneg _) (Real.exp_pos _).le

theorem absLe_prod {ι : Type} (s : Finset ι) {σ : D.what₂.LL →+* ℂ} (z : ι → ℂ) (B : ι → ℝ) (h : ∀ i ∈ s, AbsLe σ (z i) (B i)) :
    AbsLe σ (∏ i ∈ s, z i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, map_one _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact absLe_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem absLe_rat (σ : D.what₂.LL →+* ℂ) (q : ℚ) {B : ℝ} (h : |(q : ℝ)| ≤ Real.exp B) : AbsLe σ (q : ℂ) B := by
  refine ⟨(q : D.what₂.LL), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Abs

theorem sum_placeSz_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∑ w : locPl G t, placeSz G w ≤ sig G := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) (placeSz G)]
  have h1 : ∑ w ∈ locPl G t, placeSz G w = ∑ w ∈ G.pl.W0, placeSz G w := by
    refine (Finset.sum_subset (Finset.subset_union_left) fun w _ hw => ?_).symm
    simp [placeSz, (depthAt_of_notMem G hw).1]
  rw [h1, sig]
  unfold Places.W0
  refine (Finset.sum_image_le_of_nonneg fun w _ => placeSz_nonneg G w).trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
  rw [placeSz, (depthAt_w G hv).1, G.pl.under_w hv]

end GlobalTheory.ArchTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmetic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem vw_lw_arith : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  intro K _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w a b ha hb
    exact Formalism.DivisionValues.ValuationRepresentative.vw_mul w a b ha hb
  · intro w m d hd hmd
    obtain ⟨k, rfl⟩ := hmd
    have hm0 : m ≠ 0 := by rintro rfl; simp at hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hd
    have hnn : ∀ n : ℕ, 0 ≤ Formalism.DivisionValues.vw w (n : K) := by
      intro n
      have h := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w ((n : ℕ) : 𝓞 K)
      simpa using h
    refine ⟨hnn m, ?_⟩
    rw [Nat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast hm0) (by exact_mod_cast hk0)]
    linarith [hnn k]
  · intro d hd
    have hf := FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (d : K))
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    exact hw
  · intro d hd s
    exact Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s d hd.ne'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Plane Chars RealMaps IsMatched IsConst)

variable {D : D7}

def InLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (z : V.V) : Prop := V.frame.equivFun z ∈ Λ

def PlaneSplit (S S₁ : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) : Prop :=
  S.rank = S₁.rank + 2 ∧ Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι ∧ S.hD x x = 0 ∧ S.hD y y = 0 ∧ S.hD x y = 1 ∧
    (∀ u, S.hD (ι u) x = 0 ∧ S.hD (ι u) y = 0) ∧ (∀ u, InLat S₁ Λ₁ u ↔ InLat S Λ (ι u)) ∧
    ∀ z, InLat S Λ z → ∃ (s r : D.host.E) (u : S₁.V), InLat S Λ (s • x) ∧ InLat S Λ (r • y) ∧ InLat S₁ Λ₁ u ∧
      z = s • x + ι u + r • y

def IsStepB {T : Type} {A A' WW B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T A B' WW₁) : Prop :=
  Y.rA = X.rA ∧ (∃ ι x y, PlaneSplit A' B' X.rA'.Λ Y.rA'.Λ ι x y) ∧ ∃ ι x y, PlaneSplit WW WW₁ X.rW.Λ Y.rW.Λ ι x y

def HasConstR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (Γ : Geo σ a a') (R : RealMaps F a a') (χ : Chars F E) (κ : ℂ) : Prop :=
  ∃ om om' Rf, IsMatched B Γ χ om om' R Rf ∧ IsConst B Γ χ om om' R Rf κ

end GlobalTheory.SqStepK
end
end

