import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

variable {D : D7}

def toE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp
    (GlobalTheory.BotFormula.toAfE D).toRingHom

def matE {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (EAf D) :=
  ((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (toE D)

def IsIntE {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) : Prop := ∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)

def Approx (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) (z : Matrix (Fin d) (Fin a) D.host.E) : Prop :=
  ∀ i j, (z.map (inc D) - (unitBlock D o a d).map (inc D) *
    (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ hatId D 𝔪

def GoodMod (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e SS ∧ (∀ w ∈ SS, 0 < c w) ∧
    𝔪 = ∏ w ∈ SS, w.asIdeal ^ c w ∧ IsCoprime 𝔪 D.host.𝔟

def KillsCong (ν : (AE D)ˣ →* Circle) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ x y, IsFinIdl x y → IntU D y → (y : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → ν x = 1

def cosInd (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (z : Matrix (Fin d) (Fin a) D.host.E) (t : WO S T) : ℂ :=
  if IsHalf e t ∧ ∀ i j, InId 𝔪 (toEAf D (t i j) - toEAf D e * eToEAf D (z (Fin.cast hT i) (Fin.cast hS j))) then 1 else 0

def cosV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (G : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z)
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) G)

theorem cosV_smul (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (c : ℂ)
    (G : VC D a d → ℂ) : cosV δ 𝔪 z (c • G) = c • cosV δ 𝔪 z G := by
  have hU : ∀ (x : VC D a d) (F : VC D a d → ℂ),
      Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x (c • F) = c • Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x F := fun x F => by
    funext y
    simp only [Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hI : ∀ A B : AddSubgroup (VC D a d), Iop D (tor0 D ⊤ δ) A B (c • G) = c • Iop D (tor0 D ⊤ δ) A B G := fun A B => by
    funext y
    simp only [Iop, hU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [← mul_finsum, mul_left_comm]
  funext y
  simp only [cosV, Wd, hI, hU, Pi.smul_apply, smul_eq_mul]
  ring

theorem GoodMod.ne_bot {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : 𝔪 ≠ ⊥ := by
  obtain ⟨SS, c, -, -, rfl, -⟩ := h
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_approx {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) {a : ℕ} (d : ℕ) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) : ∃ z : Matrix (Fin d) (Fin a) D.host.E, IsIntE z ∧ Approx 𝔪 o k z := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hI : ∀ i j, ((unitBlock D o a d).map (inc D) *
      (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ OhE D := by
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => mul_mem ?_ (((GlobalTheory.NormSum.mem_intG k).1 hk) l j).2
    by_cases h : i.1 = o + l.1
    · simp [unitBlock, h]
    · simp [unitBlock, h]
  choose b w hw hb using fun i j => GlobalTheory.CongApprox.exists_int_approx D _ hn _ (hI i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, rfl⟩, fun i j => ?_⟩
  rw [Matrix.sub_apply, hb i j]
  have e : (Matrix.of fun i j => (b i j : D.host.E)).map (inc D) i j -
      (inc D (b i j : D.host.E) + (Ideal.absNorm 𝔪 : Formalism.MainNotions.StandardLatticesGL3.AE D) * w i j) =
      inc D (((Ideal.absNorm 𝔪 : 𝓞 D.host.E)) : D.host.E) * (-w i j) := by
    simp
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, _, neg_mem (hw i j), rfl⟩

end GlobalTheory.StdRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open Classical in

private theorem meanInf_avg_le (K M : Type) [Field K] [NumberField K] [Field M] [Algebra ℚ M] [FiniteDimensional ℚ M]
    (i : K →+* M) (h : (M →ₐ[ℚ] ℂ) → ℝ) (h0 : ∀ ρ, 0 ≤ h ρ) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun p => (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}, h ρ) /
      Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}) ≤
      2 * ((∑ ρ, h ρ) / (Module.finrank ℚ M : ℝ)) := by
  letI : Algebra K M := i.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  have hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M := by
    intro σ
    have h1 := GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)
    rw [Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole] at h1
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun ρ _ => ?_
    rw [AlgHom.ext_iff]
    rfl
  have hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ := by
    intro σ
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext ρ
    simp [RingHom.ext_iff]
  have hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤
      ∑ ρ, h ρ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]
    have hinj : Function.Injective (fun p : InfinitePlace K => p.embedding) := fun p q hpq => by
      rw [← p.mk_embedding, ← q.mk_embedding]
      exact congrArg _ hpq
    rw [← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding)
      (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ)
      (fun p _ q _ hpq => hinj hpq)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hk : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  simp only [hcard, hsum]
  rw [← Finset.sum_div, ← ht]
  generalize (∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *
  calc _ = 2 * (S / (Module.finrank ℚ K * Module.finrank K M : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le : ∃ C1 : ℝ, 0 < C1 ∧ ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hArea D δ t0)) ≤ C1 * L ∧ Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hTh D δ t0)) ≤ C1 * L := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hI δ t0 hc ht L hL hrL hdL
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have h2 : g2 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h3 : g3 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h4 : wpF (lat D δ) t0 ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  haveI : FiniteDimensional ℚ (fld D δ t0) := by
    let b := Module.finBasis ℚ D.what₂.LL
    obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
      (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
      ((Set.finite_range _).union (Set.toFinite _)) (by
        rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
        · exact mem_algebraicClosure_iff.2
            ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
        · exact hdata.2.1
        · exact hdata.2.2
        · exact hwp)
    have hle : fld D δ t0 ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro y (⟨y, rfl⟩ | hy)
      · rw [← b.sum_repr y, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
      · exact hM _ (Or.inr hy)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ) := fun ρ => by
    have h := (hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3
    unfold tc
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨hu, hv⟩ := hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt
  let i : D.what₂.LL →+* fld D δ t0 := D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)
  refine ⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_,
    (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu zero_le_two
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv zero_le_two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  first | exact @GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK | exact GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK | (intros; apply GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwistedStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detCharInvariant_same_value_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  first | exact @GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | exact GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | (intros; apply GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detOne_mul_blockUnitary_decomposition : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e), 0 < d → ∀ x : UB J, ∃ (s : UB J) (g : GA D A × GA D B), (mat s).det = 1 ∧ x = s * blkU A B e h g := by
  first | exact @GlobalTheory.DetDecomp.exists_detOne_mul_blkU | exact GlobalTheory.DetDecomp.exists_detOne_mul_blkU | (intros; apply GlobalTheory.DetDecomp.exists_detOne_mul_blkU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroup
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinEmbStd

variable {D : D7}

theorem eq_of_finHom (V : HSp D) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g' : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    g = g' := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [MonoidHom.mem_ker.1 hg, MonoidHom.mem_ker.1 hg']
  · exact Units.ext (Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective (h i j))

theorem toFinE_inc (e : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd ℚ D.host.E (1 ⊗ₜ[ℚ] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem finAdEquiv_inclR (e : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (inclR (F := D.host.F) (Af D.host.F) e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E (1 ⊗ₜ[D.host.F] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem toFinE_toAfE_symm (y : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
  simp [GlobalTheory.BotFormula.toAfE]

theorem finAdEquiv_finHom_rat (V : HSp D) (γ : GA D V) (u : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u = matHom V γ) (i j : Fin V.rank) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      algebraMap D.host.E _ ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  have : ((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j =
      inclR (F := D.host.F) (Af D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (((matHom V γ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) = _
    rw [← hγ]
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (F := D.host.F) (AF D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
    simp [inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rw [this, finAdEquiv_inclR]

theorem exists_std_of_GfC (V : HSp D) (hG : V.gram = 1) (g : GA D V) (hg : g ∈ GfC V) :
    ∃ x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, IsFinPt V g x := by
  let M : Matrix (Fin V.rank) (Fin V.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := (finHom V g).val
  have hM : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) M * M = 1 := by
    have h2 := GlobalTheory.UnitarySplit.finHom_mem V g
    change Formalism.UG.cT _ M * JR (Af D.host.F) V.gram * M = JR (Af D.host.F) V.gram at h2
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hu : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom = 1 := by
    refine GlobalTheory.DefU.ClassFin.unitary_map _ (sigR (Af D.host.F) D.sp.cm.sig) _ ?_ _ hM
    intro y
    apply (GlobalTheory.BotFormula.toAfE D).injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, GlobalTheory.BotFormula.toAfE_sgA]
  let x0 : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D) := Formalism.UG.bc (GlobalTheory.BotFormula.toAfE D).symm.toRingHom (finHom V g)
  have hx0 : x0 ∈ Formalism.MainNotions.StandardLatticesGL3.GA D V.rank := by
    change Formalism.UG.cT _ (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _ * (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact hu
  refine ⟨⟨x0, hx0⟩, hg, rfl, fun i j => ?_⟩
  exact (toFinE_toAfE_symm _).symm

theorem exists_GQ_of_rat (V : HSp D) (hG : V.gram = 1) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (hxr : x ∈ ratG D V.rank)
    (g : GA D V) (hg : ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V g := by
  rw [GlobalTheory.NormSum.ratG_eq_ratPts] at hxr
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxr)
  let U : Matrix (Fin V.rank) (Fin V.rank) D.host.E := u.val
  have huV : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram * U = V.gram := by
    have h : Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U * 1 * U = 1 := hu
    have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U = Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U := by
      exact Matrix.ext fun i j => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
    rw [hG, hc]; exact h
  have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U).map (inclR (F := D.host.F) (AF D.host.F)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * U.map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [hcT, JR, ← Matrix.map_mul, ← Matrix.map_mul, huV]
  let γ : GA D V := ⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u, hmem⟩
  refine ⟨γ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨u, huV, rfl⟩), ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [finAdEquiv_finHom_rat V γ u rfl i j, hg i j, ← toFinE_inc]
  congr 1
  rw [← hu']
  rfl

theorem exists_finEmb : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
    (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
      ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  intro D V n hG hr
  subst hr
  have key : ∀ (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank), IsFinPt V g x ↔ g ∈ GfC V ∧ ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) := by
    intro g x
    constructor
    · rintro ⟨h1, e, h2⟩
      exact ⟨h1, fun i j => by simpa using h2 i j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, rfl, fun i j => by simpa using h2 i j⟩
  choose f hf using fun x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG x rfl
  have uniq : ∀ g x, IsFinPt V g x → g = f x := by
    intro g x hg
    obtain ⟨g1, g2⟩ := (key g x).1 hg
    obtain ⟨f1, f2⟩ := (key _ x).1 (hf x)
    exact eq_of_finHom V g1 f1 fun i j => (g2 i j).trans (f2 i j).symm
  have hfx : ∀ x, ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (((finHom V (f x) : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) :=
    fun x => ((key _ x).1 (hf x)).2
  let ι : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GA D V :=
    { toFun := f
      map_one' := (uniq 1 1 ((key 1 1).2 ⟨one_mem _, fun i j => by
          simp [Matrix.one_apply, apply_ite]; split_ifs <;> simp_all⟩)).symm
      map_mul' := fun x y => (uniq _ _ ((key _ _).2 ⟨mul_mem ((key _ x).1 (hf x)).1 ((key _ y).1 (hf y)).1, fun i j => by
          simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, hfx]⟩)).symm }
  refine ⟨ι, hf, ?_, ?_, ?_⟩
  · intro x y hxy
    change f x = f y at hxy
    apply Subtype.ext; apply Units.ext; ext i j
    apply (GlobalTheory.BotFormula.toFinE D).injective
    rw [← hfx x, ← hfx y, hxy]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ((key _ x).1 (hf x)).1
    · intro g hg
      obtain ⟨x, hx⟩ := exists_std_of_GfC V hG g hg
      exact ⟨x, (uniq g x hx).symm⟩
  · intro x
    constructor
    · rintro ⟨γ, hγ, he⟩
      change finHom V γ = finHom V (f x) at he
      obtain ⟨u, -, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
      rw [GlobalTheory.NormSum.mem_ratG]
      refine ⟨(u : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ?_⟩
      refine Matrix.ext fun i j => ?_
      apply (GlobalTheory.BotFormula.toFinE D).injective
      rw [Matrix.map_apply, toFinE_inc, ← hfx x, ← he, finAdEquiv_finHom_rat V γ u hu' i j]
    · intro hxr
      exact exists_GQ_of_rat V hG x hxr (f x) (hfx x)

end GlobalTheory.FinEmbStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  first | exact @GlobalTheory.DefTransfer.LatMove.exists_finite_point | exact GlobalTheory.DefTransfer.LatMove.exists_finite_point | (intros; apply GlobalTheory.DefTransfer.LatMove.exists_finite_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSquaringPathWithTangentVectorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalSquaringPath_with_tangentVector : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R] [Algebra ℚ R], Smooth G.hom → QuasiSeparated G.hom → ∀ (b : Sp R ⟶ S) (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∃ ξ, IsPath G 2 b ξ ∧ HasTan G b ξ τ w := by
  first | exact @GlobalTheory.Nef.exists_path_tan | exact GlobalTheory.Nef.exists_path_tan | (intros; apply GlobalTheory.Nef.exists_path_tan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLMulIsPrimitiveFrameDiagonalLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_mul_isPrimitiveFrame_diagonalLattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : ℕ) (C : Type) [Fintype C] [DecidableEq C] (d : C → kˣ) (X : Matrix (Fin a) C k), X.rank = a →
    ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  first | exact @GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame | exact GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame | (intros; apply GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMapStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  first | exact @GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | exact GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | (intros; apply GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap <;> assumption)
end

