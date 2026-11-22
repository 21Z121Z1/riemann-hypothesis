import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchFlip
import Development.AutomorphicArithmetic.DivisorFrames.ConjSizeHeckeCharLocalOfMemRangeEmbedding
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLevi
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

namespace GlobalTheory.CentralLevi

theorem exists_unit_smul_of_central : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ f g hg hc
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ f

  let Dα : GL (Fin (r + 1)) (AF F ⊗[F] E) → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun α =>
    ⟨cT (sigR (AF F) σ) (α⁻¹).1, cT (sigR (AF F) σ) α.1,
      by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one],
      by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]⟩
  have hmem : ∀ α, lv α ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := fun α => by
    refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨⟨α, trivial, hlv.onC α⟩, ⟨Dα α, trivial, hlv.onD α⟩⟩
  obtain ⟨B, -, hB⟩ := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg (Fin.last r)) (Finset.mem_singleton_self _)).1
  change GL (Fin (r + 1)) (AF F ⊗[F] E) at B
  change (matHom _ σ J g).1 * adMat F X = adMat F X * B.1 at hB
  have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, f.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcomm : ∀ α : GL (Fin (r + 1)) (AF F ⊗[F] E), B.1 * α.1 = α.1 * B.1 := fun α => by
    have e := congrArg (fun h => (matHom _ σ J h).1 * adMat F X) (hc (lv α) (hmem α))
    simp only [map_mul, Units.val_mul] at e
    have e1 : (matHom _ σ J g).1 * (matHom _ σ J (lv α)).1 * adMat F X = adMat F X * (B.1 * α.1) := by
      rw [Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have e2 : (matHom _ σ J (lv α)).1 * (matHom _ σ J g).1 * adMat F X = adMat F X * (α.1 * B.1) := by
      rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hlv.onC, Matrix.mul_assoc]
    have := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) (e1.symm.trans (e.trans e2))
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using this
  obtain ⟨c, hcB⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := B.1) fun t =>
    (hcomm ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩).symm
  have hu : IsUnit c := by
    have h1 := congrFun (congrFun (Units.mul_inv B) 0) 0
    rw [← hcB, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h1
    exact ⟨⟨c, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, ?_⟩
  rw [hB, ← hcB, IsUnit.unit_spec]
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

end GlobalTheory.CentralLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizer
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.ResidueEisenstein

theorem finCovol_leviOne_last : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW π DM hπ hDM
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame F E σ n J r X Y hcm hJ hW
  letI : MeasurableSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set A := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hA
  set G₁ := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker
  set ΓA := (ratPts σ J).subgroupOf A
  set ΓG := (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range.subgroupOf G₁
  obtain ⟨hlc, hsc, hdisc, hfinGL⟩ := GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume F E σ hcm (r + 1)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv F E σ n J r m X Y Z J₀ hF
  have hclA : IsClosed (A : Set (GAd σ J)) :=
    (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const).inter
      (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const)
  haveI : LocallyCompactSpace A := hclA.locallyCompactSpace
  haveI : LocallyCompactSpace (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) :=
    (GlobalTheory.StdPar.isClosed_levi _ hcm hJ hW).2.locallyCompactSpace
  haveI := hlc
  haveI := hsc
  haveI := hdisc
  haveI : DiscreteTopology ΓA := DiscreteTopology.of_continuous_injective
    (f := fun x : ΓA => (⟨(x.1 : GAd σ J), x.2⟩ : ratPts σ J))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : ratPts σ J => (y : GAd σ J)) h)
  haveI : Countable (ΓA.prod ΓG) := by
    haveI : Countable ΓA := inferInstance
    haveI : Countable ΓG := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact Function.Injective.countable (f := fun x : ΓA.prod ΓG => ((⟨x.1.1, x.2.1⟩ : ΓA), (⟨x.1.2, x.2.2⟩ : ΓG)))
      (fun a b h => Subtype.ext (Prod.ext (congrArg (fun q => (q.1 : A)) h) (congrArg (fun q => (q.2 : G₁)) h)))
  refine GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv (A × G₁) _ φ (ΓA.prod ΓG) _ (fun g => ?_)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty A G₁ ΓA ΓG
      (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J (r + 1) m X Y Z J₀ hF μ 𝓕 hμ h𝓕) (fun μ hμ 𝓕 h𝓕 => hfinGL μ 𝓕 hμ h𝓕)
      μ hμ 𝓕 h𝓕) π DM hπ hDM
  rw [Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hφ g]

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTopOfDictionaryDepth
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.TopInt

theorem finTopK_of (hPL : ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.NormSum.Inp D →
      DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
            GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
          (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v)) (hSL : ∀ C1 : ℝ, 0 < C1 → ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.NormSum.Inp D →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
        Loss (GlobalTheory.SumSize.TopInt.topDl ch.G δ C1 large₂.sc.b) (bOne ch.G C large₂.sc.b)) :
    GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK := by
  intro hP hI hD hE
  obtain ⟨C1, hC1, hPL⟩ := hPL
  obtain ⟨CF1, hS⟩ := hSL C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  obtain ⟨CF3, hE⟩ := hE
  refine ⟨max CF1 (max CF2 CF3), fun CF hCF => ?_⟩
  obtain ⟨C01, hS⟩ := hS CF (le_of_max_le_left hCF)
  obtain ⟨C02, hD⟩ := hD CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨C03, hE⟩ := hE CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max C01 (max C02 C03), fun ε C hC => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε C (le_of_max_le_left hC)
  obtain ⟨x2, hD⟩ := hD ε C (le_trans (le_max_left _ _) (le_of_max_le_right hC))
  obtain ⟨x3, hE⟩ := hE ε C (le_trans (le_max_right _ _) (le_of_max_le_right hC))
  refine ⟨max x1 (max x2 x3), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch :=
    hD D large₂ he (le_trans (le_max_left _ _) (le_of_max_le_right hx)) Γ Pl0 T A Ks R F hs ch hch hsc hfo
  have dep : DepthAt ch :=
    hE D large₂ he (le_trans (le_max_right _ _) (le_of_max_le_right hx)) Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have loss := hS D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hch hsc hfo (hI D) S δ hL
  refine ⟨topDl ch.G δ C1 large₂.sc.b, loss, ?_⟩
  intro t w hw Φ β d hocc c j a v hv
  obtain ⟨hβ, τ, hτ, hd⟩ := hocc
  have hτ' := hτ
  obtain ⟨hk, ⟨e, -, h1, -⟩, h3⟩ := hτ'
  have hrat := (hfo.isRatAt hβ hτ hd c).1 j
  have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t (.top t j)
    (show (j : ℕ) + 1 ≤ D.R.m from j.2) _ (d.1 j) hk ((h3 d hd).1 j) ((h1 d hd).1 j).2.2 ((h1 d hd).1 j).1 _ _ hrat
    w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
  refine inLat_mono key ?_
  have hdep := (dep t Φ β hβ).2 w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw
  have := le_topDl ch.G hL.2.1 hC1.le large₂.sc.b w j.2 hdep
  linarith

theorem finTopK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK :=
  finTopK_of GlobalTheory.T.norm_sum_choice_bound GlobalTheory.T.sum_equalSign_kernel_losses_bounded

end GlobalTheory.SumSize.TopInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMemberLieActionFockPlusTrace
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MeasureTheory MvPolynomial Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.RealLift GlobalTheory.HoweD

namespace GlobalTheory.HoweD.LieFirstD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

def swapTD (P Q R S : ι → ℕ) :
    (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) ≃ₗ[ℂ] ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) :=
  PiTensorProduct.congr fun w => GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w)

theorem swapTD_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' f) =
      L (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (atPl w L' T) = atPl w L (swapTD P Q R S T) := by
  have e : (swapTD P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapTD P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapTD,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapTD_sumPl (L' : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ w f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' w f) =
      L w (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (sumPl L' T) = sumPl L (swapTD P Q R S T) := by
  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapTD_atPl w (L' w) (L w) (h w) T

end Tensor

theorem lieFirstD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om →
    ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om hCM hψ hfr hΦ hdd hW
  have hfr' : FramedD τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMapD ψ τ d' C A (Φ ∘ₗ (swapTD P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapTD P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapTD P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapTD_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ)
      (fun w f => GlobalTheory.RealLift.LieFirstPf.swapE_heisOp (c w) f)]
  obtain ⟨c, hA⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om hCM hψ hfr' hΦ' hW
  refine ⟨c, fun γ hγ Y hY T => ?_⟩
  have key := hA γ hγ Y hY ((swapTD P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapTD_sumPl (fun w => fockAct2 (R w) (S w) (P w) (Q w) (Y w) + (c w * (Y w).trace) • 1)
    (fun w => fockAct1 (P w) (Q w) (R w) (S w) (Y w) + (c w * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
        GlobalTheory.RealLift.LieFirstPf.swapE_apply, (GlobalTheory.FockSwap.swap_symmetry (R w) (S w) (P w) (Q w)).2.1]),
    LinearEquiv.apply_symm_apply] at key

end GlobalTheory.HoweD.LieFirstD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipBoundOfHyp
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize ValuativeRel
open Formalism.L2.Host GlobalTheory.StepData

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

private theorem psiAt_pow {W : G.Weil} {w : Pl D.host.E} (hc : HasConductor (psiAt W w) 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ^ (Ideal.absNorm w.asIdeal ^ n) = 1 := by
  have e := GivenAdm.isEquiv_val w
  set q := Ideal.absNorm w.asIdeal
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]

private theorem cong_le_givenLevel {μ₀ : T} (hL : L.Is μ₀) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (he : depthAt G w = cosExp G w) (X : ℕ × ℕ) :
    glLatCong (unifAt w ^ depthAt G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ≤ givenLevel G t w X := by
  obtain ⟨i, _ | j⟩ := X
  · rw [givenLevel, he]
  · rcases i with _ | i
    · obtain ⟨P, hP, -⟩ := GivenAdm.exists_types hL hw
      rw [GivenAdm.givenLevel_succ (hP _)]
      refine le_trans (fun g hg => mem_KOne.2 fun a b => ((GivenAdm.mem_glLatCong.1 hg).2 a b).trans_lt ?_)
        (TypeDatum.KOne_le _)
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_lt_one₀ zero_le' (isUnif_unifAt w ▸ uniformizer_lt_one) (by rw [depthAt]; omega)
    · exact fun g hg => (GivenAdm.mem_glLatCong.1 hg).1

private theorem nu_un {K : Type} [Field K] {ι τ : K →+* ℂ} (t : T) (w : Pl D.host.E)
    (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
    (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un ι τ ((G.ch.chiH i).loc w x : ℂ))
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : Un ι τ ((locGrid G t w).nu i j u : ℂ) := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact ((hmu _ _).mul (hxi _)).mul (hchi _ (by omega) (by omega) _).inv

private theorem locRank_le (t : T) (w : Pl D.host.E) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    (locGrid G t w).rank (i + 1, j + 1) ≤ 2 * bigN D := by
  change D.R.r + (j + 1) * D.R.t + (i + 1) * sLen D ≤ 2 * bigN D
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : 1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have h4 : D.R.r ≤ sLen D := Nat.le_add_right _ _
  unfold bigN
  rw [mul_add D.R.m, mul_add D.R.m]
  omega

end

open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.DIV NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize in
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw in
theorem _root_.GlobalTheory.T.flip_bound_of_published_inputs : GlobalTheory.FunPr.Hypotheses₂ → BigC fun _ ch C _ => FlipAt ch C := by
  refine fun _ => ⟨0, fun CF _ => ⟨48, fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ hF σ Φ w₀ z
  obtain ⟨w, hw⟩ := w₀
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q A.μ0, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard A.μ0
  have hg := (Good.locGrid_isGood hL ch.G ch.W A.μ0 hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B A.μ0 Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hW : w ∈ ch.G.pl.W0 := (GivenAdm.mem_locPl.1 hw).resolve_right fun h =>
    (hL.Q_ram A.μ0 w).2 (.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)
  have he : depthAt ch.G w = cosExp ch.G w := by
    obtain ⟨h1, h2⟩ := GivenAdm.under_mem_and_place_above_eq_of_mem hW
    have := depthAt_w ch.G h1
    rw [h2] at this
    rw [this.1, this.2]
  have hmu : ∀ j x, Un D.what₂.embLL σ ((R.toLevCh.C.mu0 j).loc w x : ℂ) := fun j x => by
    obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 j).inf
    exact UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ hn _ _ _ _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, Un D.what₂.embLL σ ((R.toLevCh.xiH A.μ0).loc w x : ℂ) := fun x => by
    rw [hL.xi_base]; exact Un.one
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un D.what₂.embLL σ ((ch.G.ch.chiH i).loc w x : ℂ) :=
    fun i a b x => UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ (ch.G.ch.inf i a b) _ _ _ _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ Set.range D.what₂.embLL := fun u =>
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.apow_half_mem D.what₂.embLL.fieldRange w
      (RingHom.mem_fieldRange.2 (hF.sqrt w (.inr ⟨A.μ0, hw⟩))) u)
  have hq0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hψ := fun x hx => (fun h => Un.of_pow_eq_one (τ := σ) (hF.roots A.μ0 w hw _ h) (pow_ne_zero _ hq0) h)
    (psiAt_pow (W := ch.W) h00.cond (depthAt ch.G w) x hx)
  have hν : ∀ x ∈ flipOrder D.R.m, (locGrid ch.G A.μ0 w).rank (x.1 + 1, x.2 + 1) ≤ 2 * bigN D ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ∀ u, Un D.what₂.embLL σ ((locGrid ch.G A.μ0 w).nu x.1 x.2 u : ℂ) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G A.μ0 w).alpha_div_beta i j
    exact ⟨locRank_le _ _ hi hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, nu_un _ w hmu hxi hchi hi hj⟩
  have key := sz_flips h00.unif h00.cond h00.one_le habs hψ (2 * bigN D) (flipOrder D.R.m)
    (givenStage A.μ0 w ch.S.B Φ) 1 hν (canFlip_flipOrder _).1
    (fun X => ⟨(GivenAdm.givenLevel_open hL hw X).1, (GivenAdm.givenLevel_open hL hw X).2, cong_le_givenLevel hL hw he X⟩)
    hadm.tensor (UpperTheory.localGrid_tensor_size_le_one_of_unimodular _ _ ch.S.B A.μ0 Φ w hmu hxi) z
  refine key.mono ?_
  rw [mul_one, (canFlip_flipOrder _).2.1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw, he,
    ← Real.exp_log (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) _), Real.log_pow, Real.exp_le_exp]
  have h1 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le w
  have h2 := placeSz_nonneg ch.G w
  calc _ ≤ ((6 * cosExp ch.G w * (2 * bigN D) ^ 2 * D.R.m ^ 2 : ℕ) : ℝ) *
        (2 * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = 48 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w := by rw [placeSz]; push_cast; ring
    _ ≤ _ := by gcongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIrrGLTransportAlongFieldIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_irrGL_transport_along_fieldIso : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → UpperTheory.Zero.LLC.Good x → UpperTheory.Zero.LLC.Good x' := by
  first | (exact @GlobalTheory.RecTTransport.good_of_repRel) | (exact GlobalTheory.RecTTransport.good_of_repRel) | (intros; apply GlobalTheory.RecTTransport.good_of_repRel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperatorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  first | exact @GlobalTheory.InertVacEquiv.heisInv_comp | exact GlobalTheory.InertVacEquiv.heisInv_comp | (intros; apply GlobalTheory.InertVacEquiv.heisInv_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  first | exact @GlobalTheory.InertLagUniq.exists_test | exact GlobalTheory.InertLagUniq.exists_test | (intros; apply GlobalTheory.InertLagUniq.exists_test <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMulStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_pullback_reading_eq_unitConst_pow_mul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → Even n → rdU (U₂ σ₂) g k₂ x = t ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f k x' := by
  first | exact @GlobalTheory.LevRead.reading_pull | exact GlobalTheory.LevRead.reading_pull | (intros; apply GlobalTheory.LevRead.reading_pull <;> assumption)
end

