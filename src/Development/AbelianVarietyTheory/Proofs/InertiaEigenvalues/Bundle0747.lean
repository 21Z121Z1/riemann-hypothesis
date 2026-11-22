import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.DualSep

variable {D : D7}

theorem algebraMap_OI {v : FinPl D} (o : OI v) : algebraMap (OI v) (Fv D.host.F v) o = (o : Fv D.host.F v) := rfl

theorem mem_pow_iff {v : FinPl D} (ϖ : OI v) (hϖ : (ϖ : Fv D.host.F v) ≠ 0) (N : ℕ) (x : Fv D.host.F v) :
    (∃ o : OI v, x = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)) ↔
      Valued.v x ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
  constructor
  · rintro ⟨o, rfl⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    have ho : Valued.v (o : Fv D.host.F v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 o.2
    calc Valued.v (ϖ : Fv D.host.F v) ^ N * Valued.v (o : Fv D.host.F v)
        ≤ Valued.v (ϖ : Fv D.host.F v) ^ N * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ
    have hv : 0 < Valued.v ((ϖ : Fv D.host.F v) ^ N) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hp
    have hmem : x / (ϖ : Fv D.host.F v) ^ N ∈ v.adicCompletionIntegers D.host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hv, map_pow]
      exact h
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow]
    show x = (ϖ : Fv D.host.F v) ^ N * (x / (ϖ : Fv D.host.F v) ^ N)
    rw [mul_div_cancel₀ _ hp]

theorem adjCo_smul {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (s : AE D) (z : WO S T) :
    adjCo φ S T BS BT (cA D s • z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • adjCo φ S T BS BT z := by
  have h1 : ((cA D s • z : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      s • (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) := by
    ext i j
    simp [GlobalTheory.DualPairCheck.cA_cA]
  have h2 : ∀ (M : Matrix (Fin S.rank) (Fin T.rank) (AE D)),
      (s • M).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • M.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) := by
    intro M; ext i j; simp
  unfold adjCo
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.DownLift.GenSplit.DualSep

namespace GlobalTheory.DownLift.GenSplit

open DualSep in

theorem exists_sep_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ N x hx hxN
  obtain ⟨a, -, ha0, -, himg⟩ := (GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he).2
  have hα : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) ≠ 0 := by
    rw [← GlobalTheory.SplitProjChart.emb_apply]
    exact (map_ne_zero _).2 (star_ne_zero.2 ha0)
  have hϖ0 : (ϖ : Fv D.host.F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ0
  set c : Fv D.host.F v := GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) / (ϖ : Fv D.host.F v) ^ N with hcdef
  have hc : c ≠ 0 := div_ne_zero hα hp
  obtain ⟨s, hs⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.1 c
  have hcoef : ∀ z : WO S T, adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) =
      c • adjCo φ S T (frCo φ βS) (frCo φ βT) z := fun z => by rw [adjCo_smul, hs]
  have hval : ∀ m : Fv D.host.F v, Valued.v (c * m) ≤ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) ↔
      Valued.v m ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
    intro m
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = c * (ϖ : Fv D.host.F v) ^ N := by
      rw [hcdef, div_mul_cancel₀ _ hp]
    rw [e1, map_mul, map_mul, map_pow, mul_le_mul_iff_right₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc))]
  have hinPow : ∀ z : WO S T, InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) ↔
      ∀ i j, Valued.v ((c • adjCo φ S T (frCo φ βS) (frCo φ βT) z) i j) ≤
        Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) := by
    intro z
    unfold InPow
    simp only [Matrix.smul_apply, smul_eq_mul, hval, mem_pow_iff ϖ hϖ0 N]
  have hhalf : ∀ z : WO S T, IsHalf (cA D e) z → IsHalf (cA D e) (cA D s • z) := by
    intro z hz
    rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hz]
  have hcoord := (GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)).1
  have hmem : ∀ z : WO S T, IsHalf (cA D e) z → InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) →
      cA D s • z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro z hz hzN
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) ∈ adjCo φ S T (frCo φ βS) (frCo φ βT) ''
        {t | t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧
          IsHalf (cA D e) t} := by
      rw [himg, hcoef]
      exact (hinPow z).1 hzN
    obtain ⟨t, ⟨htΛ, htH⟩, hteq⟩ := h1
    have h2 : t = cA D s • z := hcoord.2.1.injOn htH (hhalf z hz) hteq
    rw [← h2]
    exact htΛ
  have hnot : cA D s • x ∉
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro hmx
    apply hxN
    rw [hinPow]
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤
          Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a))} := by
      rw [← himg]
      exact ⟨_, ⟨hmx, hhalf x hx⟩, rfl⟩
    rw [hcoef] at h1
    exact h1
  have hsd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hse := GlobalTheory.SplitScalar.isSplitIdem_conj he.1
  obtain ⟨l, hlΛ, hlH, hne⟩ := GlobalTheory.SplitScalar.exists_dual_half hse hsd
    (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1.1 u hu) (hhalf x hx) hnot
  rw [GlobalTheory.DualPairCheck.cA_cA] at hlH
  refine ⟨s • l, ?_, fun z hz => ?_, ?_⟩
  · rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hlH]
  · obtain ⟨hz1, hz2⟩ := hz
    have h1 := (hsd _ (GlobalTheory.SplitScalar.half_fin hse (hhalf z hz1))).1 (hmem z hz1 hz2) l hlΛ
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1
  · have h1 := GlobalTheory.SplitScalar.psi_skew_ne hne
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCharacterEqOneOfTrivialDegreeOneFrobeniusStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  first | exact @GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial | exact GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial | (intros; apply GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocalEqOneOfTrivialOnNormsSplitStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  first | exact @GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | exact GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | (intros; apply GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharRestrictMaxRealValEqProdAboveStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    (∀ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v,
      ν.UnrAt w ∧ w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1) →
    (GlobalTheory.PolChar.resReal ν).val v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, ν.val w := by
  first | exact @GlobalTheory.PolChar.resReal_val_eq_prod | exact GlobalTheory.PolChar.resReal_val_eq_prod | (intros; apply GlobalTheory.PolChar.resReal_val_eq_prod <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideOfLPowerGaloisCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_outside_of_lPower_galois_char : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (l n : ℕ), l.Prime → (∀ σ, r σ ^ (l ^ n) = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  first | exact @GlobalTheory.UnramPull.unramOutside_of_corr | exact GlobalTheory.UnramPull.unramOutside_of_corr | (intros; apply GlobalTheory.UnramPull.unramOutside_of_corr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (M : ℕ), M ≠ 0 → (∀ σ, r σ ^ M = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P') → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  first | exact @GlobalTheory.UnramTame.unramOutside_of_corr_of_tame | exact GlobalTheory.UnramTame.unramOutside_of_corr_of_tame | (intros; apply GlobalTheory.UnramTame.unramOutside_of_corr_of_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeAdd

open Classical in
theorem heckeFunI_add_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  intro L _ _ _ n v w Dv U hU W _ _ h h' hh hh' c f
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]

end GlobalTheory.InertHeckeAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertKU

theorem compAt_mem_tensInt (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hz

theorem mem_range_bc_of_entries {K : Type} [Field K] (S : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg' i j⟩
  have hM : (RingHom.mapMatrix S.subtype) M = (g : Matrix (Fin n) (Fin n) K) := rfl
  have hM' : (RingHom.mapMatrix S.subtype) M' = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have h1 : M * M' = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.mul_inv g)
  have h2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.inv_mul g)
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem loc_inv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x⁻¹ = (Dv.loc x)⁻¹ := by
  unfold InertDatum.loc
  simp only [InvMemClass.coe_inv, map_inv]
  group

theorem loc_entries_mem (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (y : GAf L n) (hy : y ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc y : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j
      ∈ Formalism.UG.intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hE : ∀ l k, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (y : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) l k ∈ Formalism.UG.intL (w.adicCompletion L) :=
    fun l k => (Dv.integ _).1 (compAt_mem_tensInt L v (hy l k))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hE l k)) (hP k j)

theorem loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  intro L _ _ _ n v w Dv x hx hg
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨hg, ?_⟩
  apply mem_range_bc_of_entries
  · exact loc_entries_mem L n v w Dv x hx
  · intro i j
    rw [← loc_inv]
    exact loc_entries_mem L n v w Dv x⁻¹ (inv_mem hx) i j

end GlobalTheory.InertKU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitary

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : AL L) :
    compAt L v (conjAL L a) = Formalism.UG.sigR (↑(IsCMField.complexConj L))
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v) (compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [compAt, conjAL, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m]
    (M N : Matrix m m A) : Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m] :
    Formalism.UG.cT σ (1 : Matrix m m A) = 1 := by
  unfold Formalism.UG.cT
  simp

theorem cT_conj_form {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m]
    (Pm Pi X : Matrix m m A) (h1 : Pm * Pi = 1) (hX : Formalism.UG.cT σ X * X = 1) :
    Formalism.UG.cT σ (Pi * X * Pm) * (Formalism.UG.cT σ Pm * Pm) * (Pi * X * Pm) = Formalism.UG.cT σ Pm * Pm := by
  have h2 : Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm = 1 := by
    rw [← cT_mul, h1, cT_one]
  rw [cT_mul, cT_mul]
  calc _ = Formalism.UG.cT σ Pm * (Formalism.UG.cT σ X * ((Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm) * ((Pm * Pi) * X))) * Pm := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Pm * Pm := by
        rw [h1, h2, Matrix.one_mul, Matrix.one_mul, hX, Matrix.mul_one]

theorem mem_UJ_iff {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m] (σ : A →+* A)
    (J : Matrix m m A) (g : GL m A) : g ∈ Formalism.UG.UJ σ J ↔ Formalism.UG.cT σ (g : Matrix m m A) * J * g = J := Iff.rfl

theorem loc_mem_GU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  intro L _ _ _ n v w Dv x
  let φ : AL L →+* HeightOneSpectrum.adicCompletion L w :=
    (Dv.e : _ →+* HeightOneSpectrum.adicCompletion L w).comp (compAt L v)
  have hφ : ∀ a : AL L, φ (conjAL L a) = Dv.σw (φ a) := by
    intro a
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe, compAt_conjAL, Dv.comm]
  have hx : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ReciprocityTheory.Aut.conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hconj : φ.mapMatrix (ReciprocityTheory.Aut.conjT (conjAL L)
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) =
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ReciprocityTheory.Aut.conjT, Formalism.UG.cT,
      Matrix.transpose_apply, hφ]
  have hX : φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) = 1 := by
    rw [← hconj, ← map_mul, hx, map_one]
  have hX' := mul_eq_one_comm.mp hX
  have hloc : ((Dv.loc x : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
      Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) =
      ((Dv.P⁻¹ : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) *
      φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((Dv.P : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) := by
    rw [Formalism.AUTREP.InertDatum.loc, Units.val_mul, Units.val_mul]
    congr 2
  rw [mem_UJ_iff, hloc, ← Dv.Panti]
  exact cT_conj_form Dv.σw _ _ _ (by simp) hX'

end GlobalTheory.LocalUnitary
end

