import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0305
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
section
noncomputable section

namespace GlobalTheory.CosetApprox

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_valuation_le (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : P.valuation E x ≤ 1) :
    Formalism.L2.Col.IntAt P x := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x h
  exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

theorem apply_eq_sum {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) (w : Fin n → E) (l : Fin n) :
    g w l = ∑ k, w k * g (Pi.single k 1) l := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (g : T → (Fin n → E) →ₗ[E] (Fin n → E))
    (c : T → E) (t : T → Fin n → E) :
    ∃ d : Fin n → E, ∀ P : T, ∀ l, (P.1).valuation E (c P * g P (d - t P) l) ≤ 1 := by
  classical
  have hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧
      ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b := by
    intro P
    obtain ⟨b, hb⟩ := (Set.finite_range fun lk : Fin n × Fin n =>
      (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove
    exact ⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩
  choose B hB1 hBle using hb
  have hB0 : ∀ P, B P ≠ 0 := fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'
  have hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹ := by
    intro k
    obtain ⟨a, -, ha, -⟩ := PI.FinOrdValD.WA.weakApprox T
      (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0)
      (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1)
      (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))
    refine ⟨a, fun P => ?_⟩
    have h := ha P.1 P.2
    simp only [dif_pos P.2, Subtype.coe_eta] at h
    rw [← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h
  choose a ha using hk
  refine ⟨a, fun P l => ?_⟩
  rw [apply_eq_sum, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring,
    map_mul, Pi.sub_apply]
  calc (P.1).valuation E (a k - t P k) * (P.1).valuation E (c P * g P (Pi.single k 1) l)
      ≤ (B P)⁻¹ * B P := mul_le_mul' (ha k P).le (hBle P l k)
    _ = 1 := inv_mul_cancel₀ (hB0 P)

end Gen

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.MainNotions _root_.Formalism.L2.DIV _root_.Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem exists_sameCoset {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  classical
  obtain ⟨d, hd⟩ := exists_approx (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n))
    (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))
  refine ⟨d, fun P l => intAt_of_valuation_le _ _ ?_⟩
  have h := hd P l
  have e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [e]
  exact h

end GlobalTheory.CosetApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceNotBadBelowStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_not_bad_below : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := by
  first | exact @GlobalTheory.GoodOffBad.good_not_mem_badPl | exact GlobalTheory.GoodOffBad.good_not_mem_badPl | (intros; apply GlobalTheory.GoodOffBad.good_not_mem_badPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceOutsideBadSetsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_outside_bad_sets : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i := by
  first | exact @GlobalTheory.OffSQ.good_off_SQ | exact GlobalTheory.OffSQ.good_off_SQ | (intros; apply GlobalTheory.OffSQ.good_off_SQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceSplitConditionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_split_condition : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ c : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} → c = (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) := by
  first | exact @GlobalTheory.ValInert.val_inert | exact GlobalTheory.ValInert.val_inert | (intros; apply GlobalTheory.ValInert.val_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixedVectorMemLocalModelImageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_fixedVector_mem_localModelImage : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (c : k), c ≠ 0 → ∀ g, Formalism.IndefR.Datum.IsThetaFunO ψ S T g → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → Formalism.IndefR.Datum.heisO ψ S T (p.up FS FT (c • x)) g = g) → (∀ y : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → ψ (Formalism.IndefR.Datum.symplO S T (p.up FS FT (c • x)) y) = 1) → Formalism.IndefR.Datum.heisO ψ S T y g = g) → ∀ r : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf p.e r → Formalism.IndefR.Datum.heisO ψ S T r g ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  first | exact @GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed | exact GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed | (intros; apply GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtAdeleMulOfPlaceComponentEqZero
section
open NumberField IsDedekindDomain

namespace GlobalTheory.VanishAtOver

theorem intAtA_mul_of_prV_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q →
    ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 →
    ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  intro F E _ _ _ _ _ v Q hv a ha c
  apply GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero
  intro w hw
  have hwv : w = v := HeightOneSpectrum.ext (hw.trans hv.symm)
  subst hwv
  rw [map_mul, ha, mul_zero]

end GlobalTheory.VanishAtOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompactStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_type_space_maximal_compact : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  first | exact @GlobalTheory.SplitSatLoc.exists_locComp_hasSatake | exact GlobalTheory.SplitSatLoc.exists_locComp_hasSatake | (intros; apply GlobalTheory.SplitSatLoc.exists_locComp_hasSatake <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed | exact GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed | (intros; apply GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepLoc

theorem exists_sep {K F V : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ W : Submodule ℂ V, (∀ k, ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop) (hP : ∀ T, P T → ∀ k v, T (ρ k v) = r k (T v))
    (f : F) (hf : f ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T) (hf0 : f ≠ 0) :
    ∃ φ : F →ₗ[ℂ] V, φ f ≠ 0 ∧ ∀ k, ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T,
      φ (r k f') = ρ k (φ f') := by
  first
  | exact @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | (apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional ..)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL f hf hf0
  have hle := GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hcL
  have hirr : ∀ W : Submodule ℂ σ.V, (∀ k : {x : GAf L n // TrivOutside {s.v} x}, ∀ v ∈ W,
      σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let R : Subrepresentation σ.ρ := ⟨W, fun g v hv => by
      obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
      have hg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = g := by
        rw [hxe]; ext i j; simp
      have := hW ⟨x, hx⟩ v hv
      rwa [hg] at this⟩
    haveI := σ.irr
    rcases eq_bot_or_eq_top R with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  obtain ⟨φ, hφf, hφ⟩ := exists_sep (K := {x : GAf L n // TrivOutside {s.v} x}) (fun k => NG.rt L n k.1)
    (fun k => σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1))) hirr
    (fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) => (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v,
      T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v))
    (fun T hT k v => hT.2 k.1 k.2 v) f (hle hf) hf0
  exact ⟨φ, hφf, fun x hx f' hf' => hφ ⟨x, hx⟩ f' (hle hf')⟩

end GlobalTheory.SepLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTopG

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem hom_mem_stdAt {n m : ℕ} (f : HomE E n m) (hf : ∀ j l, IntAt P (f (Pi.single j 1) l)) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : f v ∈ stdAt E m P :=
  mem_stdAt.2 fun l => by
    have h := intAt_form_of_mem_stdAt (1 : E) (LinearMap.proj l ∘ₗ f) (fun i => by simpa using hf i l) hv
    simpa using h

theorem symm_mem_stdAt {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    κ.symm w ∈ stdAt E n P :=
  (hκ (κ.symm w)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hw)

theorem symm_near {n D : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P)
    (hD : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) ∈ stdAt E n P := by
  have h := hD _ (symm_mem_stdAt hκ hw)
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) = -(((qOf P : E) ^ D)⁻¹ • (w - κ.symm w)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact Submodule.neg_mem _ h

end SlopeTestRemainingChoices

theorem topDat_frames_vGs : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie P hP κ κ' hκ hκD hκ' hκ'D y y'' hy''
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hn : TopNum D.R (t.m2 + 1) := topNum_of (m_eq t μ)
  have hX : t.X.Ok := hPin.fields.ok
  have hPr := t.pr_ok
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := qOf_ne_zero
  obtain ⟨d, hd⟩ : ∃ d, (t.cst μ).D P = d + 1 := ⟨(t.cst μ).D P - 1, by have := hc.D_pos P; omega⟩
  by_cases hI : ∀ j l, IntAt P.1 (y (Pi.single j 1) l)
  ·
    have hA : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') := by
      refine topDat_congr t.Ch t.sel (t.tup μ) (t.cst μ) hX hPr hc hn P hP _ _ _ ?_ ?_
      · have h1 : κ.symm ((qOf P.1 : t.X.E) • y'') ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ (mem_stdAt.2 hy'')
        rw [map_smul] at h1
        intro j
        simpa using mem_stdAt.1 h1 j
      · intro j
        have hkj : κ (Pi.single j 1) ∈ stdAt t.X.E _ P.1 := (hκ _).2 (single_mem_stdAt j)
        have hv : y (κ (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 := hom_mem_stdAt y hI hkj
        have hz : κ'.symm (y (κ (Pi.single j 1))) ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ' hv
        have hzI : ∀ l, IntAt P.1 ((κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l) := fun l => mem_stdAt.1 hz l
        refine ⟨iff_of_true hzI (hI j), fun _ l => ?_⟩
        set s := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ (Pi.single j 1) - Pi.single j 1) with hs
        set s' := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.symm (y (κ (Pi.single j 1))) - y (κ (Pi.single j 1))) with hs'
        have hsI : s ∈ stdAt t.X.E _ P.1 := hκD _ (single_mem_stdAt j)
        have hs'I : s' ∈ stdAt t.X.E _ P.1 := symm_near hκ' hκ'D hv
        have hys : IntAt P.1 (y s l) := mem_stdAt.1 (hom_mem_stdAt y hI hsI) l
        have e1 : y s l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (y (κ (Pi.single j 1)) l - y (Pi.single j 1) l) := by
          rw [hs, map_smul, map_sub]
          rfl
        have e2 : s' l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (κ'.symm (y (κ (Pi.single j 1))) l - y (κ (Pi.single j 1)) l) := by
          rw [hs']
          rfl
        have key : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l =
            y (Pi.single j 1) l + (qOf P.1 : t.X.E) * ((qOf P.1 : t.X.E) ^ d * (y s l + s' l)) := by
          rw [e1, e2, hd]
          show κ'.symm (y (κ (Pi.single j 1))) l = _
          field_simp
          ring
        rw [key, redP_add_q ((intAt_pow (intAt_nat _) d).mul (hys.add (mem_stdAt.1 hs'I l)))]
    have hB : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' := by
      unfold topDat
      congr 1
      have hw : (qOf P.1 : t.X.E) • y'' ∈ stdAt t.X.E _ P.1 := mem_stdAt.2 hy''
      have hsw := symm_near hκ hκD hw
      have hdiff : κ.symm y'' - y'' ∈ stdAt t.X.E _ P.1 := by
        refine mem_stdAt.2 fun i => ?_
        have hi := mem_stdAt.1 hsw i
        have e : (κ.symm y'' - y'') i = (qOf P.1 : t.X.E) ^ d *
            ((((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.symm ((qOf P.1 : t.X.E) • y'') - (qOf P.1 : t.X.E) • y'')) i) := by
          rw [map_smul, hd]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        rw [e]
        exact (intAt_pow (intAt_nat _) d).mul hi
      have h := ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (fun h => absurd hP h) (κ := 1)
        (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ y) y'' (κ.symm y'')
        (fun _ => hy'') (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
      exact h
    exact hA.trans hB
  ·
    push_neg at hI
    obtain ⟨j, l, hjl⟩ := hI
    have h0 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' = 0 := by
      by_contra h
      exact hjl (topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP y y'' h j l)
    have h1 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') = 0 := by
      by_contra h
      have hzI := topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP _ _ h
      apply hjl
      have hm : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 :=
        hom_mem_stdAt _ hzI (symm_mem_stdAt hκ (single_mem_stdAt j))
      have e : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) = κ'.symm (y (Pi.single j 1)) := by
        simp
      rw [e] at hm
      have hm' := (hκ' _).2 hm
      rw [LinearEquiv.apply_symm_apply] at hm'
      exact mem_stdAt.1 hm' l
    rw [h0, h1]

end GlobalTheory.TwV.AwayTopG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameRat

theorem nearAt_liftFr_smul : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST SG) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG X.E n SG)) • d).1.liftFr w)) := by
  intro D X s n ST SG d w g hq y hy
  have hf := GlobalTheory.TopStep.liftFr_spec d.2 w
  have hf' : GlobalTheory.TopStep.IsLiftFr (d.1.act g.1 1) w (((g, (1 : GLG X.E n SG)) • d).1.liftFr w) := by
    have := GlobalTheory.TopStep.liftFr_spec ((g, (1 : GLG X.E n SG)) • d).2 w
    rwa [DecoSet.smul_val] at this
  set κ := GlobalTheory.TopStep.passFr g.1 1 hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL n w.1 κ = 1 := GlobalTheory.TopStep.redGL_passFr g.1 1 hf hf'
  have hred' : GlobalTheory.TopStep.redGL n w.1 κ⁻¹ = 1 := by rw [map_inv, hred, inv_one]
  have he : ((g, (1 : GLG X.E n SG)) • d).1.liftFr w = g.1 * d.1.liftFr w * (κ⁻¹).1 := by
    rw [InvMemClass.coe_inv, hκ]
    show _ = g.1 * d.1.liftFr w * ((((g, (1 : GLG X.E n SG)) • d).1.liftFr w)⁻¹ * g.1 * d.1.liftFr w)⁻¹
    group
  rw [he, map_mul, map_mul, mul_assoc, nearAt_rat_mul]
  exact GlobalTheory.CplPt.nearAt_mul 1 hy (GlobalTheory.CplPt.congAt_one_of_redGL s hq κ⁻¹ hred')

end GlobalTheory.FrameRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwU

set_option maxHeartbeats 1000000 in

theorem funMoved_ratA_act : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG X.E (D.R.N i) SG), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  intro D X s i hi T bad lev ST SG P v h ι x d g hh H w hw z hz
  have hw' : g.symm w ∈ d.N := (Formalism.L2.Col.mem_gmap g d.N w).1 hw
  have key : pullV (F := D.host.F) (ratA D.host.F (seamGL s g) * x) (fun a => s.iE (w a)) =
      pullV (F := D.host.F) x (fun a => s.iE (g.symm w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have e1 : (seamGL s g)⁻¹ = seamGL s g.symm := (map_inv (seamGL s) g).symm
    rw [← map_inv, e1]
    have := Formalism.MainNotions.G.KAat.bc_mulVec (F := D.host.F) (seamGL s g.symm) (fun a => s.iE (w a))
    rw [seamGL_mulVec] at this
    exact this
  show d.f P (g.symm w) = _
  exact H (g.symm w) hw' z (by rw [hz, key])

end GlobalTheory.TwU
end

