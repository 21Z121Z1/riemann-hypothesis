import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0988
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0990
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0991
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0992

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConverges
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

theorem units_coe_multiset (A : Multiset ℂˣ) :
    (do let a ← A; pure (a : ℂ) : Multiset ℂ) = A.map (fun α : ℂˣ => (α : ℂ)) := by
  show A.bind (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton A _

theorem powSum_conj (B : Multiset ℂ) (r : ℕ) :
    (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum = starRingEnd ℂ ((B.map fun β => β ^ (r + 1)).sum) := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Function.comp_def, map_pow]

theorem natCast_cpow_eq_exp (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) = Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem four_terms (A B : Multiset ℂ) (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (A.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (A.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) =
    ((‖((A + B).map (· ^ (r + 1))).sum‖ ^ 2 / ((r : ℝ) + 1) : ℝ) : ℂ) *
      Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  rw [powSum_conj A, powSum_conj B, natCast_cpow_eq_exp q hq, Multiset.map_add, Multiset.sum_add]
  set PA := (A.map fun α => α ^ (r + 1)).sum
  set PB := (B.map fun α => α ^ (r + 1)).sum
  have hn : ((‖PA + PB‖ ^ 2 : ℝ) : ℂ) = (PA + PB) * starRingEnd ℂ (PA + PB) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, hn, map_add]
  ring

theorem fourProd_eq_exp (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a)
    (σ' : CG E b) (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : UnrOutside T σ) (hT' : UnrOutside T σ') (x : ℝ) (hx : 1 < x) :
    ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧
      (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  have L := GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E
  obtain ⟨s1, p1⟩ := L a a σ σ hσ hσ T hT hT x hx
  obtain ⟨s2, p2⟩ := L b b σ' σ' hσ' hσ' T hT' hT' x hx
  obtain ⟨s3, p3⟩ := L a b σ σ' hσ hσ' T hT hT' x hx
  obtain ⟨s4, p4⟩ := L b a σ' σ hσ' hσ T hT' hT x hx
  have h := (((s1.of_norm.hasSum.add s2.of_norm.hasSum).add s3.of_norm.hasSum).add s4.of_norm.hasSum)
  refine ⟨?g, ?hs, ?hp⟩
  case hp =>
    simp only [lfac]
    rw [p1.tprod_eq, p2.tprod_eq, p3.tprod_eq, p4.tprod_eq, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
  case hs =>
    refine (congrArg (fun f => HasSum f _) (funext fun p => ?_)).mpr h
    simp only [Pi.add_apply, units_coe_multiset]
    rw [four_terms _ _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1)]
    rfl

end GlobalTheory.RSNonvan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantBilinearFormsVanishOfIoGenerationRealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  first | exact @GlobalTheory.GenByIo.forms_vanish_of_io | exact GlobalTheory.GenByIo.forms_vanish_of_io | (intros; apply GlobalTheory.GenByIo.forms_vanish_of_io <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrixStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D), e * e = e → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (EAf D), (∀ i j, toEAf D e * z i j = z i j) → ∃ y : WO S T, IsHalf (cA D e) y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapAdj S T βS βT y = z := by
  first | exact @GlobalTheory.AdjHalfLift.exists_half_frMapAdj | exact GlobalTheory.AdjHalfLift.exists_half_frMapAdj | (intros; apply GlobalTheory.AdjHalfLift.exists_half_frMapAdj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_enlarged_hecke_set : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := by
  first | exact @GlobalTheory.HeckeSbLayer.exists_sb_layer | exact GlobalTheory.HeckeSbLayer.exists_sb_layer | (intros; apply GlobalTheory.HeckeSbLayer.exists_sb_layer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtensionComplexDataEmbeddingRestrictCoeffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  first | exact @GlobalTheory.PlaceRead.exists_extends_and_emb | exact GlobalTheory.PlaceRead.exists_extends_and_emb | (intros; apply GlobalTheory.PlaceRead.exists_extends_and_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_lift_residues_idempotentSum : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ N : EAf D, ∃ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N ∧ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = Y PP := by
  first | exact @GlobalTheory.IdemResLift.exists_int_lift | exact GlobalTheory.IdemResLift.exists_int_lift | (intros; apply GlobalTheory.IdemResLift.exists_int_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralUnitOfIsUnitAwayFromLevelEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  first | exact @GlobalTheory.PlaceRead.unit_of_unitOff | exact GlobalTheory.PlaceRead.unit_of_unitOff | (intros; apply GlobalTheory.PlaceRead.unit_of_unitOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_twisted_place_coefficient_map : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  first | exact @GlobalTheory.PlaceScale.exists_scale | exact GlobalTheory.PlaceScale.exists_scale | (intros; apply GlobalTheory.PlaceScale.exists_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaSeriesRationalVectorNeZeroOfCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SeriesTie.RatNe

theorem thetaKO_sum' {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (x : GA D S) (g : GA D T)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ : ι → WO S T → ℂ) :
    thetaKO om x g (∑ k ∈ s, c k • φ k) = ∑ k ∈ s, c k * thetaKO om x g (φ k) := by
  unfold thetaKO
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

theorem ser_sum {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (g : GA D (Wc D i))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (w : ι → (R.cV i).W) :
    ser R i t f u h (∑ k ∈ s, a k • w k) g = ∑ k ∈ s, a k * ser R i t f u h (w k) g := by
  unfold ser
  rw [map_sum, map_sum]
  simp only [map_smul]
  exact thetaKO_sum' _ _ _ _ _ _

theorem exists_rat_of_ser_ne {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (g : GA D (Wc D i))
    {K' : Type} [Field K'] (σ' : K' →+* ℂ) (ψ : K' →+* D.what₂.LL) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i σ' c0' c) (w : VsV D i K')
    (hne : ser R i t f u h (c0' w) g ≠ 0) :
    ∃ (v : VsV D i D.what₂.LL) (x : VsV D i ℂ),
      (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) ∧
      ser R i t f u h (c x) g ≠ 0 := by
  classical
  have hw' : c0' w = ∑ b, σ' ((bVV K' (lamV D i)).repr w b) • c0' (bVV K' (lamV D i) b) := by
    conv_lhs => rw [← (bVV K' (lamV D i)).sum_repr w]
    rw [map_sum]
    simp only [map_smulₛₗ]
  rw [hw', ser_sum] at hne
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hb' := right_ne_zero_of_mul hb
  obtain ⟨P, hP⟩ := bVVfun_int K' (lamV D i) b
  have hvmem : MvPolynomial.map (Int.castRingHom D.what₂.LL) P ∈ VV D.what₂.LL (lamV D i) := by
    have := Formalism.L2.Col.mti_map_mem_VV ψ (lamV D i) (bVV K' (lamV D i) b).2
    rwa [bVV_coe, hP, MvPolynomial.map_map, show ψ.comp (Int.castRingHom K') = Int.castRingHom _ from
      RingHom.ext_int _ _] at this
  have hxmem : MvPolynomial.map (Int.castRingHom ℂ) P ∈ VV ℂ (lamV D i) := by
    have := Formalism.L2.Col.mti_map_mem_VV σ' (lamV D i) (bVV K' (lamV D i) b).2
    rwa [bVV_coe, hP, MvPolynomial.map_map, show σ'.comp (Int.castRingHom K') = Int.castRingHom _ from
      RingHom.ext_int _ _] at this
  refine ⟨⟨_, hvmem⟩, ⟨_, hxmem⟩, fun m => ⟨((MvPolynomial.coeff m P : ℤ) : ℚ), ?_⟩, ?_, ?_⟩
  · show MvPolynomial.coeff m (MvPolynomial.map (Int.castRingHom D.what₂.LL) P) = _
    rw [MvPolynomial.coeff_map]
    simp
  · show MvPolynomial.map (Int.castRingHom ℂ) P = MvPolynomial.map D.what₂.embLL (MvPolynomial.map (Int.castRingHom D.what₂.LL) P)
    rw [MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]
  · rwa [hc (bVV K' (lamV D i) b) ⟨_, hxmem⟩ (by
      show MvPolynomial.map (Int.castRingHom ℂ) P = MvPolynomial.map σ' ((bVV K' (lamV D i) b : VV K' (lamV D i)) : Pol K' D.what₂.Tau (Vc D i).rank)
      rw [bVV_coe, hP, MvPolynomial.map_map, RingHom.ext_int (σ'.comp (Int.castRingHom K')) (Int.castRingHom ℂ)])]

end GlobalTheory.SeriesTie.RatNe

namespace GlobalTheory.SeriesTie.RatNe

set_option maxHeartbeats 2000000 in
open GlobalTheory.OneMapAll in
theorem exists_ser_rat_ne : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → IoExt Rl.toRealDat → ∀ (j : Fin D.R.m), OMPins T Rl.toRealDat κ v₀ O j → OneMapRow0 T Rl.toRealDat κ v₀ O j → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)), (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL)) ∧ (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧ h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 := by
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl F κ v₀ O hnV hC hFW hIo j hP hrow hne c hc u hu
  have hspan := GlobalTheory.ClassSumSpanCore.classSumsSpan_core D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow
  have hA1 : cuspOver (O j) (κ j) ≠ ⊥ := GlobalTheory.T.cuspForms_baseChange_secondField_ne_bot D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow hne
  obtain ⟨g0, ⟨hg0, x, hx, hsum⟩, hg0ne⟩ : ∃ g0 ∈ {g | g ∈ cuspOver (O j) (κ j) ∧ ∃ x, (O j).Plc () x ∧ IsSum (O j) () x g},
      g0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hA1 (eq_bot_iff.2 (hspan.trans ((Submodule.span_le).2 fun g hg => ?_)))
    rw [SetLike.mem_coe, hcon g hg]
    exact Submodule.zero_mem _
  have hrow' := hrow
  obtain ⟨cc, ph, hO⟩ := hrow'
  obtain ⟨-, ⟨-, -, -, hcc, hph, z, hz, hR⟩, -⟩ := hO
  obtain ⟨ze, -, ⟨m, hm, hze⟩, hR⟩ := hR ()
  have hid := (hR x hx).2 g0 ((mem_cusp _ _ _ _ _ _).1 hg0).1 hsum
  obtain ⟨q, hq⟩ : ∃ q, jFn (Wc D j) (inC (O j).c') (rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c')))
      (O j).dict (O j).mu (actLev (O j).c' (O j).lev2 z g0) q ≠ 0 :=
    GlobalTheory.T.exists_centralTranslate_uniformisation_cuspForm_ne_zero D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow g0 hg0 hg0ne z hz
  have hth : (O j).thAd () x q ≠ 0 := by
    intro h0
    have e := hid q
    rw [h0, mul_zero] at e
    have hze0 : ze ≠ 0 := fun h => by simp [h, hm.ne'] at hze
    have hcc0 : cc ((O j).dict q.out).1 ≠ 0 := fun h => by simpa [h] using hcc ((O j).dict q.out).1
    have hl : ((lieFac (T.toCore.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (κ j)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne'
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hze0 hcc0) hl) hq) e.symm
  obtain ⟨hLL, hPins⟩ := hP
  obtain ⟨hs, J', hRep, -, hTh, hPlc⟩ := (hPins.tuple ()).reps
  obtain ⟨x₀, hpl⟩ := (hPlc x).1 hx
  have e1 := hTh _ x hpl
  rw [e1] at hth
  have hv : (fun ρ => (u ρ : (Rl.toRealDat.MW j (sg0 D A3.A)).sm ρ)) = v₀ j (sg0 D A3.A) := funext hu
  have hcls := GlobalTheory.LiftUnfoldCore.thF_eq_classSum_core D Γ Pl0 T0 A3.A T.Q.c.F Rl.toRealDat F hC j A3.A.μ0 (O j).c'.F
    (inC (O j).c') (O j).c0' ((O j).Cl' ()) hs ((O j).bad ()) J' ((O j).Lh ()) ((O j).gam ()) ((O j).vol ()) hPins.lift.std hRep
    _ x hpl u q.out
  rw [hv] at hcls
  change Rl.toRealDat.thF j A3.A.μ0 (jVx Rl.toRealDat j A3.A.μ0 x₀) (v₀ j (sg0 D A3.A)) q.out ≠ 0 at hth
  rw [hcls] at hth
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hth
  have hk' : ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u (hs k) ((O j).c0' (x k)) q.out ≠ 0 := right_ne_zero_of_mul hk
  have hsurj : Function.Surjective (O j).jL := by
    intro a
    have ha : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hLL ▸ a.2
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 ha
    refine ⟨y, Subtype.ext ?_⟩
    have := RingHom.congr_fun hPins.lift.field y
    exact this.trans hy
  let ψ : (O j).c'.F →+* D.what₂.LL := (RingEquiv.ofBijective (O j).jL ⟨(O j).jL.injective, hsurj⟩).symm.toRingHom
  obtain ⟨v, x', hv1, hv2, hv3⟩ := exists_rat_of_ser_ne Rl.toRealDat j A3.A.μ0 _ u (hs k) q.out (inC (O j).c') ψ (O j).c0' c hc
    (x k) hk'
  exact ⟨v, x', hs k, q.out, hv1, hv2, (hRep.2.2.2.2.2.2 k).1.1, hv3⟩

end GlobalTheory.SeriesTie.RatNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_place : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  first | exact @GlobalTheory.GalLoc.twistedAt_atMem | exact GlobalTheory.GalLoc.twistedAt_atMem | (intros; apply GlobalTheory.GalLoc.twistedAt_atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserFamilyHostFieldIntegersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformiser_family_hostField_integers : ∀ (D : D7), ∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2 := by
  first | exact @GlobalTheory.exists_uniformiser_family_host | exact GlobalTheory.exists_uniformiser_family_host | (intros; apply GlobalTheory.exists_uniformiser_family_host <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ParAsm

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.nV, Ranks.r] at *
  omega

theorem goodRowCuspParam_of_lift : ∀ (D : D7) (Rw : RowSide D), ParLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D →
    (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) →
    GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  intro D Rw hL h45 hEFK hCM hdef hLift hLoc j hj1 hj2 σ hiso hgood
  obtain ⟨π, μ, hπ⟩ := hLift j hj1 hj2 σ hiso
  obtain ⟨Pa, hPa⟩ := h45 hEFK hCM j hj1 hj2 (one_le_nV D) (hdef j hj1 hj2) π hπ.sph
  have hmu := GlobalTheory.T.trivial_part_in_base_change D Rw hL j σ π μ Pa hπ (hLoc σ) hPa
  exact GlobalTheory.T.exists_cusp_param_good_row D Rw hL j σ π μ Pa hπ (hLoc σ) hPa hmu hgood

end GlobalTheory.ParAsm
end

